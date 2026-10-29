"""Odds & Lines page: FanDuel (The Odds API) + ESPN scoreboard odds + Kalshi.

ESPN and Kalshi need no key. FanDuel lines come from fanduel_odds.py.
"""
import json
from datetime import datetime
from typing import Dict, Optional, Tuple

import pandas as pd
import plotly.express as px
import requests
import streamlit as st

from fanduel_odds import (MARKET_LABELS, ODDS_SPORT_MAP, _api_key, _fmt_price,
                          american_to_prob, events_to_df, fetch_fanduel_odds,
                          load_history, save_snapshot)

ESPN_SCOREBOARD = "https://site.api.espn.com/apis/site/v2/sports/{ep_key}/scoreboard"
KALSHI_MARKETS = "https://api.elections.kalshi.com/trade-api/v2/markets"

# ESPN ep_key → Kalshi game-winner series
KALSHI_SERIES: Dict[str, str] = {
    'football/nfl':                        'KXNFLGAME',
    'football/college-football':           'KXNCAAFGAME',
    'basketball/nba':                      'KXNBAGAME',
    'basketball/wnba':                     'KXWNBAGAME',
    'basketball/mens-college-basketball':  'KXNCAAMBGAME',
    'baseball/mlb':                        'KXMLBGAME',
    'hockey/nhl':                          'KXNHLGAME',
}


def _num(v) -> Optional[float]:
    try:
        return float(str(v).replace('+', ''))
    except (TypeError, ValueError):
        return None


@st.cache_data(ttl=300, show_spinner="Fetching ESPN lines…")
def fetch_espn_lines(ep_key: str) -> Tuple[pd.DataFrame, str]:
    """One row per game from the ESPN scoreboard, with its embedded odds."""
    try:
        resp = requests.get(ESPN_SCOREBOARD.format(ep_key=ep_key), timeout=15)
        resp.raise_for_status()
        events = resp.json().get('events', [])
    except Exception as e:
        return pd.DataFrame(), str(e)
    rows = []
    for ev in events:
        comp = (ev.get('competitions') or [{}])[0]
        teams = {c.get('homeAway'): c.get('team', {}) for c in comp.get('competitors', [])}
        home, away = teams.get('home', {}), teams.get('away', {})
        odds = (comp.get('odds') or [{}])[0]
        ml = odds.get('moneyline', {})
        ps = odds.get('pointSpread', {})

        def close(side, d, k='odds'):
            blk = d.get(side, {})
            return _num((blk.get('close') or blk.get('open') or {}).get(k))

        rows.append({
            'espn_id': ev.get('id'), 'date': ev.get('date', ''),
            'status': comp.get('status', {}).get('type', {}).get('state', ''),
            'home_team': home.get('displayName', ''), 'away_team': away.get('displayName', ''),
            'home_loc': home.get('location', ''), 'away_loc': away.get('location', ''),
            'home_abbr': home.get('abbreviation', ''), 'away_abbr': away.get('abbreviation', ''),
            'home_id': str(home.get('id', '')), 'away_id': str(away.get('id', '')),
            'home_logo': home.get('logo', ''), 'away_logo': away.get('logo', ''),
            'espn_book': (odds.get('provider') or {}).get('name', ''),
            'espn_home_ml': close('home', ml), 'espn_away_ml': close('away', ml),
            'espn_spread': close('home', ps, 'line') if ps else _num(odds.get('spread')),
            'espn_total': _num(odds.get('overUnder')),
        })
    return pd.DataFrame(rows), ''


@st.cache_data(ttl=120, show_spinner="Fetching Kalshi markets…")
def fetch_kalshi_markets(series: str) -> Tuple[pd.DataFrame, str]:
    """Open game-winner markets; `prob` is the bid/ask mid (or last trade)."""
    rows, cursor = [], ''
    try:
        for _ in range(5):
            resp = requests.get(KALSHI_MARKETS, timeout=15, params={
                'series_ticker': series, 'status': 'open', 'limit': 200, 'cursor': cursor})
            resp.raise_for_status()
            data = resp.json()
            for m in data.get('markets', []):
                bid, ask = _num(m.get('yes_bid_dollars')), _num(m.get('yes_ask_dollars'))
                last = _num(m.get('last_price_dollars'))
                prob = (bid + ask) / 2 if bid and ask else last
                rows.append({'event': m.get('event_ticker'), 'team': m.get('yes_sub_title') or '',
                             'prob': prob})
            cursor = data.get('cursor') or ''
            if not cursor:
                break
    except Exception as e:
        return pd.DataFrame(), str(e)
    return pd.DataFrame(rows), ''


def _team_matches(kalshi_name: str, full: str, loc: str, abbr: str) -> bool:
    k = kalshi_name.lower().strip()
    return bool(k) and (k in (loc.lower(), abbr.lower(), full.lower())
                        or full.lower().startswith(k + ' '))


def attach_kalshi(games: pd.DataFrame, km: pd.DataFrame) -> pd.DataFrame:
    games = games.copy()
    games['kalshi_home'] = None
    if km.empty or games.empty:
        return games
    for _, ev in km.groupby('event'):
        if len(ev) != 2:
            continue
        for gi, g in games.iterrows():
            hit_h = ev[ev['team'].map(lambda t: _team_matches(t, g.home_team, g.home_loc, g.home_abbr))]
            hit_a = ev[ev['team'].map(lambda t: _team_matches(t, g.away_team, g.away_loc, g.away_abbr))]
            if len(hit_h) == 1 and len(hit_a) == 1 and hit_h.index[0] != hit_a.index[0]:
                ph, pa = hit_h['prob'].iat[0], hit_a['prob'].iat[0]
                if ph is not None and pa is not None and ph + pa > 0:
                    games.at[gi, 'kalshi_home'] = ph / (ph + pa)  # normalise bid/ask spread
                break
    return games


def attach_fanduel(games: pd.DataFrame, fd: pd.DataFrame) -> pd.DataFrame:
    games = games.copy()
    for c in ('fd_game_id', 'fd_home_ml', 'fd_away_ml', 'fd_home_nv', 'fd_spread', 'fd_total'):
        games[c] = None
    if fd.empty or games.empty:
        return games
    for gid, g in fd.groupby('game_id', sort=False):
        home, away = g['home_team'].iat[0], g['away_team'].iat[0]
        idx = games.index[(games['home_team'] == home) & (games['away_team'] == away)]
        if not len(idx):
            continue

        def pick(market, outcome, col='price'):
            r = g[(g['market'] == market) & (g['outcome'] == outcome)]
            return r[col].iat[0] if not r.empty else None

        i = idx[0]
        games.at[i, 'fd_game_id'] = gid
        games.at[i, 'fd_home_ml'] = pick('h2h', home)
        games.at[i, 'fd_away_ml'] = pick('h2h', away)
        games.at[i, 'fd_home_nv'] = pick('h2h', home, 'no_vig')
        games.at[i, 'fd_spread'] = pick('spreads', home, 'point')
        games.at[i, 'fd_total'] = pick('totals', 'Over', 'point')
    return games


def _ok(v) -> bool:
    return v is not None and not pd.isna(v)


def _best(*prices) -> Optional[float]:
    """Best American price for the bettor (highest payout)."""
    ps = [p for p in prices if _ok(p)]
    return max(ps, key=lambda p: (p / 100) if p > 0 else (100 / -p)) if ps else None


def _pct(v) -> str:
    return f'{v:.1%}' if _ok(v) else '—'


def _line(v) -> str:
    return f'{v:+g}' if _ok(v) else '—'


def _plain(v) -> str:
    return f'{v:g}' if _ok(v) else '—'


def _book_home_nv(r) -> Optional[float]:
    """Sportsbook no-vig home probability: FanDuel if present, else ESPN's book."""
    if _ok(r.fd_home_nv):
        return r.fd_home_nv
    h, a = american_to_prob(r.espn_home_ml), american_to_prob(r.espn_away_ml)
    return h / (h + a) if h and a else None


def render_odds_page(db) -> None:
    st.subheader('🎯 Odds & Lines')
    st.caption('FanDuel (The Odds API) · ESPN scoreboard odds · Kalshi prediction market. '
               'Informational only — bets are placed by you on the sportsbook.')

    active = json.loads(db.get_config('active_endpoints', '[]'))
    supported = set(ODDS_SPORT_MAP) | set(KALSHI_SERIES)
    leagues = [k for k in active if k in supported] or sorted(supported)
    c1, c2 = st.columns([3, 1])
    ep_key = c1.selectbox('League', leagues, key='fd_league')
    if c2.button('🔄 Refresh lines', use_container_width=True):
        fetch_fanduel_odds.clear()
        fetch_espn_lines.clear()
        fetch_kalshi_markets.clear()

    games, err = fetch_espn_lines(ep_key)
    if err:
        st.error(f'ESPN: {err}')
    if not games.empty:
        games = games[games['status'] != 'post'].reset_index(drop=True)
    if games.empty:
        st.info('No upcoming or live games on the ESPN scoreboard for this league.')
        return

    sources = ['ESPN']
    if ep_key in KALSHI_SERIES:
        km, kerr = fetch_kalshi_markets(KALSHI_SERIES[ep_key])
        if kerr:
            st.warning(f'Kalshi: {kerr}')
        games = attach_kalshi(games, km)
        sources.append('Kalshi')
    else:
        games['kalshi_home'] = None

    key = _api_key()
    fd = pd.DataFrame()
    if key and ep_key in ODDS_SPORT_MAP:
        events, ferr, remaining = fetch_fanduel_odds(ODDS_SPORT_MAP[ep_key], key)
        if ferr:
            st.warning(f'FanDuel: {ferr}')
        fd = events_to_df(events)
        save_snapshot(db.db_name, ep_key, fd)
        sources.append(f'FanDuel ({remaining} API calls left)')
    elif not key:
        st.info('Add `ODDS_API_KEY` (free at the-odds-api.com) to `.streamlit/secrets.toml` '
                'to include FanDuel lines.')
    games = attach_fanduel(games, fd)
    st.caption('Sources: ' + ' · '.join(sources))

    book_nv = [_book_home_nv(r) for r in games.itertuples()]
    view = pd.DataFrame({
        'Start': pd.to_datetime(games['date']).dt.tz_convert(datetime.now().astimezone().tzinfo).dt.strftime('%a %m/%d %H:%M'),
        'Matchup': games['away_abbr'] + ' @ ' + games['home_abbr'],
        'FD Home ML': games['fd_home_ml'].map(_fmt_price),
        'FD Away ML': games['fd_away_ml'].map(_fmt_price),
        'FD Spread': games['fd_spread'].map(_line),
        'FD Total': games['fd_total'].map(_plain),
        'ESPN Book': games['espn_book'].replace('', '—'),
        'ESPN Home ML': games['espn_home_ml'].map(_fmt_price),
        'ESPN Away ML': games['espn_away_ml'].map(_fmt_price),
        'ESPN Spread': games['espn_spread'].map(_line),
        'ESPN Total': games['espn_total'].map(_plain),
        'Best Home ML': [_fmt_price(_best(a, b)) for a, b in zip(games['fd_home_ml'], games['espn_home_ml'])],
        'Best Away ML': [_fmt_price(_best(a, b)) for a, b in zip(games['fd_away_ml'], games['espn_away_ml'])],
        'Book Home % (no-vig)': [_pct(p) for p in book_nv],
        'Kalshi Home %': games['kalshi_home'].map(_pct),
        'Kalshi − Book': [f'{k - b:+.1%}' if _ok(k) and _ok(b) else '—'
                          for k, b in zip(games['kalshi_home'], book_nv)],
    })
    # Hide columns with no data (e.g. FanDuel when no key is set).
    view = view.loc[:, [c for c in view.columns if not (view[c] == '—').all()]]
    st.dataframe(view, hide_index=True, use_container_width=True)
    st.caption('**Kalshi − Book**: how much more (+) or less (−) likely the prediction market '
               'rates the home team than the sportsbook no-vig price. Big gaps can flag value '
               '— or a stale line.')

    fd_games = games[games['fd_game_id'].notna()]
    if fd_games.empty:
        return
    st.markdown('#### 📉 FanDuel line movement')
    labels = dict(zip(fd_games['away_abbr'] + ' @ ' + fd_games['home_abbr'], fd_games['fd_game_id']))
    sel = st.selectbox('Game', list(labels), key='fd_game')
    hist = load_history(db.db_name, labels[sel])
    if hist['fetched_at'].nunique() < 2:
        st.caption('Movement appears after lines have been fetched at least twice '
                   '(at least 4 minutes apart).')
        return
    mkt = st.radio('Market', list(MARKET_LABELS), format_func=MARKET_LABELS.get,
                   horizontal=True, key='fd_mkt')
    h = hist[hist['market'] == mkt]
    y = 'price' if mkt == 'h2h' else 'point'
    fig = px.line(h, x='fetched_at', y=y, color='outcome', markers=True,
                  labels={'fetched_at': 'Snapshot (UTC)', y: 'Odds' if y == 'price' else 'Line'})
    fig.update_layout(height=320, margin=dict(l=10, r=10, t=10, b=10))
    st.plotly_chart(fig, use_container_width=True)

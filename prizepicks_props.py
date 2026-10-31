"""PrizePicks player props via The Odds API (`us_dfs` region, `prizepicks`
bookmaker) — PrizePicks has no public API, so this is the sanctioned route.

Credit budget (free tier = 500 requests/month): the events list is free;
each game costs one credit per prop market requested. Props are fetched only
for the game the user opens, cached 15 minutes, and snapshotted to SQLite.
"""
import json
import re
import sqlite3
import unicodedata
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple

import pandas as pd
import requests
import streamlit as st

from fanduel_odds import ODDS_SPORT_MAP, _api_key

EVENTS_URL = "https://api.the-odds-api.com/v4/sports/{sport}/events"
EVENT_ODDS_URL = "https://api.the-odds-api.com/v4/sports/{sport}/events/{event}/odds"

# Prop market -> (our box-score category, stat label, friendly name). A few key
# markets per sport keeps the credit cost per game small.
MARKETS: Dict[str, Dict[str, Tuple[str, str, str]]] = {
    'football': {
        'player_pass_yds': ('passing', 'YDS', 'Pass yards'),
        'player_rush_yds': ('rushing', 'YDS', 'Rush yards'),
        'player_reception_yds': ('receiving', 'YDS', 'Receiving yards'),
        'player_receptions': ('receiving', 'REC', 'Receptions'),
    },
    'basketball': {
        'player_points': ('stats', 'PTS', 'Points'),
        'player_rebounds': ('stats', 'REB', 'Rebounds'),
        'player_assists': ('stats', 'AST', 'Assists'),
        'player_threes': ('stats', '3PT', '3-pointers'),
    },
    'hockey': {
        'player_shots_on_goal': ('forwards', 'S', 'Shots on goal'),
        'player_goals': ('forwards', 'G', 'Goals'),
        'player_assists': ('forwards', 'A', 'Assists'),
    },
    'baseball': {
        'batter_hits': ('batting', 'H', 'Hits'),
        'batter_home_runs': ('batting', 'HR', 'Home runs'),
        'pitcher_strikeouts': ('pitching', 'K', 'Strikeouts'),
    },
}


def _norm(name: str) -> str:
    """'Patrick Mahomes II' / 'D.J. Moore' -> comparable key."""
    s = unicodedata.normalize('NFKD', name).encode('ascii', 'ignore').decode().lower()
    s = re.sub(r'\b(jr|sr|ii|iii|iv)\b\.?', '', s)
    return re.sub(r'[^a-z]', '', s)


@st.cache_data(ttl=3600, show_spinner=False)
def fetch_events(sport: str, key: str) -> List[Dict]:
    """Upcoming events (free endpoint — costs no credits)."""
    try:
        r = requests.get(EVENTS_URL.format(sport=sport), params={'apiKey': key}, timeout=15)
        r.raise_for_status()
        return r.json()
    except Exception:
        return []


@st.cache_data(ttl=900, show_spinner=False)
def fetch_props(sport: str, event_id: str, markets: Tuple[str, ...], key: str) -> Tuple[List[Dict], str, str]:
    """PrizePicks props for one event. Returns (rows, error, credits_remaining)."""
    try:
        r = requests.get(EVENT_ODDS_URL.format(sport=sport, event=event_id), timeout=15, params={
            'apiKey': key, 'regions': 'us_dfs', 'bookmakers': 'prizepicks',
            'markets': ','.join(markets), 'oddsFormat': 'american'})
        remaining = r.headers.get('x-requests-remaining', '?')
        if r.status_code == 401:
            return [], 'Invalid ODDS_API_KEY.', remaining
        if r.status_code == 422:
            return [], 'PrizePicks props are not offered for this game.', remaining
        r.raise_for_status()
        data = r.json()
    except Exception as e:
        return [], str(e), '?'
    rows = []
    for bk in data.get('bookmakers', []):
        if bk.get('key') != 'prizepicks':
            continue
        for mk in bk.get('markets', []):
            for oc in mk.get('outcomes', []):
                if oc.get('name') != 'Over' or oc.get('point') is None:
                    continue  # one row per player line (Over side carries it)
                rows.append({'market': mk['key'], 'player': oc.get('description', ''),
                             'line': float(oc['point'])})
    return rows, '', remaining


def find_event(events: List[Dict], home: str, away: str) -> Optional[Dict]:
    for e in events:
        if e.get('home_team') == home and e.get('away_team') == away:
            return e
    # Fall back to a looser match on team nickname.
    h, a = home.split()[-1].lower(), away.split()[-1].lower()
    for e in events:
        if h in e.get('home_team', '').lower() and a in e.get('away_team', '').lower():
            return e
    return None


def _save_snapshot(db_name: str, event_id: str, rows: List[Dict]) -> None:
    if not rows:
        return
    con = sqlite3.connect(db_name, timeout=30)
    con.execute('''CREATE TABLE IF NOT EXISTS prop_snapshots (
        fetched_at TEXT, source TEXT, event_id TEXT, market TEXT, player TEXT, line REAL)''')
    stamp = datetime.utcnow().replace(microsecond=0).isoformat()
    last = con.execute('SELECT MAX(fetched_at) FROM prop_snapshots WHERE event_id=?',
                       (event_id,)).fetchone()[0]
    if not last or (datetime.utcnow() - datetime.fromisoformat(last)).total_seconds() > 600:
        con.executemany('INSERT INTO prop_snapshots VALUES (?,?,?,?,?,?)',
                        [(stamp, 'prizepicks', event_id, r['market'], r['player'], r['line'])
                         for r in rows])
        con.commit()
    con.close()


def _history(db: Any, ep: str, team_abbr: str) -> pd.DataFrame:
    """Per-game stat values for a team's players: player, category, stat, value, event, date."""
    raw = db.get_team_players_stats(ep, team_abbr)
    rows = []
    for r in raw.itertuples():
        try:
            labels, vals = json.loads(r.stat_labels), json.loads(r.stat_values)
        except Exception:
            continue
        for lab, v in zip(labels, vals):
            try:
                num = float(str(v).split('-')[0].split('/')[0].replace(',', ''))
            except ValueError:
                continue
            rows.append((r.player_name, (r.category or 'stats').lower(), lab, num,
                         r.event_id, r.game_date or ''))
    return pd.DataFrame(rows, columns=['player', 'category', 'stat', 'value', 'event', 'date'])


def compare(db: Any, ep: str, props: List[Dict], teams: List[Tuple[str, float]],
            projections_fn) -> pd.DataFrame:
    """Join PrizePicks lines with our projection and each player's recent hit rate.
    teams: [(team_abbr, opponent_factor)]."""
    cat_markets = MARKETS.get(ep.split('/')[0], {})
    proj_lookup: Dict[Tuple[str, str, str], Tuple[float, str]] = {}
    hist_frames = []
    for abbr, factor in teams:
        for cat, df in projections_fn(db, ep, abbr, factor, top=60).items():
            for player, row in df.iterrows():
                for stat, val in row.items():
                    if stat != 'GP':
                        proj_lookup[(_norm(player), cat, stat)] = (float(val), abbr)
        h = _history(db, ep, abbr)
        if not h.empty:
            hist_frames.append(h.assign(team=abbr))
    hist = pd.concat(hist_frames, ignore_index=True) if hist_frames else pd.DataFrame()
    if not hist.empty:
        hist['key'] = hist['player'].map(_norm)

    rows = []
    for p in props:
        cat, stat, nice = cat_markets.get(p['market'], (None, None, p['market']))
        k = _norm(p['player'])
        proj, team = proj_lookup.get((k, cat, stat), (None, ''))
        hit, n = None, 0
        if not hist.empty and cat:
            g = hist[(hist['key'] == k) & (hist['category'] == cat) & (hist['stat'] == stat)]
            g = g.drop_duplicates('event').sort_values('date', ascending=False).head(10)
            n = len(g)
            if n:
                hit = (g['value'] > p['line']).mean()
                team = team or g['team'].iat[0]
        rows.append({'Player': p['player'], 'Team': team, 'Prop': nice, 'PrizePicks': p['line'],
                     'Our projection': proj,
                     'Diff': (proj - p['line']) if proj is not None else None,
                     'Over hit rate (L10)': hit, 'Games': n})
    df = pd.DataFrame(rows)
    if df.empty:
        return df
    df['lean'] = [('More ⬆' if d > 0 else 'Less ⬇') if d is not None and abs(d) >= 0.1 * l else '—'
                  for d, l in zip(df['Diff'], df['PrizePicks'])]
    return df.sort_values('Diff', key=lambda s: s.abs(), ascending=False, na_position='last')


def render_prizepicks(db: Any, ep: str, home_team: str, away_team: str,
                      teams: List[Tuple[str, float]], projections_fn, key_suffix: str = '') -> None:
    """PrizePicks lines for one game next to our projections. Fetches nothing
    until the user asks (each game costs Odds API credits)."""
    cat = ep.split('/')[0]
    sport = ODDS_SPORT_MAP.get(ep)
    if not sport or cat not in MARKETS:
        st.caption('PrizePicks props aren\'t available for this league through The Odds API.')
        return
    key = _api_key()
    if not key:
        st.info('Add a free `ODDS_API_KEY` (the-odds-api.com) to `.streamlit/secrets.toml` to '
                'pull PrizePicks player props.')
        return
    markets = tuple(MARKETS[cat])
    load_key = f'pp_load_{ep}_{home_team}_{away_team}{key_suffix}'
    if not st.session_state.get(load_key):
        st.caption(f'Loading props uses up to {len(markets)} of your monthly Odds API credits '
                   f'for this game (cached 15 min).')
        if st.toggle('Show PrizePicks props for this game', key=f'{load_key}_t'):
            st.session_state[load_key] = True
            st.rerun()
        return

    event = find_event(fetch_events(sport, key), home_team, away_team)
    if not event:
        st.info('This game isn\'t listed on The Odds API yet.')
        return
    with st.spinner('Fetching PrizePicks lines…'):
        props, err, remaining = fetch_props(sport, event['id'], markets, key)
    if err:
        st.warning(f'PrizePicks: {err}')
        return
    if not props:
        st.info('PrizePicks hasn\'t posted props for this game yet.')
        return
    _save_snapshot(db.db_name, event['id'], props)
    df = compare(db, ep, props, teams, projections_fn)
    st.caption(f'{len(props)} PrizePicks lines · Odds API credits left this month: {remaining}')
    show = df.drop(columns=['Diff']).assign(**{
        'Our projection': df['Our projection'].map(lambda v: '—' if v is None or pd.isna(v) else f'{v:.1f}'),
        'Over hit rate (L10)': [('—' if h is None or pd.isna(h) else f'{h:.0%} ({n})')
                                for h, n in zip(df['Over hit rate (L10)'], df['Games'])],
    }).drop(columns=['Games']).rename(columns={'lean': 'Model lean'})
    st.dataframe(show, hide_index=True, use_container_width=True)
    st.caption('Lean shows where our projection is 10%+ above (More) or below (Less) the line. '
               'Projections = recent form × opponent defense; not validated by the backtest — '
               'research only, not advice.')

"""Live centre: every in-progress game across the active leagues, streamed from
ESPN (scoreboard + game summary) with Kalshi in-play prices, a live projection
of the final score, play-by-play and live box scores — plus a Best Bets board
that ranks model-vs-market edges on upcoming games.

ESPN's public feeds lag the broadcast by roughly 10–60 seconds; the page
refreshes itself every 20 seconds.
"""
import json
import math
import re
import time
from datetime import datetime
from typing import Any, Callable, Dict, List, Optional, Tuple

import pandas as pd
import plotly.graph_objects as go
import requests
import streamlit as st

from fanduel_odds import american_to_prob
from matchups import (_HFA, _SIGMA, blended_prob, build_slate, predict,
                      prob_to_american, team_form)
from odds_page import KALSHI_SERIES, attach_kalshi, fetch_kalshi_markets

SCOREBOARD = "https://site.api.espn.com/apis/site/v2/sports/{ep}/scoreboard"
SUMMARY = "https://site.api.espn.com/apis/site/v2/sports/{ep}/summary"
REFRESH_SECONDS = 20

# (regulation periods, minutes per period); baseball uses innings.
_CLOCK = {
    'football/nfl': (4, 15), 'football/college-football': (4, 15),
    'basketball/nba': (4, 12), 'basketball/wnba': (4, 10),
    'basketball/mens-college-basketball': (2, 20),
    'basketball/womens-college-basketball': (4, 10),
    'hockey/nhl': (3, 20), 'baseball/mlb': (9, None),
}

_session = requests.Session()
_session.headers.update({'User-Agent': 'Mozilla/5.0 (TrulySporting Live)'})


def _norm_cdf(x: float) -> float:
    return 0.5 * (1 + math.erf(x / math.sqrt(2)))


def _get(url: str, **params) -> Dict:
    resp = _session.get(url, params=params, timeout=12)
    resp.raise_for_status()
    return resp.json()


# ── Feeds ─────────────────────────────────────────────────────

@st.cache_data(ttl=15, show_spinner=False)
def fetch_live_games(ep: str) -> pd.DataFrame:
    """In-progress games for one league (ESPN scoreboard)."""
    try:
        events = _get(SCOREBOARD.format(ep=ep)).get('events', [])
    except Exception:
        return pd.DataFrame()
    rows = []
    for ev in events:
        comp = (ev.get('competitions') or [{}])[0]
        status = comp.get('status', {})
        if status.get('type', {}).get('state') != 'in':
            continue
        t = {c.get('homeAway'): c for c in comp.get('competitors', [])}
        h, a = t.get('home', {}), t.get('away', {})
        sit = comp.get('situation') or {}
        rows.append({
            'ep': ep, 'espn_id': ev.get('id'), 'date': ev.get('date', ''),
            'period': status.get('period', 0), 'clock': status.get('displayClock', ''),
            'detail': status.get('type', {}).get('shortDetail', ''),
            'home_team': h.get('team', {}).get('displayName', ''),
            'away_team': a.get('team', {}).get('displayName', ''),
            'home_abbr': h.get('team', {}).get('abbreviation', ''),
            'away_abbr': a.get('team', {}).get('abbreviation', ''),
            'home_loc': h.get('team', {}).get('location', ''),
            'away_loc': a.get('team', {}).get('location', ''),
            'home_id': str(h.get('team', {}).get('id', '')),
            'away_id': str(a.get('team', {}).get('id', '')),
            'home_logo': h.get('team', {}).get('logo', ''),
            'away_logo': a.get('team', {}).get('logo', ''),
            'home_score': int(float(h.get('score') or 0)),
            'away_score': int(float(a.get('score') or 0)),
            'situation': sit.get('downDistanceText') or sit.get('shortDownDistanceText') or '',
            'possession': sit.get('possession', ''),
            'last_play': (sit.get('lastPlay') or {}).get('text', ''),
        })
    return pd.DataFrame(rows)


@st.cache_data(ttl=20, show_spinner=False)
def fetch_summary(ep: str, event_id: str) -> Dict:
    try:
        return _get(SUMMARY.format(ep=ep), event=event_id)
    except Exception:
        return {}


# ── Live projection ───────────────────────────────────────────

def fraction_remaining(ep: str, period: int, clock: str) -> float:
    if ep.startswith('soccer/'):
        # Clock counts up: "60'" or "45'+2'".
        import re
        m = re.match(r"\s*(\d+)", str(clock))
        minute = int(m.group(1)) if m else (45 if period >= 2 else 0)
        return max(0.01, (90 - minute) / 90)
    regs, mins = _CLOCK.get(ep, (4, 15))
    if mins is None:  # baseball: innings
        return max(0.02, (regs - max(period, 1) + 0.5) / regs)
    try:
        parts = str(clock).split(':')
        secs = float(parts[0]) * 60 + float(parts[1]) if len(parts) == 2 else float(parts[0])
    except ValueError:
        secs = 0.0
    if period > regs:  # overtime
        return 0.02
    left = (regs - period) * mins * 60 + secs
    return max(0.0, min(1.0, left / (regs * mins * 60)))


_PREGAME: Dict[Tuple, Tuple[float, Optional[Dict]]] = {}


def pregame_prediction(db: Any, worker: Any, ep: str, season: int,
                       home_id: str, away_id: str) -> Optional[Dict]:
    """Pre-game model for a live game (cached for an hour)."""
    key = (ep, home_id, away_id)
    hit = _PREGAME.get(key)
    if hit and time.time() - hit[0] < 3600:
        return hit[1]
    cat, spt = ep.split('/')
    fh = team_form(db, worker, cat, spt, home_id, season)
    fa = team_form(db, worker, cat, spt, away_id, season)
    pred = predict(ep, fh, fa)
    _PREGAME[key] = (time.time(), pred)
    return pred


def live_projection(ep: str, pred: Optional[Dict], home: int, away: int,
                    period: int, clock: str) -> Dict:
    """Blend the current score with the pre-game expectation for the time left."""
    f = fraction_remaining(ep, period, clock)
    sigma = _SIGMA.get(ep.split('/')[0], 12.0)
    if pred:
        rest_margin = pred['margin'] * f
        rest_total = (pred['home_pts'] + pred['away_pts']) * f
    else:
        played = max(1e-3, 1 - f)
        rest_margin = _HFA.get(ep, 0.3 if ep.startswith('soccer/') else 1.0) * f
        rest_total = (home + away) / played * f
    margin = (home - away) + rest_margin
    total = home + away + rest_total
    # Uncertainty shrinks with time left, with a floor for late-game swings
    # (fouls, onside kicks, empty nets) so the model isn't overconfident.
    spread = math.sqrt(sigma ** 2 * f + (0.25 * sigma) ** 2)
    p_draw = 0.0
    if ep.startswith('soccer/'):
        # Goals are discrete: a final margin within ±0.5 is a draw.
        p_home = 1 - _norm_cdf((0.5 - margin) / spread)
        p_draw = _norm_cdf((0.5 - margin) / spread) - _norm_cdf((-0.5 - margin) / spread)
    else:
        p_home = _norm_cdf(margin / spread)
    return {'f': f, 'margin': margin, 'p_home': p_home, 'p_draw': p_draw,
            'home_final': total / 2 + margin / 2, 'away_final': total / 2 - margin / 2}


# ── Summary parsing ───────────────────────────────────────────

def recent_plays(summary: Dict, n: int = 15) -> List[Dict]:
    plays = summary.get('plays') or []
    if not plays:
        drives = summary.get('drives') or {}
        cur = drives.get('current') or {}
        prev = drives.get('previous') or []
        for d in prev[-2:] + ([cur] if cur else []):
            plays += d.get('plays', [])
    out = []
    for p in reversed(plays[-n:]):
        per = p.get('period', {})
        out.append({
            'when': f"{per.get('displayValue') or 'Q' + str(per.get('number', ''))} "
                    f"{(p.get('clock') or {}).get('displayValue', '')}".strip(),
            'text': p.get('text', ''),
            'score': f"{p.get('awayScore', '')}–{p.get('homeScore', '')}",
            'scoring': bool(p.get('scoringPlay')),
        })
    return out


def box_tables(summary: Dict) -> Dict[str, Dict[str, pd.DataFrame]]:
    """{team_abbr: {category: DataFrame}} from the live box score."""
    out: Dict[str, Dict[str, pd.DataFrame]] = {}
    for team in (summary.get('boxscore') or {}).get('players', []):
        abbr = team.get('team', {}).get('abbreviation', '?')
        cats = {}
        for stat in team.get('statistics', []):
            labels = stat.get('labels') or []
            rows = [[a.get('athlete', {}).get('displayName', '')] + a.get('stats', [])
                    for a in stat.get('athletes', []) if a.get('stats')]
            if rows and labels:
                df = pd.DataFrame(rows, columns=['Player'] + labels[:len(rows[0]) - 1])
                cats[(stat.get('name') or 'stats').title()] = df
        out[abbr] = cats
    return out


def team_stat_rows(summary: Dict) -> List[tuple]:
    """[(label, away_display, home_display, away_num, home_num)] from the live box score."""
    teams = (summary.get('boxscore') or {}).get('teams') or []
    if len(teams) != 2:
        return []
    by_side = {}
    for t in teams:
        side = t.get('homeAway') or ('home' if t is teams[1] else 'away')
        by_side[side] = {x.get('label') or x.get('name'): x.get('displayValue', '')
                         for x in t.get('statistics', [])}
    away, home = by_side.get('away', {}), by_side.get('home', {})
    rows = []
    for lbl in away:
        if lbl not in home:
            continue
        a, h = str(away[lbl]), str(home[lbl])
        def n(v):
            try:
                return float(re.split(r'[-/:]', v.replace(',', ''))[0].rstrip('%'))
            except ValueError:
                return None
        rows.append((lbl, a, h, n(a), n(h)))
    return rows


def momentum(summary: Dict, last_n: int = 20) -> Optional[tuple]:
    """(away_pts, home_pts, plays) scored over the last N plays with a score."""
    plays = summary.get('plays') or []
    if not plays:
        for d in ((summary.get('drives') or {}).get('previous') or [])[-4:]:
            plays += d.get('plays', [])
    scored = [p for p in plays if p.get('awayScore') is not None and p.get('homeScore') is not None]
    if len(scored) < 2:
        return None
    window = scored[-last_n:]
    first, last = window[0], window[-1]
    return (int(last['awayScore']) - int(first['awayScore']),
            int(last['homeScore']) - int(first['homeScore']), len(window))


def line_score(summary: Dict) -> Optional[pd.DataFrame]:
    comps = ((summary.get('header') or {}).get('competitions') or [{}])[0].get('competitors', [])
    rows = {}
    for c in comps:
        ls = [x.get('displayValue', '') for x in c.get('linescores') or []]
        if ls:
            rows[c.get('team', {}).get('abbreviation', c.get('homeAway', ''))] = ls + [c.get('score', '')]
    if len(rows) != 2:
        return None
    n = max(len(v) for v in rows.values()) - 1
    return pd.DataFrame(rows, index=[str(i + 1) for i in range(n)] + ['T']).T


def _stat_bars(rows: List[tuple], away: str, home: str) -> str:
    html = (f'<div style="display:flex;justify-content:space-between;font-size:12px;'
            f'font-weight:700;color:#475569;margin:4px 0 6px"><span>{away}</span><span>{home}</span></div>')
    for lbl, a, h, an, hn in rows:
        if an is None or hn is None or (an + hn) <= 0:
            continue
        pa = 100 * an / (an + hn)
        html += (f'<div style="margin:6px 0"><div style="display:flex;justify-content:space-between;'
                 f'font-size:12px"><b>{a}</b><span style="color:#64748b">{lbl}</span><b>{h}</b></div>'
                 f'<div style="display:flex;height:6px;border-radius:4px;overflow:hidden;background:#e2e8f0">'
                 f'<div style="width:{pa:.0f}%;background:#94a3b8"></div>'
                 f'<div style="width:{100 - pa:.0f}%;background:#2563eb"></div></div></div>')
    return html


# Every ESPN team-sport league we scan for the all-ESPN board.
ALL_ESPN_LEAGUES = [
    'football/nfl', 'football/college-football', 'football/ufl',
    'basketball/nba', 'basketball/wnba', 'basketball/mens-college-basketball',
    'basketball/womens-college-basketball', 'basketball/nba-development',
    'baseball/mlb', 'baseball/college-baseball', 'hockey/nhl',
    'hockey/mens-college-hockey', 'soccer/usa.1', 'soccer/eng.1', 'soccer/esp.1',
    'soccer/ger.1', 'soccer/ita.1', 'soccer/fra.1', 'soccer/uefa.champions',
    'soccer/uefa.europa', 'soccer/mex.1', 'soccer/usa.nwsl', 'soccer/eng.2',
]


@st.cache_data(ttl=60, show_spinner=False)
def fetch_board(ep: str) -> pd.DataFrame:
    """Live and upcoming (next 24h) games for one league."""
    try:
        events = _get(SCOREBOARD.format(ep=ep)).get('events', [])
    except Exception:
        return pd.DataFrame()
    now = pd.Timestamp.utcnow()
    rows = []
    for ev in events:
        comp = (ev.get('competitions') or [{}])[0]
        state = comp.get('status', {}).get('type', {}).get('state')
        start = pd.to_datetime(ev.get('date'), utc=True, errors='coerce')
        if state == 'post' or (state == 'pre' and (start is pd.NaT or start - now > pd.Timedelta('24h'))):
            continue
        t = {c.get('homeAway'): c for c in comp.get('competitors', [])}
        h, a = t.get('home', {}), t.get('away', {})
        tv = ', '.join(b.get('media', {}).get('shortName', '') for b in comp.get('broadcasts', [])
                       if b.get('media', {}).get('shortName')) or ', '.join(
            n for b in comp.get('broadcasts', []) for n in b.get('names', []))
        rows.append({'ep': ep, 'state': state, 'start': start,
                     'detail': comp.get('status', {}).get('type', {}).get('shortDetail', ''),
                     'away': a.get('team', {}).get('displayName', ''),
                     'home': h.get('team', {}).get('displayName', ''),
                     'away_score': a.get('score', ''), 'home_score': h.get('score', ''),
                     'tv': tv})
    return pd.DataFrame(rows)


def render_all_espn(label: Callable[[str], str]) -> None:
    @st.fragment(run_every=60)
    def _board():
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=6) as pool:
            frames = list(pool.map(fetch_board, ALL_ESPN_LEAGUES))
        frames = [f for f in frames if not f.empty]
        stamp = datetime.now().strftime('%I:%M %p')
        if not frames:
            st.info(f'Nothing live or starting in the next 24 hours across ESPN ({stamp}).')
            return
        allg = pd.concat(frames, ignore_index=True)
        n_live = int((allg['state'] == 'in').sum())
        n_pre = int((allg['state'] == 'pre').sum())
        st.caption(f'{n_live} live · {n_pre} starting in the next 24h · '
                   f'{len(ALL_ESPN_LEAGUES)} ESPN leagues scanned · updated {stamp}')
        tz = datetime.now().astimezone().tzinfo
        allg['sort'] = allg['state'].map({'in': 0, 'pre': 1})
        for ep, grp in sorted(allg.groupby('ep'), key=lambda x: (x[1]['sort'].min(), -len(x[1]))):
            live_n = int((grp['state'] == 'in').sum())
            with st.expander(f"{label(ep)} — {live_n} live · {len(grp) - live_n} upcoming",
                             expanded=live_n > 0):
                grp = grp.sort_values(['sort', 'start'])
                st.dataframe(pd.DataFrame({
                    'Status': ['🔴 ' + d if s == 'in' else '🕒 ' + st_.tz_convert(tz).strftime('%a %I:%M %p')
                               for s, d, st_ in zip(grp['state'], grp['detail'], grp['start'])],
                    'Away': grp['away'],
                    'Score': [f'{a}–{h}' if s == 'in' else '' for s, a, h in
                              zip(grp['state'], grp['away_score'], grp['home_score'])],
                    'Home': grp['home'], 'TV': grp['tv']}),
                    hide_index=True, use_container_width=True)
    _board()


def win_prob_series(summary: Dict) -> List[float]:
    return [w.get('homeWinPercentage', 0.5) for w in (summary.get('winprobability') or [])]


# ── Rendering: live centre ────────────────────────────────────

def _scoreline(g) -> str:
    def side(abbr, logo, score, lead):
        img = f'<img src="{logo}" style="width:26px;height:26px;object-fit:contain">' if logo else ''
        w = '800' if lead else '600'
        return (f'<div style="display:flex;align-items:center;gap:8px;padding:2px 0">{img}'
                f'<span style="flex:1;font-weight:{w}">{abbr}</span>'
                f'<span style="font-size:22px;font-weight:{w};font-variant-numeric:tabular-nums">'
                f'{score}</span></div>')
    return (side(g.away_abbr, g.away_logo, g.away_score, g.away_score > g.home_score)
            + side(g.home_abbr, g.home_logo, g.home_score, g.home_score > g.away_score))


def _live_game_card(db, worker, g, season: int, kalshi_home: Optional[float]) -> None:
    summ = fetch_summary(g.ep, g.espn_id)
    pred = pregame_prediction(db, worker, g.ep, season, g.home_id, g.away_id)
    proj = live_projection(g.ep, pred, g.home_score, g.away_score, g.period, g.clock)
    wp = win_prob_series(summ)
    espn_p = wp[-1] if wp else None

    with st.container(border=True):
        top = (f'<span class="tsg-pill" style="background:#fee2e2;color:#b91c1c;font-size:12px;'
               f'font-weight:700;padding:3px 10px;border-radius:999px">● LIVE · {g.detail}</span>')
        if g.situation:
            top += (f' <span style="font-size:12px;color:#475569;margin-left:6px">'
                    f'🏈 {g.situation}</span>')
        st.html(f'<div style="margin-bottom:6px">{top}</div>' + _scoreline(g))

        m1, m2, m3 = st.columns(3)
        m1.metric('Projected final',
                  f"{proj['away_final']:.0f}–{proj['home_final']:.0f}",
                  help='Current score + the pre-game model for the time left')
        p_away = 1 - proj['p_home'] - proj['p_draw']
        fav, fav_p = (g.home_abbr, proj['p_home']) if proj['p_home'] >= p_away else (g.away_abbr, p_away)
        m2.metric('Our win prob', f"{fav} {fav_p:.0%}",
                  f"draw {proj['p_draw']:.0%}" if proj['p_draw'] else None, delta_color='off')
        if espn_p is not None:
            fav_e = g.home_abbr if espn_p >= .5 else g.away_abbr
            m3.metric('ESPN win prob', f"{fav_e} {max(espn_p, 1 - espn_p):.0%}")
        elif kalshi_home is not None:
            fav_k = g.home_abbr if kalshi_home >= .5 else g.away_abbr
            m3.metric('Kalshi (live)', f"{fav_k} {max(kalshi_home, 1 - kalshi_home):.0%}")
        if kalshi_home is not None and espn_p is not None:
            st.caption(f"Kalshi live market: {g.home_abbr} {kalshi_home:.0%} · "
                       f"{proj['f']:.0%} of regulation left")
        else:
            st.caption(f"{proj['f']:.0%} of regulation left")

        if g.last_play:
            st.markdown(f"**Last play:** {g.last_play}")

        mo = momentum(summ)
        if mo and (mo[0] or mo[1]):
            lead = g.home_abbr if mo[1] > mo[0] else g.away_abbr
            st.caption(f"⚡ Momentum (last {mo[2]} plays): {g.away_abbr} {mo[0]} – {mo[1]} "
                       f"{g.home_abbr}" + (f" · {lead} on a run" if abs(mo[1] - mo[0]) >= 7 else ''))

        with st.expander('📊 Team analytics · 📈 win probability · ▶ play-by-play · box score'):
            ls = line_score(summ)
            if ls is not None:
                st.dataframe(ls, use_container_width=True)
            trows = team_stat_rows(summ)
            if trows:
                st.markdown('**Team stats**')
                st.html(_stat_bars(trows, g.away_abbr, g.home_abbr))
            if len(wp) > 1:
                fig = go.Figure(go.Scatter(y=[p * 100 for p in wp], mode='lines',
                                           line=dict(color='#2563eb', width=2), fill='tozeroy',
                                           fillcolor='rgba(37,99,235,.08)'))
                fig.add_hline(y=50, line_dash='dot', line_color='#94a3b8')
                fig.update_layout(height=220, margin=dict(l=10, r=10, t=10, b=10),
                                  yaxis=dict(range=[0, 100], title=f'{g.home_abbr} win %'),
                                  xaxis=dict(title='Play', showgrid=False))
                st.plotly_chart(fig, use_container_width=True, key=f'wp_{g.espn_id}')
            plays = recent_plays(summ)
            if plays:
                st.markdown('**Latest plays**')
                st.html(''.join(
                    f'<div style="padding:6px 0;border-bottom:1px solid #eef1f6;font-size:13px">'
                    f'<span style="color:#64748b;font-size:12px;margin-right:8px">{p["when"]}</span>'
                    f'{"🔥 " if p["scoring"] else ""}{p["text"]}'
                    f'<span style="float:right;color:#64748b;font-size:12px">{p["score"]}</span></div>'
                    for p in plays))
            boxes = box_tables(summ)
            if boxes:
                st.markdown('**Live box score**')
                tabs = st.tabs(list(boxes))
                for tab, abbr in zip(tabs, boxes):
                    with tab:
                        for cat, df in boxes[abbr].items():
                            st.caption(cat)
                            st.dataframe(df, hide_index=True, use_container_width=True)


def render_live_now(db: Any, worker: Any, leagues: List[str],
                    season_for: Callable[[str], int], label: Callable[[str], str]) -> None:
    @st.fragment(run_every=REFRESH_SECONDS)
    def _feed():
        # Your leagues, plus any other ESPN league that has a game live right now.
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=6) as pool:
            boards = dict(zip(ALL_ESPN_LEAGUES, pool.map(fetch_board, ALL_ESPN_LEAGUES)))
        extra = [ep for ep, b in boards.items()
                 if ep not in leagues and not b.empty and (b['state'] == 'in').any()]
        frames = [fetch_live_games(ep) for ep in list(leagues) + extra]
        live = pd.concat([f for f in frames if not f.empty], ignore_index=True) \
            if any(not f.empty for f in frames) else pd.DataFrame()
        stamp = datetime.now().strftime('%I:%M:%S %p')
        if live.empty:
            st.info(f'No games are live right now in your leagues. This page checks ESPN every '
                    f'{REFRESH_SECONDS}s (last check {stamp}).')
            return
        st.caption(f'{len(live)} live game(s) · ESPN feed (≈10–60s behind TV) · '
                   f'updated {stamp}, refreshes every {REFRESH_SECONDS}s')
        for ep, grp in live.groupby('ep', sort=False):
            st.markdown(f'#### {label(ep)}')
            if ep in KALSHI_SERIES:
                grp = attach_kalshi(grp.reset_index(drop=True),
                                    fetch_kalshi_markets(KALSHI_SERIES[ep])[0])
            else:
                grp = grp.assign(kalshi_home=None)
            for g in grp.itertuples():
                k = g.kalshi_home if g.kalshi_home is not None and not pd.isna(g.kalshi_home) else None
                _live_game_card(db, worker, g, season_for(ep.split('/')[0]), k)
    _feed()


# ── Rendering: best bets ──────────────────────────────────────

def _profit_per_100(american: float) -> float:
    return american if american > 0 else 10000 / -american


def find_bets(games: pd.DataFrame, ep: str) -> pd.DataFrame:
    """Every priced moneyline on the slate with the market-anchored probability
    (model blended into the market, weight fitted by the backtest), the book's
    no-vig probability, edge and EV per $100. Spreads/totals are model leans."""
    sigma = _SIGMA.get(ep.split('/')[0], 12.0)
    rows = []
    for g in games.itertuples():
        pred = g.pred
        if not pred:
            continue
        game = f'{g.away_abbr} @ {g.home_abbr}'
        ph = pred['p_home']

        def add(bet, market, book, price, p_model, p_market, side_price=None):
            if price is None or pd.isna(price) or p_model is None:
                return
            ev = p_model * _profit_per_100(price) - (1 - p_model) * 100
            rows.append({'Game': game, 'Bet': bet, 'Market': market, 'Book': book,
                         'Price': price, 'Model %': p_model, 'Market %': p_market,
                         'Edge': (p_model - p_market) if p_market is not None else None,
                         'EV / $100': ev})

        def nv(h, a):
            ph_, pa_ = american_to_prob(h), american_to_prob(a)
            return (ph_ / (ph_ + pa_), pa_ / (ph_ + pa_)) if ph_ and pa_ else (ph_, pa_)

        # Consensus = average no-vig probability across every source we see;
        # the model is blended into the consensus, and each book is compared
        # against that (so price differences between books show up as edges).
        books = [(b, h, a) for b, h, a in (('FanDuel', g.fd_home_ml, g.fd_away_ml),
                                           (g.espn_book or 'ESPN book', g.espn_home_ml, g.espn_away_ml))
                 if h is not None and not pd.isna(h) and a is not None and not pd.isna(a)]
        probs = [nv(h, a)[0] for _, h, a in books]
        if g.kalshi_home is not None and not pd.isna(g.kalshi_home):
            probs.append(float(g.kalshi_home))
        probs = [p for p in probs if p is not None]
        consensus = sum(probs) / len(probs) if probs else None
        pb = blended_prob(ep, ph, consensus)
        for book, h, a in books:
            mh, ma = nv(h, a)
            add(f'{g.home_abbr} moneyline', 'moneyline', book, h, pb, mh)
            add(f'{g.away_abbr} moneyline', 'moneyline', book, a, 1 - pb, ma)
        if g.kalshi_home is not None and not pd.isna(g.kalshi_home):
            k = float(g.kalshi_home)
            add(f'{g.home_abbr} to win', 'moneyline', 'Kalshi', prob_to_american(k), pb, k)
            add(f'{g.away_abbr} to win', 'moneyline', 'Kalshi', prob_to_american(1 - k), 1 - pb, 1 - k)
        # Spread & total: raw model vs ESPN line at standard -110 (not validated).
        if g.espn_spread is not None and not pd.isna(g.espn_spread):
            hs = float(g.espn_spread)
            p_cover = _norm_cdf((pred['margin'] + hs) / sigma)
            add(f'{g.home_abbr} {hs:+g}', 'spread', g.espn_book or 'ESPN book', -110, p_cover, 0.5)
            add(f'{g.away_abbr} {-hs:+g}', 'spread', g.espn_book or 'ESPN book', -110, 1 - p_cover, 0.5)
        if g.espn_total is not None and not pd.isna(g.espn_total):
            line = float(g.espn_total)
            tot = pred['home_pts'] + pred['away_pts']
            p_over = 1 - _norm_cdf((line - tot) / (sigma * 1.2))
            add(f'Over {line:g}', 'total', g.espn_book or 'ESPN book', -110, p_over, 0.5)
            add(f'Under {line:g}', 'total', g.espn_book or 'ESPN book', -110, 1 - p_over, 0.5)
    return pd.DataFrame(rows)


def _bet_table(df: pd.DataFrame) -> pd.DataFrame:
    return df.drop(columns=['Market']).assign(
        Price=df['Price'].map(lambda p: f'{p:+.0f}'),
        **{'Model %': df['Model %'].map('{:.0%}'.format),
           'Market %': df['Market %'].map(lambda p: '—' if p is None else f'{p:.0%}'),
           'Edge': df['Edge'].map(lambda e: '—' if e is None else f'{e:+.1%}'),
           'EV / $100': df['EV / $100'].map(lambda v: f'${v:+.0f}')})


def render_best_bets(db: Any, worker: Any, ep: str, season: int, label: Callable[[str], str]) -> None:
    st.caption(f'{label(ep)} · upcoming games · market-anchored model vs every line we can see.')
    with st.spinner('Pricing the slate…'):
        games, err = build_slate(db, worker, ep, season)
    if err:
        st.warning(f'ESPN: {err}')
    if games.empty:
        st.info('No upcoming games with lines for this league right now.')
        return
    bets = find_bets(games, ep)
    if bets.empty:
        st.info('Not enough completed games yet to model this slate.')
        return

    # Only a rule that held up in BOTH halves of the backtest becomes "Best bets".
    try:
        rule = json.loads(db.get_config(f'bet_rule_{ep}', '') or '{}')
    except ValueError:
        rule = {}
    ml = bets[bets['Market'] == 'moneyline']
    if rule:
        side_ok = {'all': lambda p: True, 'underdogs': lambda p: p > 0,
                   'favorites': lambda p: p < 0}[rule['side']]
        picks = ml[(ml['Edge'].fillna(0) >= rule['edge']) & ml['Price'].map(side_ok)]
        picks = picks.sort_values('EV / $100', ascending=False).drop_duplicates(['Game', 'Bet'])
        st.success(f"**Validated rule:** {rule['side']} moneylines with edge ≥ {rule['edge']:.0%} — "
                   f"profitable in both backtest halves ({rule['roi_early']:+.1%} and "
                   f"{rule['roi_late']:+.1%}). See 📊 Backtest.")
        if picks.empty:
            st.info('No game on this slate meets the validated rule right now.')
        else:
            top = picks.head(3)
            cols = st.columns(len(top))
            for col, (_, b) in zip(cols, top.iterrows()):
                with col.container(border=True):
                    st.markdown(f"**{b['Bet']}**  \n{b['Game']}")
                    st.metric(f"{b['Book']} {b['Price']:+.0f}", f"${b['EV / $100']:+.0f} EV",
                              f"edge {b['Edge']:+.1%}")
            st.dataframe(_bet_table(picks), hide_index=True, use_container_width=True)
    else:
        st.warning('**No validated betting edge for this league.** In the 📊 Backtest, no rule '
                   'made money in both the earlier and the later seasons, so nothing here is '
                   'a recommendation. Below are the biggest places the model disagrees with '
                   'the market — useful for research, not for betting.')

    with st.expander('🔍 Model leans — every market, biggest disagreements first',
                     expanded=not rule):
        leans = bets.dropna(subset=['Edge']).sort_values('Edge', ascending=False)
        leans = leans.drop_duplicates(['Game', 'Bet']).head(25)
        st.dataframe(_bet_table(leans), hide_index=True, use_container_width=True)
        st.caption('Moneyline probabilities are market-anchored: the model blended into the '
                   'consensus of all books with the backtest-fitted weight. A moneyline edge here '
                   'mostly means one book is pricing the game differently from the others. '
                   'Spreads/totals use the raw model at −110 and have not been validated.')
    st.caption('⚠️ Informational only, not betting advice. Kalshi prices exclude fees.')


def render_live_page(db: Any, worker: Any, leagues: List[str], g_league: str,
                     season_for: Callable[[str], int], label: Callable[[str], str]) -> None:
    st.markdown('## 🔴 Live & Best Bets')
    # A toggle, not st.tabs: tabs run every tab's code, and pricing the slate is slow.
    view = st.segmented_control('View', ['🔴 Live now', '📡 All of ESPN', '💡 Best bets'],
                                key='live_view', default='🔴 Live now',
                                label_visibility='collapsed')
    if view == '📡 All of ESPN':
        render_all_espn(label)
    elif view != '💡 Best bets':
        render_live_now(db, worker, leagues, season_for, label)
    else:
        if g_league in _HFA:
            render_best_bets(db, worker, g_league, season_for(g_league.split('/')[0]), label)
        else:
            st.info('Best bets are available for NFL, college football, NBA, WNBA, '
                    'college basketball, NHL and MLB.')

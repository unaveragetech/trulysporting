"""Live tracker component (frontend/index.html) plus post-game scorecards.

The component polls ESPN directly from the browser, so scores, clocks, field
views and watch alerts update with no Streamlit reruns and no server load.
Python only supplies pre-game predictions, which are logged before kickoff so
finished games can be graded honestly.
"""
import os
import re
import sqlite3
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime
from difflib import SequenceMatcher
from typing import Any, Callable, Dict, List, Optional

import pandas as pd
import streamlit as st
import streamlit.components.v1 as components

import matchups as _mu
from backtest import apply_shrink, load_games, run_backtest
from live import ALL_ESPN_LEAGUES, SCOREBOARD, SUMMARY, _get, pregame_prediction
from matchups import _HFA
from odds_page import fetch_espn_lines

_component = components.declare_component(
    'ts_tracker', path=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'frontend'))


# ── Prediction log ───────────────────────────────────────────

def _con(db_name: str) -> sqlite3.Connection:
    con = sqlite3.connect(db_name, timeout=30)
    con.execute('''CREATE TABLE IF NOT EXISTS prediction_log (
        event_id TEXT PRIMARY KEY, ep TEXT, logged_at TEXT, state TEXT,
        p_home REAL, margin REAL, total REAL)''')
    return con


def log_prediction(db_name: str, event_id: str, ep: str, state: str, pred: Dict) -> None:
    """Keep the latest pre-game number; never overwrite it once the game starts."""
    con = _con(db_name)
    if state == 'pre':
        con.execute('INSERT OR REPLACE INTO prediction_log VALUES (?,?,?,?,?,?,?)',
                    (event_id, ep, datetime.utcnow().isoformat(timespec='seconds'), state,
                     pred['p_home'], pred['margin'], pred['home_pts'] + pred['away_pts']))
    else:
        con.execute('INSERT OR IGNORE INTO prediction_log VALUES (?,?,?,?,?,?,?)',
                    (event_id, ep, datetime.utcnow().isoformat(timespec='seconds'), state,
                     pred['p_home'], pred['margin'], pred['home_pts'] + pred['away_pts']))
    con.commit()
    con.close()


def logged_predictions(db_name: str, ids: List[str]) -> Dict[str, Dict]:
    if not ids:
        return {}
    con = _con(db_name)
    rows = con.execute('SELECT event_id, p_home, margin, total, state FROM prediction_log '
                       f"WHERE event_id IN ({','.join('?' * len(ids))})", ids).fetchall()
    con.close()
    return {r[0]: {'p': r[1], 'm': r[2], 't': r[3], 'state': r[4]} for r in rows}


def slate_predictions(db: Any, worker: Any, leagues: List[str],
                      season_for: Callable[[str], int]) -> Dict[str, Dict]:
    """Pre-game numbers for current games in the active leagues, logged as they go."""
    preds: Dict[str, Dict] = {}
    for ep in [e for e in leagues if e in _HFA]:
        games, _ = fetch_espn_lines(ep)
        if games.empty:
            continue
        season = season_for(ep.split('/')[0])
        start = pd.to_datetime(games['date'], utc=True, errors='coerce')
        soon = games[(games['status'] == 'in') | ((games['status'] == 'pre') & (
            start < pd.Timestamp.now(tz='UTC') + pd.Timedelta('36h')))]

        def one(g, _ep=ep, _s=season):
            return g.espn_id, g.status, pregame_prediction(db, worker, _ep, _s, g.home_id, g.away_id)

        with ThreadPoolExecutor(max_workers=4) as pool:
            for eid, state, pred in pool.map(one, list(soon.itertuples())):
                if pred:
                    log_prediction(db.db_name, str(eid), ep, state, pred)
        preds.update(logged_predictions(db.db_name, [str(x) for x in games['espn_id']]))
    return preds


def render_tracker(db: Any, worker: Any, leagues: List[str], season_for, label,
                   tab: str = 'live') -> None:
    @st.fragment(run_every=180)
    def _inner():
        eps = list(dict.fromkeys(list(leagues) + ALL_ESPN_LEAGUES))
        preds = slate_predictions(db, worker, leagues, season_for)
        _component(leagues=[{'ep': e, 'label': label(e)} for e in eps], preds=preds, tab=tab,
                   key=f'ts_tracker_{tab}', default=None)
    _inner()


# ── Post-game scorecards ─────────────────────────────────────

@st.cache_data(ttl=120, show_spinner=False)
def _day_events(ep: str, day: str) -> List[Dict]:
    try:
        return _get(SCOREBOARD.format(ep=ep), dates=day).get('events', [])
    except Exception:
        return []


@st.cache_data(ttl=3600, show_spinner=False)
def _final_summary(ep: str, event_id: str) -> Dict:
    try:
        return _get(SUMMARY.format(ep=ep), event=event_id)
    except Exception:
        return {}


def _plays(s: Dict) -> List[Dict]:
    if s.get('plays'):
        return s['plays']
    out: List[Dict] = []
    for d in (s.get('drives') or {}).get('previous') or []:
        out += d.get('plays', [])
    return out


def game_flow(plays: List[Dict]) -> Dict:
    """Lead changes, ties and biggest lead for each side, from the play scores."""
    changes, ties, big_h, big_a, leader = 0, 0, 0, 0, 0
    last = None
    for p in plays:
        if p.get('homeScore') is None or p.get('awayScore') is None:
            continue
        d = int(p['homeScore']) - int(p['awayScore'])
        big_h, big_a = max(big_h, d), max(big_a, -d)
        sign = (d > 0) - (d < 0)
        if sign and leader and sign != leader:
            changes += 1
        if d == 0 and last not in (None, 0):
            ties += 1  # the game became tied (not every play while tied)
        if sign:
            leader = sign
        last = d
    return {'lead_changes': changes, 'ties': ties, 'big_home': big_h, 'big_away': big_a}


def timeouts_taken(plays: List[Dict], home: Dict, away: Dict) -> Dict[str, int]:
    """Team timeouts from the play feed. The text names the caller ("Timeout #2 by
    GB"); a play's `team` can be the team with the ball, so it is only a fallback."""
    out = {'home': 0, 'away': 0}
    for p in plays:
        ty = (p.get('type') or {}).get('text', '')
        if 'imeout' not in ty or 'official' in ty.lower() or 'tv' in ty.lower():
            continue
        txt = p.get('text', '')
        hit = None
        m = re.search(r'\bby\s+([A-Za-z]{2,5})\b', txt)
        if m:
            # Play text can use other codes than the scoreboard (BLT for BAL, ARZ for ARI).
            code = m.group(1).upper()
            hit = max(('home', 'away'), key=lambda x: SequenceMatcher(
                None, code, (home if x == 'home' else away)['abbr'].upper()).ratio())
        else:
            for side, t in (('home', home), ('away', away)):
                names = '|'.join(re.escape(x) for x in (t['abbr'], t['short']) if x)
                if re.search(rf'\b({names})\b', txt, re.I):
                    hit = side
                    break
        if hit is None:
            tid = str((p.get('team') or {}).get('id', ''))
            hit = 'home' if tid == home['id'] else 'away' if tid == away['id'] else None
        if hit:
            out[hit] += 1
    return out


def _retro_prediction(db: Any, ep: str, event_id: str, bounds) -> Optional[Dict]:
    """Walk-forward pick when none was logged before kickoff (uses earlier games only)."""
    if ep not in _HFA:
        return None
    n = len(load_games(db.db_name, ep))
    if n < 50:
        return None
    df = run_backtest(db.db_name, ep, n, bounds)
    if df.empty:
        return None
    df = apply_shrink(df, ep, _mu.CALIBRATION.get(ep, 1.0))
    row = df[df['event_id'].astype(str) == str(event_id)]
    if row.empty:
        return None
    r = row.iloc[0]
    return {'p': float(r['p_home']), 'm': float(r['pred_margin']), 't': float(r['pred_total']),
            'state': 'retro'}


def build_report(db: Any, ep: str, ev: Dict, logged: Dict, bounds) -> Dict:
    s = _final_summary(ep, ev['id'])
    comp = ev['competitions'][0]
    t = {c['homeAway']: c for c in comp['competitors']}

    def team(side):
        x = t[side]['team']
        return {'id': str(x.get('id')), 'abbr': x.get('abbreviation', ''),
                'name': x.get('displayName', ''),
                'short': x.get('shortDisplayName', x.get('name', '')) or x.get('abbreviation', '')}

    home, away = team('home'), team('away')
    hs, as_ = int(float(t['home'].get('score') or 0)), int(float(t['away'].get('score') or 0))
    wp = s.get('winprobability') or []
    pc = (s.get('pickcenter') or [{}])[0]
    ours = logged.get(ev['id']) or _retro_prediction(db, ep, ev['id'], bounds)
    plays = _plays(s)
    stats: Dict[str, Dict] = {}
    for tm in (s.get('boxscore') or {}).get('teams') or []:
        side = tm.get('homeAway') or (
            'home' if str(tm.get('team', {}).get('id')) == home['id'] else 'away')
        stats[side] = {x.get('label') or x.get('name'): x.get('displayValue')
                       for x in tm.get('statistics', [])}
    return {'id': ev['id'], 'home': home, 'away': away, 'hs': hs, 'as': as_, 'ours': ours,
            'espn_p': wp[0].get('homeWinPercentage') if wp else None,
            'book': (pc.get('provider') or {}).get('name'), 'line': pc.get('details'),
            'home_line': pc.get('spread'), 'total_line': pc.get('overUnder'),
            'flow': game_flow(plays), 'timeouts': timeouts_taken(plays, home, away),
            'stats': stats}


def _call(p: Optional[float], hs: int, as_: int) -> Optional[bool]:
    return None if p is None or hs == as_ else (p >= .5) == (hs > as_)


def render_results(db: Any, worker: Any, ep: str, label, bounds) -> None:
    st.caption(f"{label(ep)} · how our projector and ESPN's pre-game win probability "
               'did on finished games.')
    day = st.date_input('Date', value=date.today(), max_value=date.today(), key='res_day')
    ds = day.strftime('%Y%m%d')
    events = [e for e in _day_events(ep, ds)
              if e['competitions'][0]['status']['type'].get('state') == 'post']
    if not events:
        st.info('No finished games for this league on that date.')
        return
    # Make sure these games are stored, so a walk-forward pick can be computed.
    fresh = st.session_state.setdefault('_res_synced', set())
    if (ep, ds) not in fresh:
        fresh.add((ep, ds))
        cat, spt = ep.split('/')
        worker.fetch_date_scoreboard(cat, spt, ds)
    logged = logged_predictions(db.db_name, [e['id'] for e in events])
    with st.spinner('Grading the games…'):
        with ThreadPoolExecutor(max_workers=4) as pool:
            reps = list(pool.map(lambda e: build_report(db, ep, e, logged, bounds), events))

    ours = [_call((r['ours'] or {}).get('p'), r['hs'], r['as']) for r in reps]
    espn = [_call(r['espn_p'], r['hs'], r['as']) for r in reps]

    def tally(calls):
        return f"{sum(1 for x in calls if x)}/{sum(1 for x in calls if x is not None)}"

    c = st.columns(3)
    c[0].metric('Finished games', len(reps))
    c[1].metric('Our projector', tally(ours))
    c[2].metric('ESPN', tally(espn))

    mark = {True: '✅', False: '❌', None: '➖'}
    how = {'pre': 'logged before kickoff', 'in': 'logged during the game',
           'retro': 'replayed from earlier games'}
    for r, o_ok, e_ok in zip(reps, ours, espn):
        with st.container(border=True):
            win = r['home'] if r['hs'] > r['as'] else r['away']
            st.markdown(f"**{r['away']['name']} {r['as']} @ {r['home']['name']} {r['hs']}**"
                        + ('' if r['hs'] == r['as'] else f" · {win['abbr']} won"))
            a, b, d = st.columns(3)
            o = r['ours']
            if o:
                pick = r['home'] if o['p'] >= .5 else r['away']
                a.markdown(f"{mark[o_ok]} **Our projector:** {pick['abbr']} "
                           f"{max(o['p'], 1 - o['p']):.0%}  \n"
                           f"Margin error {abs(o['m'] - (r['hs'] - r['as'])):.1f} · "
                           f"{how.get(o.get('state'), '')}")
            else:
                a.markdown('➖ **Our projector:** no pick available')
            if r['espn_p'] is not None:
                pick = r['home'] if r['espn_p'] >= .5 else r['away']
                b.markdown(f"{mark[e_ok]} **ESPN:** {pick['abbr']} "
                           f"{max(r['espn_p'], 1 - r['espn_p']):.0%}")
            else:
                b.markdown('➖ **ESPN:** no win probability for this game')
            if r['line']:
                res = f"**Line:** {r['line']}"
                if r['home_line'] is not None:
                    v = (r['hs'] - r['as']) + float(r['home_line'])
                    covered = (r['home'] if v > 0 else r['away'])['abbr']
                    res += ' · Push' if v == 0 else f' · {covered} covered'
                if r['total_line'] is not None:
                    tot = r['hs'] + r['as']
                    side = 'Push' if tot == r['total_line'] else (
                        'Over' if tot > r['total_line'] else 'Under')
                    res += f"  \nTotal {r['total_line']}: {side} ({tot})"
                d.markdown(res + (f"  \n{r['book']}" if r['book'] else ''))
            fl = r['flow']
            bits = [f"Lead changes {fl['lead_changes']}", f"Ties {fl['ties']}",
                    f"Biggest lead {r['home']['abbr']} {fl['big_home']} / "
                    f"{r['away']['abbr']} {fl['big_away']}",
                    f"Timeouts used {r['away']['abbr']} {r['timeouts']['away']} / "
                    f"{r['home']['abbr']} {r['timeouts']['home']}"]
            for k in ('Turnovers', 'Total Yards', 'Possession', 'Rebounds', 'SHOTS'):
                sa, sh = r['stats'].get('away', {}).get(k), r['stats'].get('home', {}).get(k)
                if sa is not None and sh is not None:
                    bits.append(f'{k} {sa}–{sh}')
            st.caption(' · '.join(bits))
    st.caption('Timeouts are counted from the play feed where ESPN attributes them to a team. '
               'Grading is win/lose only: a 51% pick counts the same as a 90% pick.')

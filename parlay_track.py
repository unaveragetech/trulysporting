"""Saved parlays: storage in the visitor's browser, grading against ESPN results, and when each one resolves.

Parlays are saved in the visitor's own browser (localStorage), so there are no accounts and nothing to lose when the
server restarts.  Every saved leg carries the details needed to grade it from the final box score:

  won / lost / push / void   - settled (void = postponed, cancelled, or the player did not play)
  live                       - the game is in progress; we show where the leg stands
  pending                    - the game has not started

A parlay is LOST as soon as any leg loses; it is WON only when every game is over and nothing lost (void and push legs
drop out, as at a sportsbook); it is "busted" when a leg can no longer win but its game is still being played.
"""
from __future__ import annotations

import json
import os
import re
import time
import unicodedata
import uuid
from typing import Any, Dict, List, Optional, Tuple

import pandas as pd

STORE_KEY = 'ts_parlays_v1'

# Typical wall-clock length of a game, hours (overtime and delays add to it).
GAME_HOURS = {'football/nfl': 3.25, 'football/college-football': 3.5, 'basketball/nba': 2.5, 'basketball/wnba': 2.25,
              'basketball/mens-college-basketball': 2.25, 'basketball/womens-college-basketball': 2.25,
              'hockey/nhl': 2.6, 'baseball/mlb': 3.0}
_VOID_WORDS = ('POSTPON', 'CANCEL', 'FORFEIT', 'ABANDON')


# ── Browser storage ──────────────────────────────────────────────────────────

_CMP = None


def _component():
    global _CMP
    if _CMP is None:
        import streamlit.components.v1 as components
        _CMP = components.declare_component(
            'ts_store', path=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'frontend_store'))
    return _CMP


def store_sync() -> Optional[List[Dict]]:
    """Saved parlays for this visitor, or None until the browser has answered (first run of a visit)."""
    import streamlit as st
    ss = st.session_state
    val = _component()(skey=STORE_KEY, write=ss.get('pl_write'), write_id=ss.get('pl_write_id', 0), default=None, key='ts_store')
    if not ss.get('pl_hydrated') and val is not None:
        try:
            stored = json.loads(val.get('data') or '[]')
        except Exception:
            stored = []
        have = {r['id'] for r in ss.get('pl_saved', [])}
        ss['pl_saved'] = ss.get('pl_saved', []) + [r for r in stored if r.get('id') not in have]
        ss['pl_hydrated'] = True
    return ss.get('pl_saved') if ss.get('pl_hydrated') else None


def store_save(records: List[Dict]) -> None:
    import streamlit as st
    ss = st.session_state
    ss['pl_saved'] = records
    ss['pl_write'] = json.dumps(records)
    ss['pl_write_id'] = ss.get('pl_write_id', 0) + 1


def new_record(legs: List[Dict], name: str, p: float, source: str) -> Dict:
    return {'id': uuid.uuid4().hex[:10], 'name': name or f'{len(legs)}-leg parlay', 'created': pd.Timestamp.now(tz='UTC').isoformat(),
            'legs': legs, 'p_saved': p, 'source': source}


# ── Reading a game ───────────────────────────────────────────────────────────

def _norm(name: str) -> str:
    s = unicodedata.normalize('NFKD', str(name)).encode('ascii', 'ignore').decode().lower()
    s = re.sub(r"[^a-z0-9 ]", '', s.replace('-', ' '))
    return ' '.join(t for t in s.split() if t not in ('jr', 'sr', 'ii', 'iii', 'iv'))


def _num(v) -> Optional[float]:
    try:
        return float(str(v).split('-')[0].split('/')[0].replace(',', ''))
    except ValueError:
        return None


def parse_game(summary: Dict) -> Dict:
    """Flat view of an ESPN game summary: state, scores and every player stat by category."""
    comp = ((summary.get('header') or {}).get('competitions') or [{}])[0]
    st_ = comp.get('status', {})
    typ = st_.get('type', {})
    teams = {c.get('homeAway'): c for c in comp.get('competitors', [])}
    h, a = teams.get('home', {}), teams.get('away', {})

    def score(c):
        try:
            return int(float(c.get('score') or 0))
        except ValueError:
            return 0

    players: Dict[str, Dict[str, Dict[str, float]]] = {}
    for team in (summary.get('boxscore') or {}).get('players', []):
        for grp in team.get('statistics', []):
            cat = (grp.get('name') or 'stats').lower()
            labels = grp.get('labels') or []
            for ath in grp.get('athletes', []):
                nm = _norm((ath.get('athlete') or {}).get('displayName', ''))
                vals = ath.get('stats') or []
                if not nm or not vals:
                    continue
                d = players.setdefault(nm, {}).setdefault(cat, {})
                for lab, v in zip(labels, vals):
                    n = _num(v)
                    if n is not None:
                        d[lab] = n
    return {'state': typ.get('state', ''), 'name': typ.get('name', ''), 'detail': typ.get('shortDetail', ''),
            'period': st_.get('period', 0), 'clock': st_.get('displayClock', ''), 'start': comp.get('date', ''),
            'home_score': score(h), 'away_score': score(a), 'players': players}


def fetch_game(ep: str, event_id: str) -> Dict:
    """Cached ESPN lookup (30 s).  Returns {'state': 'unknown'} when ESPN cannot be reached."""
    import streamlit as st

    @st.cache_data(ttl=30, show_spinner=False)
    def _go(ep_: str, eid: str) -> Dict:
        from live import SUMMARY, _get
        try:
            return parse_game(_get(SUMMARY.format(ep=ep_), event=eid))
        except Exception:
            return {'state': 'unknown'}
    return _go(ep, str(event_id))


# ── Grading ──────────────────────────────────────────────────────────────────

def _player_value(game: Dict, meta: Dict) -> Optional[float]:
    rec = game.get('players', {}).get(_norm(meta.get('player', '')))
    if not rec:
        return None
    cats = rec.get(meta.get('cat', 'stats'))
    if cats is None:
        return None
    return cats.get(meta.get('stat'))


def grade_leg(leg: Dict, game: Dict) -> Dict:
    """{'status', 'detail', 'flag'} for one saved leg given the game's current state."""
    m = leg['meta']
    state = game.get('state', '')
    name = str(game.get('name', '')).upper()
    if any(w in name for w in _VOID_WORDS):
        return {'status': 'void', 'detail': 'game postponed or cancelled: leg is void', 'flag': None}
    if state in ('', 'unknown'):
        return {'status': 'pending', 'detail': 'waiting for ESPN', 'flag': None}
    if state == 'pre':
        return {'status': 'pending', 'detail': 'not started', 'flag': None}
    hs, as_ = game.get('home_score', 0), game.get('away_score', 0)
    final = state == 'post'
    kind = m['kind']
    flag = None
    if kind == 'ml':
        mine, theirs = (hs, as_) if m['side'] == 'home' else (as_, hs)
        detail = f'{mine}-{theirs}'
        res = 'won' if mine > theirs else 'lost' if mine < theirs else 'push'
    elif kind == 'spread':
        mine, theirs = (hs, as_) if m['side'] == 'home' else (as_, hs)
        adj = mine - theirs + m['line']
        detail = f'{mine}-{theirs}, covering by {adj:+g}'
        res = 'won' if adj > 0 else 'lost' if adj < 0 else 'push'
    elif kind == 'total':
        tot = hs + as_
        detail = f'total {tot} vs {m["line"]:g}'
        if m['side'] == 'over':
            res = 'won' if tot > m['line'] else 'lost' if tot < m['line'] else 'push'
            flag = 'secured' if tot > m['line'] else None
        else:
            res = 'won' if tot < m['line'] else 'lost' if tot > m['line'] else 'push'
            flag = 'dead' if tot > m['line'] else None
    elif kind == 'player':
        v = _player_value(game, m)
        label = f"{m['player']} {m['stat']}"
        if v is None:
            if final:
                return {'status': 'void', 'detail': f"{m['player']} did not play: leg is void", 'flag': None}
            return {'status': 'live', 'detail': f"{m['player']} not in the box score yet", 'flag': None}
        detail = f'{label}: {v:g} (needs {m["thr"]:g}+)'
        res = 'won' if v >= m['thr'] else 'lost'
        flag = 'secured' if v >= m['thr'] else None
    else:
        return {'status': 'pending', 'detail': 'unknown leg type', 'flag': None}
    if final:
        return {'status': res, 'detail': detail, 'flag': None}
    if kind in ('ml', 'spread'):
        return {'status': 'live', 'detail': f'{detail} so far', 'flag': None}
    return {'status': 'live', 'detail': detail + ' so far', 'flag': flag if flag else None}


def grade_parlay(rec: Dict, games: Dict[Tuple[str, str], Dict]) -> Dict:
    """Status of a whole saved parlay: legs graded, overall status, whether every game is over."""
    legs = []
    for leg in rec['legs']:
        g = games.get((leg['ep'], str(leg['game_id'])), {'state': 'unknown'})
        gr = grade_leg(leg, g)
        gr['game_state'] = g.get('state', '')
        legs.append(gr)
    sts = [l['status'] for l in legs]
    over = [l['game_state'] == 'post' or l['status'] == 'void' for l in legs]
    all_over = all(over)
    live_ct = sts.count('live')
    if 'lost' in sts:
        status = 'lost'
    elif any(l['flag'] == 'dead' for l in legs):
        status = 'busted'
    elif all_over:
        status = 'won' if 'won' in sts else 'void'
    elif live_ct or any(l['game_state'] == 'post' for l in legs):
        status = 'live'
    else:
        status = 'pending'
    return {'status': status, 'all_over': all_over, 'legs': legs, 'settled': status in ('won', 'lost', 'void') and all_over,
            'decided': status in ('lost', 'won', 'void')}


# ── When it resolves ─────────────────────────────────────────────────────────

def est_end(ep: str, start_iso: str, game: Dict, now: Optional[pd.Timestamp] = None) -> Optional[pd.Timestamp]:
    """Best guess at when a game finishes: kickoff + typical length, or time left on the clock for a live game."""
    now = now if now is not None else pd.Timestamp.now(tz='UTC')
    dur = pd.Timedelta(hours=GAME_HOURS.get(ep, 3.0))
    state = game.get('state', 'pre')
    if state == 'post' or any(w in str(game.get('name', '')).upper() for w in _VOID_WORDS):
        return None
    if state == 'in':
        from live import fraction_remaining
        f = fraction_remaining(ep, int(game.get('period') or 0), game.get('clock', ''))
        return now + max(pd.Timedelta(minutes=4), dur * f)
    t = pd.to_datetime(game.get('start') or start_iso, utc=True, errors='coerce')
    return None if pd.isna(t) else max(t + dur, now)


def resolution_plan(rec: Dict, games: Dict[Tuple[str, str], Dict], now: Optional[pd.Timestamp] = None) -> Dict:
    """Per-game start / expected finish and when the parlay as a whole should be decided."""
    now = now if now is not None else pd.Timestamp.now(tz='UTC')
    seen, rows = set(), []
    for leg in rec['legs']:
        gid = (leg['ep'], str(leg['game_id']))
        if gid in seen:
            continue
        seen.add(gid)
        g = games.get(gid, {'state': 'unknown'})
        rows.append({'game': leg['matchup'], 'league': leg['league'], 'state': g.get('state', ''),
                     'start': pd.to_datetime(g.get('start') or leg.get('start'), utc=True, errors='coerce'),
                     'ends': est_end(leg['ep'], leg.get('start', ''), g, now)})
    pend = [r['ends'] for r in rows if r['ends'] is not None]
    return {'games': rows, 'resolves_at': max(pend) if pend else None, 'first_end': min(pend) if pend else None}


def fmt_when(ts: Optional[pd.Timestamp], tz, now: Optional[pd.Timestamp] = None) -> str:
    if ts is None or pd.isna(ts):
        return 'final'
    now = now if now is not None else pd.Timestamp.now(tz='UTC')
    local = ts.tz_convert(tz)
    mins = int((ts - now).total_seconds() // 60)
    rel = 'now' if abs(mins) < 2 else (f'in {mins // 60}h {mins % 60:02d}m' if mins >= 60 else f'in {mins}m') if mins > 0 else 'overdue'
    return f"~{local.strftime('%a %I:%M %p').replace(' 0', ' ')} ({rel})"


# ── Track record ─────────────────────────────────────────────────────────────

def track_record(records: List[Dict]) -> Dict:
    """Settled parlays and legs: hit rate versus the probability we gave."""
    legs, parlays = [], []
    for r in records:
        res = r.get('result')
        if not res or not res.get('settled'):
            continue
        parlays.append((r['p_saved'], res['status'] == 'won'))
        for leg, gr in zip(r['legs'], res['legs']):
            if gr['status'] in ('won', 'lost'):
                legs.append((leg['p'], gr['status'] == 'won'))
    out: Dict[str, Any] = {'parlays': len(parlays), 'parlays_won': sum(w for _, w in parlays), 'legs': len(legs),
                           'legs_won': sum(w for _, w in legs)}
    if legs:
        out['avg_predicted'] = sum(p for p, _ in legs) / len(legs)
    buckets = []
    for lo, hi in ((0.5, 0.6), (0.6, 0.7), (0.7, 0.8), (0.8, 0.9), (0.9, 1.01)):
        b = [(p, w) for p, w in legs if lo <= p < hi]
        if b:
            buckets.append({'range': f'{lo:.0%}-{min(hi, 1):.0%}', 'legs': len(b), 'predicted': sum(p for p, _ in b) / len(b),
                            'actual': sum(w for _, w in b) / len(b)})
    out['buckets'] = buckets
    return out

"""Unabated market-data client (https://docs.unabated.com).

Rules this module follows:
  * The API key (``UNABATED_API_KEY``) is read from st.secrets / the environment and is only ever sent in the
    ``X-Api-Key`` header from the server. It is never written to a page, a link or the repo.
  * Free tier allows one odds request per 5 seconds per key; requests are serialised behind that gap and a
    ``429`` waits out ``Retry-After``.
  * Deep links come straight from each line's ``deepLink`` field. Their path is never edited or built by us; the
    only change is setting ``utm_campaign`` to the partner code (``UNABATED_PARTNER_CODE``), replacing any
    existing value. Without a partner code no link is published, since untagged clicks do not count.
"""
import os
import threading
import time
from statistics import median
from typing import Any, Dict, List, Optional
from urllib.parse import parse_qsl, urlencode, urlparse, urlunparse

import requests

BASE_URL = os.environ.get('UNABATED_API_BASE_URL', 'https://data.unabated.com').rstrip('/')
MIN_GAP = 5.0
BET_MONEYLINE, BET_SPREAD, BET_TOTAL = 1, 2, 3
_ABBR = {'JAC': 'JAX'}  # Unabated -> nflverse

_lock = threading.Lock()
_last_call = 0.0


def _secret(name: str) -> str:
    val = os.environ.get(name, '')
    if not val:
        try:
            import streamlit as st
            val = str(st.secrets.get(name, '') or '')
        except Exception:
            val = ''
    return val.strip()


def api_key() -> str:
    return _secret('UNABATED_API_KEY')


# Public tracking identifier (not a secret); override with UNABATED_PARTNER_CODE.
DEFAULT_PARTNER_CODE = 'jessewinghart'


def partner_code() -> str:
    return _secret('UNABATED_PARTNER_CODE') or DEFAULT_PARTNER_CODE


def tag_link(url: Optional[str], code: str) -> Optional[str]:
    """Return the API's deep link with ``utm_campaign`` set to our partner code (path untouched)."""
    if not url or not code:
        return None
    parts = urlparse(url)
    q = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True) if k != 'utm_campaign']
    q.append(('utm_campaign', code))
    return urlunparse(parts._replace(query=urlencode(q)))


def _get(path: str, params: Optional[list] = None, odds: bool = False) -> Dict[str, Any]:
    global _last_call
    key = api_key()
    if not key:
        raise RuntimeError('UNABATED_API_KEY is not configured')
    for attempt in range(3):
        with _lock:
            if odds:
                wait = MIN_GAP - (time.time() - _last_call)
                if wait > 0:
                    time.sleep(wait)
                _last_call = time.time()
            resp = requests.get(f'{BASE_URL}{path}', params=params, headers={'X-Api-Key': key}, timeout=20)
        if resp.status_code in (429, 503) and attempt < 2:
            time.sleep(min(float(resp.headers.get('Retry-After', MIN_GAP)), 30))
            continue
        resp.raise_for_status()
        body = resp.json()
        if body.get('success') is False:
            if attempt < 2 and 'Unexpected error' in ' '.join(body.get('messages') or []):
                time.sleep(MIN_GAP)  # transient upstream hiccup
                continue
            raise RuntimeError('; '.join(body.get('messages') or ['Unabated request failed']))
        return body
    raise RuntimeError('Unabated rate limit; try again shortly')


def sources() -> Dict[int, str]:
    """marketSourceId -> sportsbook name (the props listing is the one that responds for every league)."""
    rows = _get('/market/nfl/props/sources').get('data') or []
    return {int(r['id']): r['name'] for r in rows}


def nfl_game_odds() -> Dict[str, Any]:
    """Raw pre-game NFL moneyline, spread and total boards."""
    params = [('betTypeId', BET_MONEYLINE), ('betTypeId', BET_SPREAD), ('betTypeId', BET_TOTAL)]
    data = _get('/market/nfl/straight/odds', params, odds=True).get('data') or {}
    pre = (((data.get('odds') or {}).get('nfl') or {}).get('periodTypes') or {}).get('game', {}).get('pregame') or {}
    return {'groups': list(pre.values()), 'updated': data.get('lastUpdated')}


def _live_lines(side: dict) -> List[dict]:
    return [l for l in (side.get('marketSourceLines') or {}).values()
            if l.get('price') is not None and not l.get('disabled') and l.get('statusId') == 1]


def _best(lines: List[dict], names: Dict[int, str], code: str, pick_points=None) -> Optional[dict]:
    if not lines:
        return None
    l = max(lines, key=lambda x: (x['price'] if pick_points is None else (pick_points(x), x['price'])))
    return {'book': names.get(int(l['marketSourceId']), f"#{l['marketSourceId']}"), 'price': l['price'],
            'points': l.get('points'), 'link': tag_link(l.get('deepLink'), code)}


def summarize(board: Dict[str, Any], names: Dict[int, str], code: str) -> List[Dict[str, Any]]:
    """One row per game: consensus spread/total and the best price (with tagged deep link) on each side."""
    games: Dict[int, Dict[str, Any]] = {}
    for g in board['groups']:
        if g.get('isLive'):
            continue
        name = g['eventName'].split(' @ ')
        if len(name) != 2:
            continue
        away, home = (n.split()[-1] for n in name)
        row = games.setdefault(g['eventId'], {
            'start': g.get('eventStart'), 'away': _ABBR.get(away, away), 'home': _ABBR.get(home, home)})
        sides = {s['sideIndex']: _live_lines(s) for s in g['sides'].values()}
        away_l, home_l = sides.get(0, []), sides.get(1, [])
        bt = g['betTypeId']
        if bt == BET_MONEYLINE:
            row['ml_away'], row['ml_home'] = _best(away_l, names, code), _best(home_l, names, code)
        elif bt == BET_SPREAD:
            pts = [l['points'] for l in home_l if l.get('points') is not None]
            if pts:
                row['spread'] = -median(pts)  # positive = home favoured, like the model
                row['spread_home'] = _best([l for l in home_l if l.get('points') is not None], names, code,
                                           pick_points=lambda x: x['points'])
        elif bt == BET_TOTAL:
            pts = [l['points'] for l in home_l + away_l if l.get('points') is not None]
            if pts:
                row['total'] = median(pts)
    return sorted(games.values(), key=lambda r: r.get('start') or '')

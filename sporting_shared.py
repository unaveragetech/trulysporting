"""Helpers needed by modules that cannot import the sporting.py app script."""
from datetime import date, datetime, tzinfo
from typing import Tuple
from zoneinfo import ZoneInfo

import streamlit as st


def viewer_tz() -> tzinfo:
    """The browser's timezone; falls back to the server's."""
    try:
        if st.context.timezone:
            return ZoneInfo(st.context.timezone)
    except Exception:
        pass
    return datetime.now().astimezone().tzinfo


def viewer_today() -> date:
    return datetime.now(viewer_tz()).date()


def season_bounds(category: str, season_year: int) -> Tuple[str, str]:
    """(start, end) dates of an ESPN season year; mirrors SportsDB.season_bounds."""
    yr, cat = int(season_year), category.lower()
    if cat == 'football':
        return f'{yr}-08-01', f'{yr + 1}-03-01'
    if cat in ('basketball', 'hockey'):
        return f'{yr - 1}-09-01', f'{yr}-07-01'
    if cat == 'baseball':
        return f'{yr}-02-01', f'{yr}-11-30'
    return f'{yr - 1}-07-01', f'{yr}-07-01'


# ── Live detection and ESPN scoreboard requests that do not miss games ───────
import re as _re
from concurrent.futures import ThreadPoolExecutor as _Pool
from typing import Dict, List

import requests as _requests

# ESPN status names that mean a game is being played right now, including the gaps inside a game
# (end of period, intermission, delays, overtime, shootouts).  FINAL, SCHEDULED, POSTPONED are not live.
LIVE_STATUS_RE = (r'^(?!.*FINAL).*(?:PROGRESS|HALF|LIVE|END_PERIOD|END_OF|OVERTIME|SHOOTOUT|DELAY|EXTRA|PENALT|'
                  r'INTERMISSION|IN_PLAY|TIMEOUT)')


def status_is_live(name) -> bool:
    s = str(name or '').upper()
    return bool(_re.search(LIVE_STATUS_RE, s))


def et_dates() -> List[str]:
    """[today, yesterday] as YYYYMMDD in US Eastern time, the calendar ESPN buckets games by."""
    from datetime import timedelta
    now = datetime.now(ZoneInfo('America/New_York'))
    return [now.strftime('%Y%m%d'), (now - timedelta(days=1)).strftime('%Y%m%d')]


ESPN_SITE = 'https://site.api.espn.com/apis/site/v2/sports/{ep}/scoreboard'
# ESPN's default scoreboard hides most college games unless a group is requested.
COLLEGE_GROUPS: Dict[str, List[str]] = {
    'football/college-football': ['80', '81'],  # FBS, FCS
    'basketball/mens-college-basketball': ['50'],
    'basketball/womens-college-basketball': ['50'],
}


def board_requests(ep: str) -> List[Dict]:
    """Query-parameter sets that together cover every game on, or just rolled off, the board for a league."""
    today, yday = et_dates()
    college = ep in COLLEGE_GROUPS
    early = datetime.now(ZoneInfo('America/New_York')).hour < 7
    reqs: List[Dict] = []
    for g in COLLEGE_GROUPS.get(ep, [None]):
        base: Dict = {'limit': 300}
        if g:
            base['groups'] = g
        if not college:
            reqs.append(dict(base))  # ESPN's own notion of the current day
        reqs.append({**base, 'dates': today})
        if not college or early:  # games that started last evening and are still going
            reqs.append({**base, 'dates': yday})
    return reqs


def fetch_events(ep: str, timeout: float = 12.0) -> List[Dict]:
    """Raw ESPN events for a league from every request above, de-duplicated by event id."""
    seen: Dict[str, Dict] = {}
    for params in board_requests(ep):
        try:
            r = _requests.get(ESPN_SITE.format(ep=ep), params=params, timeout=timeout,
                              headers={'User-Agent': 'Mozilla/5.0 (TrulySporting)'})
            r.raise_for_status()
            for ev in r.json().get('events', []):
                seen[str(ev.get('id'))] = ev
        except Exception:
            continue
    return list(seen.values())


def fetch_events_many(eps: List[str], workers: int = 10) -> Dict[str, List[Dict]]:
    with _Pool(max_workers=workers) as pool:
        return dict(zip(eps, pool.map(fetch_events, eps)))

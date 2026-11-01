"""Every Odds API call goes through here.

- Persistent cache in SQLite (survives restarts, shared by every visitor), so
  the same request is never paid for twice within its TTL.
- Budget guard: a daily credit cap (default 15/day ≈ 450/month) and a reserve
  floor; calls that would break either are refused instead of spending.
- Usage tracking from the API's own headers (x-requests-remaining/-last).

Cost model (The Odds API): credits = markets × regions per call; the events
list is free.
"""
import json
import os
import sqlite3
import threading
import time
from datetime import date
from typing import Any, Dict, Optional, Tuple

import requests

DB_NAME = os.environ.get('TS_DB', 'espn_deep_analytics.db')
DEFAULT_DAILY_CAP = 15
RESERVE = 25            # never spend below this many remaining credits
_LOCK = threading.Lock()


def _con() -> sqlite3.Connection:
    con = sqlite3.connect(DB_NAME, timeout=30)
    con.execute('CREATE TABLE IF NOT EXISTS odds_api_cache '
                '(key TEXT PRIMARY KEY, fetched REAL, body TEXT)')
    con.execute('CREATE TABLE IF NOT EXISTS config (key TEXT PRIMARY KEY, value TEXT)')
    return con


def _cfg(con, key: str, default: str = '') -> str:
    row = con.execute('SELECT value FROM config WHERE key=?', (key,)).fetchone()
    return row[0] if row else default


def _set(con, key: str, value: Any) -> None:
    con.execute('INSERT OR REPLACE INTO config (key, value) VALUES (?, ?)', (key, str(value)))


def usage() -> Dict[str, Any]:
    con = _con()
    today = date.today().isoformat()
    out = {'remaining': _cfg(con, 'oddsapi_remaining', '?'),
           'used_today': int(_cfg(con, f'oddsapi_used_{today}', '0') or 0),
           'daily_cap': int(_cfg(con, 'oddsapi_daily_cap', str(DEFAULT_DAILY_CAP)) or DEFAULT_DAILY_CAP),
           'last_call': _cfg(con, 'oddsapi_last_call', '')}
    con.close()
    return out


def refresh_remaining(api_key: str) -> None:
    """The /sports listing costs no credits and reports the balance in its headers."""
    try:
        r = requests.get('https://api.the-odds-api.com/v4/sports',
                         params={'apiKey': api_key}, timeout=10)
        left = r.headers.get('x-requests-remaining')
        if left:
            con = _con()
            _set(con, 'oddsapi_remaining', left)
            con.commit()
            con.close()
    except Exception:
        pass


def set_daily_cap(cap: int) -> None:
    con = _con()
    _set(con, 'oddsapi_daily_cap', int(cap))
    con.commit()
    con.close()


def cached_get(url: str, params: Dict[str, Any], cost: int, ttl: int,
               cache_key: str) -> Tuple[Optional[Any], str]:
    """Return (json, error). Serves from cache when fresh; otherwise spends
    `cost` credits only if the budget allows."""
    with _LOCK:
        con = _con()
        try:
            row = con.execute('SELECT fetched, body FROM odds_api_cache WHERE key=?',
                              (cache_key,)).fetchone()
            if row and time.time() - row[0] < ttl:
                return json.loads(row[1]), ''
            if cost > 0:
                today = date.today().isoformat()
                used = int(_cfg(con, f'oddsapi_used_{today}', '0') or 0)
                cap = int(_cfg(con, 'oddsapi_daily_cap', str(DEFAULT_DAILY_CAP)) or DEFAULT_DAILY_CAP)
                remaining = _cfg(con, 'oddsapi_remaining', '')
                if used + cost > cap:
                    stale = json.loads(row[1]) if row else None
                    return stale, (f'Daily Odds API budget reached ({used}/{cap} credits today) — '
                                   + ('showing the last saved lines.' if stale else 'try tomorrow '
                                      'or raise the cap in ⚙️ Settings.'))
                if remaining.isdigit() and int(remaining) - cost < RESERVE:
                    stale = json.loads(row[1]) if row else None
                    return stale, f'Only {remaining} credits left this month — saving the reserve.'
            try:
                r = requests.get(url, params=params, timeout=15)
            except Exception as e:
                return (json.loads(row[1]) if row else None), str(e)
            spent = r.headers.get('x-requests-last')
            if r.headers.get('x-requests-remaining'):
                _set(con, 'oddsapi_remaining', r.headers['x-requests-remaining'])
            if spent and spent.isdigit():
                today = date.today().isoformat()
                _set(con, f'oddsapi_used_{today}',
                     int(_cfg(con, f'oddsapi_used_{today}', '0') or 0) + int(spent))
            _set(con, 'oddsapi_last_call', time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime()))
            con.commit()
            if r.status_code == 401:
                return None, 'Invalid ODDS_API_KEY.'
            if r.status_code == 422:
                return None, 'Not offered for this sport/game.'
            if r.status_code == 429:
                return (json.loads(row[1]) if row else None), 'Odds API rate limit — try again shortly.'
            if not r.ok:
                return (json.loads(row[1]) if row else None), f'HTTP {r.status_code}'
            body = r.json()
            con.execute('INSERT OR REPLACE INTO odds_api_cache VALUES (?, ?, ?)',
                        (cache_key, time.time(), json.dumps(body)))
            con.commit()
            return body, ''
        finally:
            con.close()

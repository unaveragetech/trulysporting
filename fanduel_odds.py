"""FanDuel odds via The Odds API (https://the-odds-api.com); page is in odds_page.py.

FanDuel has no public API, so lines come from The Odds API's `fanduel`
bookmaker feed. Each fetch is snapshotted to SQLite so line movement can be
charted over time. Set ODDS_API_KEY in .streamlit/secrets.toml or the env.
"""
import os
import sqlite3
from datetime import datetime
from typing import Dict, List, Optional, Tuple

import pandas as pd
import streamlit as st

ODDS_API_URL = "https://api.the-odds-api.com/v4/sports/{sport}/odds"

# ESPN ep_key → The Odds API sport key
ODDS_SPORT_MAP: Dict[str, str] = {
    'football/nfl':                        'americanfootball_nfl',
    'football/college-football':           'americanfootball_ncaaf',
    'basketball/nba':                      'basketball_nba',
    'basketball/wnba':                     'basketball_wnba',
    'basketball/mens-college-basketball':  'basketball_ncaab',
    'baseball/mlb':                        'baseball_mlb',
    'hockey/nhl':                          'icehockey_nhl',
    'soccer/usa.1':                        'soccer_usa_mls',
    'soccer/eng.1':                        'soccer_epl',
}

MARKET_LABELS = {'h2h': 'Moneyline', 'spreads': 'Spread', 'totals': 'Total'}


_KEY_NAMES = ('odds_api_key', 'the_odds_api_key', 'oddsapi_key', 'odds_key')


def _clean(v) -> str:
    return str(v or '').strip().strip('"').strip("'").strip()


def _secrets_file_problem() -> str:
    """Streamlit reports a malformed secrets.toml as 'no secrets'; parse it
    ourselves to give the real reason."""
    try:
        import tomllib  # Python 3.11+
    except ImportError:
        return ''
    for path in (os.path.join('.streamlit', 'secrets.toml'),
                 os.path.join(os.path.expanduser('~'), '.streamlit', 'secrets.toml')):
        if os.path.isfile(path):
            try:
                with open(path, 'rb') as f:
                    tomllib.load(f)
            except Exception as e:
                return (f'{path} is not valid TOML ({e}). Values must be quoted, '
                        'e.g. ODDS_API_KEY = "abc123".')
    return ''


def find_api_key() -> dict:
    """Locate the Odds API key and explain where it came from (or why not).

    Checks, in order: st.secrets at the root (any capitalisation), st.secrets
    inside any [section] (e.g. [odds] api_key = ...), then environment
    variables. Returns {'key', 'source', 'problems'} — never logs the value."""
    problems = []
    try:
        secrets = dict(st.secrets)
    except FileNotFoundError:
        secrets = {}
        problems.append(_secrets_file_problem() or 'No secrets are configured (st.secrets is empty).')
    except Exception as e:  # malformed TOML, e.g. a value without quotes
        secrets = {}
        problems.append(f'Secrets could not be parsed as TOML: {type(e).__name__}: {e}. '
                        'Values must be quoted, e.g. ODDS_API_KEY = "abc123".')
    for k, v in secrets.items():
        if k.lower() in _KEY_NAMES and isinstance(v, str) and _clean(v):
            return {'key': _clean(v), 'source': f'st.secrets["{k}"]', 'problems': problems}
    for sec, tbl in secrets.items():
        if hasattr(tbl, 'items'):
            for k, v in dict(tbl).items():
                if (k.lower() in _KEY_NAMES or (k.lower() == 'api_key' and 'odds' in sec.lower()))                         and _clean(v):
                    return {'key': _clean(v), 'source': f'st.secrets["{sec}"]["{k}"]',
                            'problems': problems}
    for k, v in os.environ.items():
        if k.lower() in _KEY_NAMES and _clean(v):
            return {'key': _clean(v), 'source': f'environment variable {k}', 'problems': problems}
    if secrets:
        problems.append('Secrets loaded, but none is named ODDS_API_KEY. Found: '
                        + ', '.join(sorted(secrets)) + '.')
    return {'key': '', 'source': '', 'problems': problems}


def _api_key() -> str:
    return find_api_key()['key']


def american_to_prob(price: Optional[float]) -> Optional[float]:
    if price is None or pd.isna(price) or price == 0:
        return None
    price = float(price)
    return 100 / (price + 100) if price > 0 else -price / (-price + 100)


def _init_table(db_name: str) -> None:
    con = sqlite3.connect(db_name)
    con.execute('''CREATE TABLE IF NOT EXISTS odds_snapshots (
        fetched_at TEXT, sport_key TEXT, game_id TEXT, commence_time TEXT,
        home_team TEXT, away_team TEXT, market TEXT, outcome TEXT,
        price REAL, point REAL)''')
    con.execute('CREATE INDEX IF NOT EXISTS idx_odds_game ON odds_snapshots(game_id, market)')
    con.commit()
    con.close()


FD_TTL = 1800  # 30 min — moneylines rarely move enough to matter faster


def fetch_fanduel_odds(odds_sport: str, api_key: str) -> Tuple[List[Dict], str, str]:
    """FanDuel moneylines for a league. Returns (events, error, credits_remaining).

    Costs 1 credit (h2h only; ESPN already supplies spreads/totals), cached
    30 min in SQLite for every visitor, and refused when over the budget."""
    from odds_budget import cached_get, usage
    body, err = cached_get(
        ODDS_API_URL.format(sport=odds_sport),
        {'apiKey': api_key, 'regions': 'us', 'bookmakers': 'fanduel',
         'markets': 'h2h', 'oddsFormat': 'american'},
        cost=1, ttl=FD_TTL, cache_key=f'fd_h2h_{odds_sport}')
    return (body or []), err, usage()['remaining']


def events_to_df(events: List[Dict]) -> pd.DataFrame:
    rows = []
    for ev in events:
        for bk in ev.get('bookmakers', []):
            if bk.get('key') != 'fanduel':
                continue
            for mk in bk.get('markets', []):
                for oc in mk.get('outcomes', []):
                    rows.append({
                        'game_id': ev['id'], 'commence_time': ev.get('commence_time', ''),
                        'home_team': ev.get('home_team', ''), 'away_team': ev.get('away_team', ''),
                        'market': mk['key'], 'outcome': oc.get('name', ''),
                        'price': oc.get('price'), 'point': oc.get('point'),
                    })
    df = pd.DataFrame(rows)
    if df.empty:
        return df
    df['implied'] = df['price'].map(american_to_prob)
    # Remove the vig: normalise implied probabilities within each game/market.
    df['no_vig'] = df['implied'] / df.groupby(['game_id', 'market'])['implied'].transform('sum')
    return df


def save_snapshot(db_name: str, sport_key: str, df: pd.DataFrame) -> None:
    if df.empty:
        return
    _init_table(db_name)
    con = sqlite3.connect(db_name)
    stamp = datetime.utcnow().replace(microsecond=0).isoformat()
    last = con.execute('SELECT MAX(fetched_at) FROM odds_snapshots WHERE sport_key=?',
                       (sport_key,)).fetchone()[0]
    # Don't write duplicate snapshots when serving from the 5-minute cache.
    if last and (datetime.utcnow() - datetime.fromisoformat(last)).total_seconds() < 240:
        con.close()
        return
    out = df[['game_id', 'commence_time', 'home_team', 'away_team',
              'market', 'outcome', 'price', 'point']].copy()
    out.insert(0, 'sport_key', sport_key)
    out.insert(0, 'fetched_at', stamp)
    out.to_sql('odds_snapshots', con, if_exists='append', index=False)
    con.close()


def load_history(db_name: str, game_id: str) -> pd.DataFrame:
    _init_table(db_name)
    con = sqlite3.connect(db_name)
    df = pd.read_sql('SELECT * FROM odds_snapshots WHERE game_id=? ORDER BY fetched_at',
                     con, params=(game_id,))
    con.close()
    return df


def _fmt_price(p) -> str:
    if p is None or pd.isna(p):
        return '—'
    return f'+{int(p)}' if p > 0 else str(int(p))


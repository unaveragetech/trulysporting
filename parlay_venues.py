"""Where can a watched parlay actually be bought, and which book is best?

A saved parlay is re-priced from live data, then every venue (sportsbook or exchange) is put through hard checks.
A venue is only called placeable when every check passes; anything doubtful is downgraded and the reason is shown.
"""
import threading
import time
from typing import Any, Dict, List, Optional, Tuple

import pandas as pd

import parlay_pricing as PP

MAX_QUOTE_AGE_S = 30 * 60      # older than this: stale, do not trust
WARN_QUOTE_AGE_S = 10 * 60     # older than this: warn
MIN_LEAD_S = 120               # a game starting within 2 minutes is treated as closed
MAX_AMERICAN = 5000            # beyond this a price is a placeholder or an error
MAX_LEGS_BOOK = 12             # most books cap a parlay near this size
OVERROUND_OK = (0.99, 1.20)    # both sides' implied chances must add to about 100-120% or the pair is corrupt
SPORTSBOOK_NAMES = set(PP.SPORTSBOOKS.values())
EXCHANGE_NAMES = set(PP.EXCHANGES.values())


def _age_s(ts: Optional[str], now: pd.Timestamp) -> Optional[float]:
    if not ts:
        return None
    t = pd.to_datetime(ts, utc=True, errors='coerce')
    return None if pd.isna(t) else max(0.0, (now - t).total_seconds())


def check_quote(q: Dict, now: pd.Timestamp) -> List[Tuple[str, str]]:
    """Problems with one price: a list of (severity, text) where severity is 'fail' or 'warn'."""
    out: List[Tuple[str, str]] = []
    if not q.get('exact', True):
        out.append(('fail', f"different line ({q.get('line')}); not the same bet"))
    dec = q.get('decimal') or 0
    if dec < 1.01 or dec > 1 + MAX_AMERICAN / 100:
        out.append(('fail', 'price is outside any sane range (placeholder or error)'))
    if abs(q.get('price') or 0) >= 10000 and q.get('opp') is not None and abs(q['opp']) >= 10000:
        out.append(('fail', 'placeholder price (+/-10000 on both sides) is not a real line'))
    elif q.get('price') is not None and q['price'] <= -1000:
        out.append(('warn', f"extreme favourite ({q['price']:+.0f}): many books cap or exclude such legs from parlays"))
    if q.get('opp') is not None and dec >= 1.01:
        over = PP.implied(q['price']) + PP.implied(q['opp'])
        if not OVERROUND_OK[0] <= over <= OVERROUND_OK[1]:
            out.append(('fail', f'two sides add to {over:.0%}, so the pair is corrupt or crossed'))
    age = _age_s(q.get('ts'), now)
    if age is None:
        out.append(('warn', 'no timestamp on this price'))
    elif age > MAX_QUOTE_AGE_S:
        out.append(('fail', f'price is {age / 60:.0f} minutes old'))
    elif age > WARN_QUOTE_AGE_S:
        out.append(('warn', f'price is {age / 60:.0f} minutes old'))
    return out


def check_leg_open(l: Any, now: pd.Timestamp) -> List[Tuple[str, str]]:
    """Can this leg still be bet at all (game exists, not started, not final)?"""
    out: List[Tuple[str, str]] = []
    st = l.info.get('live_state')
    if l.info.get('gone'):
        out.append(('fail', 'game is no longer on the board'))
    if st and st != 'pre':
        out.append(('fail', 'game has started or finished, so betting is closed'))
    t = pd.to_datetime(l.start, utc=True, errors='coerce')
    if not pd.isna(t) and (t - now).total_seconds() < MIN_LEAD_S:
        out.append(('fail', 'game starts within 2 minutes or already has'))
    return out


def evaluate(legs: List[Any], now: Optional[pd.Timestamp] = None) -> Dict[str, Any]:
    """Rank every venue for this parlay and say why each one passes or fails."""
    now = now or pd.Timestamp.now(tz='UTC')
    all_legs = legs
    legs = [l for l in all_legs if l.kind in ('ml', 'spread', 'total')]
    unv = [l for l in all_legs if l.kind not in ('ml', 'spread', 'total')]
    n = len(legs)
    general: List[Tuple[str, str]] = []
    if unv:
        general.append(('warn', f"{len(unv)} player leg(s) ({', '.join(l.pick for l in unv)}) have no price feed, so we cannot verify a book "
                                f"offers them. The price shown covers only the {n} verifiable leg(s); confirm the rest at the book"))
    if n == 0:
        return {'best': None, 'venues': [], 'general': [('fail', 'no legs')], 'checked': now.isoformat(), 'verdict': 'no'}
    if n > MAX_LEGS_BOOK:
        general.append(('warn', f'{n} legs: most books cap parlays near {MAX_LEGS_BOOK}'))
    seen = {}
    for l in legs:
        seen.setdefault(str(l.game_id), []).append(l)
    sgp = [v for v in seen.values() if len(v) > 1]
    if sgp:
        general.append(('warn', 'two or more legs come from the same game. Books price those as a same-game parlay (correlated) and often '
                                'refuse or reprice them, so our straight multiplication may not match the ticket'))
    keys = [l.key for l in legs]
    if len(set(keys)) != len(keys):
        general.append(('fail', 'the same leg appears twice'))
    leg_issues = [check_leg_open(l, now) for l in legs]
    open_fail = [(i, p) for i, ps in enumerate(leg_issues) for s, p in ps if s == 'fail']
    book_names = set()
    for l in legs:
        book_names |= {q['source'] for q in l.quotes if q['kind'] in ('sportsbook', 'espn')}
    venues: List[Dict[str, Any]] = []
    for name in sorted(book_names):
        reasons: List[Tuple[str, str]] = []
        dec, links, vias = 1.0, [], set()
        covered = 0
        for i, l in enumerate(legs):
            qs = [q for q in l.quotes if q['source'] == name and q['kind'] in ('sportsbook', 'espn')]
            exact = [q for q in qs if q.get('exact', True)]
            if not exact:
                why = 'quotes a different line' if qs else 'does not quote'
                reasons.append(('fail', f'{l.pick}: {name} {why}'))
                continue
            q = max(exact, key=lambda x: (x['via'] == 'Unabated', x['decimal']))
            probs = check_quote(q, now)
            for s, t in probs:
                reasons.append((s, f'{l.pick}: {t}'))
            if any(s == 'fail' for s, _ in probs):
                continue
            covered += 1
            dec *= q['decimal']
            links.append(q.get('link'))
            vias.add(q['via'])
        for i, p in open_fail:
            if legs[i].kind in ('ml', 'spread', 'total'):
                reasons.append(('fail', f'{legs[i].pick}: {p}'))
        # price cross-check: this book against the other books' price for the same leg (a big outlier is likely wrong)
        for l in legs:
            mine = [q for q in l.quotes if q['source'] == name and q.get('exact', True) and q['kind'] in ('sportsbook', 'espn')]
            others = [q['decimal'] for q in l.quotes if q['source'] != name and q.get('exact', True) and q['kind'] in ('sportsbook', 'espn')]
            if mine and len(others) >= 2:
                med = sorted(others)[len(others) // 2]
                if mine[0]['decimal'] > med * 1.25:
                    reasons.append(('warn', f"{l.pick}: {name}'s price is {mine[0]['decimal'] / med - 1:.0%} above the other books, double-check it"))
        fails = [r for r in reasons if r[0] == 'fail']
        warns = [r for r in reasons if r[0] == 'warn'] + [g for g in general if g[0] == 'warn']
        status = 'no' if fails or covered < n or any(g[0] == 'fail' for g in general) else ('caution' if warns else 'ok')
        venues.append({'name': name, 'type': 'sportsbook', 'status': status, 'decimal': dec if covered == n else None,
                       'american': PP.to_american(dec) if covered == n else None, 'covered': covered, 'n': n,
                       'reasons': reasons + [g for g in general if g not in reasons], 'links': links, 'via': sorted(vias)})
    # exchanges and prediction markets: only ever as separate single bets, never as a parlay
    ex_names = set()
    for l in legs:
        ex_names |= {q['source'] for q in l.quotes if q['kind'] == 'exchange'}
    for name in sorted(ex_names):
        reasons = [('warn', 'not a parlay: each leg is its own contract that you buy and that settles on its own. Rolling the winnings '
                            'from one into the next reproduces a parlay but needs every game to resolve in order')]
        dec, covered = 1.0, 0
        for l in legs:
            ex = [q for q in l.quotes if q['source'] == name and q['kind'] == 'exchange' and q.get('exact', True)]
            if not ex:
                reasons.append(('fail', f'{l.pick}: {name} has no contract for this'))
                continue
            probs = check_quote(ex[0], now)
            reasons += [(s, f'{l.pick}: {t}') for s, t in probs]
            if any(s == 'fail' for s, _ in probs):
                continue
            covered += 1
            dec *= ex[0]['decimal']
        reasons.append(('warn', 'price is a mid or last price plus an estimated fee, not a live order-book ask; the fill can differ'))
        status = 'no' if covered < n or open_fail else 'caution'
        venues.append({'name': name, 'type': 'exchange', 'status': status, 'decimal': dec if covered == n else None,
                       'american': PP.to_american(dec) if covered == n else None, 'covered': covered, 'n': n, 'reasons': reasons,
                       'links': [], 'via': sorted({q['via'] for l in legs for q in l.quotes if q['source'] == name})})
    order = {'ok': 0, 'caution': 1, 'no': 2}
    book_rank = lambda v: (order[v['status']], -(v['decimal'] or 0))
    sb = sorted([v for v in venues if v['type'] == 'sportsbook'], key=book_rank)
    ex = sorted([v for v in venues if v['type'] == 'exchange'], key=book_rank)
    best = next((v for v in sb if v['status'] == 'ok'), None) or next((v for v in sb if v['status'] == 'caution'), None)
    verdict = 'no' if best is None else best['status']
    return {'best': best, 'venues': sb + ex, 'general': general, 'checked': now.isoformat(), 'verdict': verdict,
            'unpriced_legs': [l.pick for l in unv], 'n_verified': n, 'closed': [legs[i].pick for i, _ in open_fail]}


# ── Live refresh of a saved parlay ──────────────────────────────────────────

def _games_by_id(eps: List[str]) -> Dict[str, Dict]:
    from live import fetch_all_games
    df = fetch_all_games(tuple(sorted(set(eps))))
    return {} if df.empty else {str(r['id']): r for r in df.to_dict('records')}


def _kalshi_by_ep(eps: List[str], games: Dict[str, Dict]) -> None:
    """Attach Kalshi's current win price to the games of each league that has Kalshi markets (best effort)."""
    try:
        from odds_page import KALSHI_SERIES, attach_kalshi, fetch_kalshi_markets
    except Exception:
        return
    for ep in set(eps):
        if ep not in KALSHI_SERIES:
            continue
        rows = [g for g in games.values() if g.get('ep') == ep]
        if not rows:
            continue
        try:
            df = pd.DataFrame(rows).assign(home_team=lambda d: d['home'], away_team=lambda d: d['away'])
            df = attach_kalshi(df.reset_index(drop=True), fetch_kalshi_markets(KALSHI_SERIES[ep])[0])
            for r in df.to_dict('records'):
                games[str(r['id'])]['kalshi_home'] = r.get('kalshi_home')
        except Exception:
            continue


def refresh_legs(legs: List[Any], now: Optional[pd.Timestamp] = None) -> List[Any]:
    """Replace each leg's saved prices with live ones. Legs whose game vanished are marked gone."""
    now = now or pd.Timestamp.now(tz='UTC')
    stamp = now.isoformat()
    eps = [l.ep for l in legs if l.kind in ('ml', 'spread', 'total')]
    games = _games_by_id(eps) if eps else {}
    _kalshi_by_ep(eps, games)
    for l in legs:
        if l.kind not in ('ml', 'spread', 'total'):
            continue
        l.quotes = []
        g = games.get(str(l.game_id))
        if g is None:
            l.info = {**l.info, 'gone': True}
            continue
        l.info = {**l.info, 'gone': False, 'live_state': g.get('state'), 'live_detail': g.get('detail')}
        side = l.meta.get('side')
        qs = PP.espn_quotes(g, l.kind, side)
        if l.kind == 'ml':
            qs += PP.kalshi_quote(g, side)
        for q in qs:
            q['ts'] = stamp
            if l.kind in ('spread', 'total') and q.get('line') is not None and abs(q['line'] - float(l.meta.get('line', q['line']))) > 0.01:
                q['exact'] = False
                q['note'] = f"line moved to {q['line']:+g}: not the bet you saved"
        l.quotes += qs
    PP.attach_unabated([l for l in legs if l.kind in ('ml', 'spread', 'total')], games)
    return legs


_CACHE: Dict[str, Tuple[float, Dict]] = {}
_CACHE_LOCK = threading.Lock()
TTL = 90


def check_record(rec: Dict, force: bool = False) -> Dict:
    """Live venue check for one saved parlay record (cached 90 seconds, so many open parlays share one round of requests)."""
    import parlays as P
    sig = rec['id'] + str(len(rec['legs']))
    with _CACHE_LOCK:
        hit = _CACHE.get(sig)
        if hit and not force and time.time() - hit[0] < TTL:
            return hit[1]
    try:
        legs = refresh_legs([P.leg_from_dict(d) for d in rec['legs']])
        res = evaluate(legs)
        res['error'] = None
    except Exception as e:  # a feed failing must never break the page
        res = {'best': None, 'venues': [], 'general': [], 'checked': pd.Timestamp.now(tz='UTC').isoformat(), 'verdict': 'no',
               'error': f'{type(e).__name__}: {e}'}
    with _CACHE_LOCK:
        _CACHE[sig] = (time.time(), res)
    return res

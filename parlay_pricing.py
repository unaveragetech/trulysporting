"""What a parlay costs and pays, from every price source we have.

How parlays are priced (the maths this module follows):
  * A sportsbook parlay pays the PRODUCT of its legs' decimal prices, so each leg's margin (the "vig") compounds:
    three -110 legs pay 6.96x instead of the 8.0x that three fair coin flips deserve.
  * The fair (no-vig) chance of a leg is its implied probability divided by the two sides' implied probabilities added
    together; the fair parlay chance is the product of the legs' fair chances.
  * Most books only price a parlay inside one book, so the placeable price is the best book that quotes EVERY leg at
    the same line.  Taking the best price for each leg from different books ("line shopping") is shown as an upper bound.
  * Exchanges and prediction markets (Kalshi, Novig, Polymarket) price single events, not parlays: shown per leg only.

Sources: ESPN's embedded book (DraftKings), Unabated (DraftKings, FanDuel, BetMGM, Caesars, theScore, Fanatics and the
exchanges, with deep links tagged with our partner code) and Kalshi.  Prices for player legs are not in our data; when
a parlay has unpriced legs the payout is an ESTIMATE using a standard book margin and is labelled as such.
"""
from __future__ import annotations

import math
import re
import threading
import time
from typing import Any, Dict, List, Optional, Tuple

import pandas as pd

SPORTSBOOKS = {1: 'DraftKings', 2: 'FanDuel', 4: 'BetMGM', 20: 'Caesars', 36: 'theScore Bet', 86: 'Fanatics'}
EXCHANGES = {89: 'Novig', 105: 'Kalshi', 111: 'Polymarket US', 107: 'Polymarket', 66: 'Prophet Exchange'}
ROUTES = {'football/nfl': 'nfl', 'football/college-football': 'cfb', 'basketball/nba': 'nba', 'basketball/wnba': 'wnba',
          'basketball/mens-college-basketball': 'cbb', 'hockey/nhl': 'nhl', 'baseball/mlb': 'mlb'}
STD_BOOK_FACTOR = 0.9545  # a two-way -110/-110 price pays 1.909x against a fair 2.0x
KALSHI_FEE_RATE = 0.07    # taker fee about 0.07 x P x (1 - P) per $1 contract (verify against Kalshi's schedule)
MAX_EST_PLAYER_P = 0.97


# ── Price maths ──────────────────────────────────────────────────────────────

def to_decimal(price: float) -> float:
    return 1 + (price / 100 if price > 0 else 100 / -price)


def to_american(decimal: float) -> Optional[int]:
    if decimal is None or decimal <= 1:
        return None
    return int(round((decimal - 1) * 100)) if decimal >= 2 else int(round(-100 / (decimal - 1)))


def implied(price: float) -> float:
    return 1 / to_decimal(price)


def devig(price: float, opp_price: float) -> float:
    """No-vig chance of the side priced at ``price`` given the other side's price."""
    a, b = implied(price), implied(opp_price)
    return a / (a + b)


def payout(decimal: float, stake: float) -> Tuple[float, float]:
    """(total returned, profit) for a winning ticket."""
    return stake * decimal, stake * (decimal - 1)


def quote(source: str, kind: str, price: float, opp: Optional[float], line: Optional[float], via: str, link: Optional[str] = None,
          note: str = '', exact: bool = True, ts: Optional[str] = None) -> Dict[str, Any]:
    return {'source': source, 'kind': kind, 'price': float(price), 'opp': None if opp is None else float(opp), 'line': line,
            'via': via, 'link': link, 'note': note, 'exact': exact, 'ts': ts, 'decimal': to_decimal(price)}


# ── ESPN and Kalshi quotes (always available) ────────────────────────────────

def _f(v) -> Optional[float]:
    try:
        x = float(v)
        return None if math.isnan(x) else x
    except (TypeError, ValueError):
        return None


def espn_quotes(g: Dict, kind: str, side: str) -> List[Dict]:
    """The price ESPN's embedded book (usually DraftKings) shows for this leg."""
    book = g.get('book') or 'ESPN book'
    if kind == 'ml':
        mine, opp = (_f(g.get('home_ml')), _f(g.get('away_ml'))) if side == 'home' else (_f(g.get('away_ml')), _f(g.get('home_ml')))
        line = None
    elif kind == 'spread':
        sp = _f(g.get('spread'))
        if sp is None:
            return []
        mine, opp = (_f(g.get('home_spread_price')), _f(g.get('away_spread_price'))) if side == 'home' else \
            (_f(g.get('away_spread_price')), _f(g.get('home_spread_price')))
        line = sp if side == 'home' else -sp
    elif kind == 'total':
        line = _f(g.get('total'))
        if line is None:
            return []
        mine, opp = (_f(g.get('over_price')), _f(g.get('under_price'))) if side == 'over' else (_f(g.get('under_price')), _f(g.get('over_price')))
    else:
        return []
    if mine is None:
        return []
    return [quote(book, 'espn', mine, opp, line, 'ESPN', note='price shown on ESPN at last check')]


def kalshi_quote(g: Dict, side: str) -> List[Dict]:
    """Kalshi game-winner contract: mid price plus the estimated taker fee, expressed as a payout price."""
    kh = _f(g.get('kalshi_home'))
    if kh is None or not 0.02 < kh < 0.98:
        return []
    p = kh if side == 'home' else 1 - kh
    cost = p + KALSHI_FEE_RATE * p * (1 - p)  # dollars paid per $1 contract
    return [quote('Kalshi', 'exchange', to_american(1 / cost) or 0, None, None, 'Kalshi',
                  note=f'prediction market, mid price {p:.2f} plus about {100 * KALSHI_FEE_RATE * p * (1 - p):.1f}c fee per contract; '
                       'single bets only, not parlays')]


# ── Unabated boards (multi-book) ─────────────────────────────────────────────

_BOARDS: Dict[str, Tuple[float, Optional[Dict]]] = {}
_BOARD_TTL, _FAIL_TTL = 120, 600
_LOCK = threading.Lock()
_STOP = {'the', 'of', 'fc', 'sc'}


def tokens(name: str) -> set:
    return {t for t in re.findall(r'[a-z0-9]+', str(name).lower()) if len(t) > 1 and t not in _STOP}


def overlap(a: set, b: set) -> float:
    return len(a & b) / min(len(a), len(b)) if a and b else 0.0


def _valid(line: Optional[Dict]) -> bool:
    return bool(line) and not line.get('disabled') and line.get('statusId', 1) == 1 and line.get('price') not in (None, 0) \
        and abs(line['price']) < 5000


def parse_board(data: Dict) -> Dict:
    """Unabated pre-game moneyline / spread / total boards keyed by event, with each book's prices and deep links."""
    events: Dict[Any, Dict] = {}
    for lg in (data.get('odds') or {}).values():
        pre = ((lg.get('periodTypes') or {}).get('game') or {}).get('pregame') or {}
        for g in pre.values():
            bt = g.get('betTypeId')
            if bt not in (1, 2, 3):
                continue
            parts = str(g.get('eventName', '')).split(' @ ')
            if len(parts) != 2:
                continue
            ev = events.setdefault(g['eventId'], {'id': g['eventId'], 'name': g['eventName'], 'start': g.get('eventStart'),
                                                  'teams': (tokens(parts[0]), tokens(parts[1])), 'ml': {}, 'spread': {}, 'total': {}})
            sides = {v.get('sideIndex'): v.get('marketSourceLines') or {} for v in g['sides'].values()}
            s0, s1 = sides.get(0, {}), sides.get(1, {})
            for sid in set(s0) & set(s1):
                a, b = s0[sid], s1[sid]  # side 0 = away / over, side 1 = home / under
                if not (_valid(a) and _valid(b)):
                    continue
                book = int(sid)
                if bt == 1:
                    ev['ml'][book] = {'away': a['price'], 'home': b['price'], 'link_away': a.get('deepLink'), 'link_home': b.get('deepLink')}
                elif bt == 2 and a.get('points') is not None and b.get('points') is not None:
                    ev['spread'][book] = {'away_pts': a['points'], 'away': a['price'], 'home_pts': b['points'], 'home': b['price'],
                                          'link_away': a.get('deepLink'), 'link_home': b.get('deepLink')}
                elif bt == 3 and a.get('points') is not None and b.get('points') is not None:
                    ev['total'][book] = {'over_pts': a['points'], 'over': a['price'], 'under_pts': b['points'], 'under': b['price'],
                                         'link_over': a.get('deepLink'), 'link_under': b.get('deepLink')}
    return {'events': list(events.values()), 'updated': data.get('lastUpdated')}


def fetch_board(route: str) -> Optional[Dict]:
    """One Unabated call per league, shared by every visitor (the free tier allows one odds call per 5 seconds)."""
    hit = _BOARDS.get(route)
    if hit and time.time() - hit[0] < (_BOARD_TTL if hit[1] else _FAIL_TTL):
        return hit[1]
    import unabated
    if not unabated.api_key():
        return None
    with _LOCK:
        hit = _BOARDS.get(route)
        if hit and time.time() - hit[0] < (_BOARD_TTL if hit[1] else _FAIL_TTL):
            return hit[1]
        try:
            body = unabated._get(f'/market/{route}/straight/odds', [('betTypeId', 1), ('betTypeId', 2), ('betTypeId', 3)], odds=True, tries=2)
            board = parse_board(body.get('data') or {})
        except Exception:
            board = None
        _BOARDS[route] = (time.time(), board)
        return board


def find_event(board: Dict, g: Dict) -> Optional[Dict]:
    """Match an ESPN game to an Unabated event by team names (loose token overlap) and start time."""
    a, h = tokens(g.get('away', '')), tokens(g.get('home', ''))
    t0 = pd.to_datetime(g.get('start'), utc=True, errors='coerce')
    best = None
    for ev in board['events']:
        if overlap(ev['teams'][0], a) < 0.67 or overlap(ev['teams'][1], h) < 0.67:
            continue
        t1 = pd.to_datetime(ev.get('start'), utc=True, errors='coerce')
        if not pd.isna(t0) and not pd.isna(t1) and abs((t1 - t0).total_seconds()) > 8 * 3600:
            continue
        best = ev
        break
    return best


def unabated_quotes(meta: Dict, ev: Dict, updated: Optional[int]) -> List[Dict]:
    import unabated
    code = unabated.partner_code()
    kind, side = meta['kind'], meta['side']
    ts = None if not updated else pd.Timestamp(updated, unit='ms', tz='UTC').isoformat()
    out: List[Dict] = []
    for sid, name in {**SPORTSBOOKS, **EXCHANGES}.items():
        k = 'sportsbook' if sid in SPORTSBOOKS else 'exchange'
        if kind == 'ml':
            m = ev['ml'].get(sid)
            if not m:
                continue
            price, opp, line, ok = m[side], m['home' if side == 'away' else 'away'], None, True
        elif kind == 'spread':
            m = ev['spread'].get(sid)
            if not m:
                continue
            line = m[f'{side}_pts']
            price, opp = m[side], m['home' if side == 'away' else 'away']
            ok = abs(line - meta['line']) < 0.01
        elif kind == 'total':
            m = ev['total'].get(sid)
            if not m:
                continue
            line = m[f'{side}_pts']
            price, opp = m[side], m['under' if side == 'over' else 'over']
            ok = abs(line - meta['line']) < 0.01
        else:
            continue
        if not ok and k == 'exchange':
            continue
        out.append(quote(name, k, price, opp, line, 'Unabated', unabated.tag_link(m.get(f'link_{side}'), code), exact=ok, ts=ts,
                         note='' if ok else f'different line ({line:+g}): not the same bet, shown for reference'))
    return out


def attach_unabated(legs: List[Any], games: Dict[str, Dict]) -> Dict:
    """Add every book's price to each game-level leg.  Returns coverage info for display."""
    info: Dict[str, Any] = {'leagues': {}, 'errors': []}
    by_ep: Dict[str, List[Any]] = {}
    for l in legs:
        if l.kind in ('ml', 'spread', 'total'):
            by_ep.setdefault(l.ep, []).append(l)
    for ep, ls in by_ep.items():
        route = ROUTES.get(ep)
        if not route:
            continue
        board = fetch_board(route)
        if board is None:
            info['errors'].append(ep)
            continue
        matched, cache = 0, {}
        for l in ls:
            g = games.get(str(l.game_id))
            if not g:
                continue
            if l.game_id not in cache:
                cache[l.game_id] = find_event(board, g)
            ev = cache[l.game_id]
            if ev:
                l.quotes += unabated_quotes(l.meta, ev, board.get('updated'))
        matched = sum(1 for v in cache.values() if v)
        info['leagues'][ep] = {'events': len(board['events']), 'games_matched': matched, 'games': len(cache),
                               'updated': board.get('updated')}
    return info


# ── The parlay price report ──────────────────────────────────────────────────

def _book_quotes(l: Any) -> Dict[str, Dict]:
    """Best exact sportsbook quote per book for a leg (Unabated is fresher than ESPN's embedded copy of the same book)."""
    out: Dict[str, Dict] = {}
    for q in l.quotes:
        if q['kind'] not in ('sportsbook', 'espn') or not q.get('exact', True):
            continue
        cur = out.get(q['source'])
        if cur is None or (q['via'] == 'Unabated' and cur['via'] != 'Unabated'):
            out[q['source']] = q
    return out


def leg_fair_p(l: Any) -> Optional[float]:
    ps = [devig(q['price'], q['opp']) for q in l.quotes if q.get('exact', True) and q['kind'] in ('sportsbook', 'espn') and q.get('opp')]
    return sum(ps) / len(ps) if ps else None


def price_report(legs: List[Any], p_ours: Optional[float] = None) -> Dict:
    """Everything about the cost of a parlay: per-leg quotes, placeable books, best case, fair price, EV and stakes."""
    n = len(legs)
    per_leg, books_sets = [], []
    fair, all_fair = 1.0, True
    for l in legs:
        bq = _book_quotes(l)
        ex = [q for q in l.quotes if q['kind'] == 'exchange' and q.get('exact', True)]
        allq = sorted([q for q in l.quotes if q.get('exact', True)], key=lambda q: -q['decimal'])
        near = [q for q in l.quotes if not q.get('exact', True)]
        fp = leg_fair_p(l)
        if fp is None:
            all_fair = False
        else:
            fair *= fp
        per_leg.append({'pick': l.pick, 'game': l.matchup, 'p_ours': l.p, 'p_fair_market': fp, 'quotes': allq, 'different_line': near,
                        'books': bq, 'exchanges': ex,
                        'best': max(bq.values(), key=lambda q: q['decimal']) if bq else None})
        books_sets.append(set(bq))
    priced = [x for x in per_leg if x['best']]
    all_priced = len(priced) == n and n > 0
    common = set.intersection(*books_sets) if books_sets and all(books_sets) else set()
    books = []
    for b in common:
        d = 1.0
        links = []
        for x in per_leg:
            d *= x['books'][b]['decimal']
            links.append(x['books'][b].get('link'))
        books.append({'book': b, 'decimal': d, 'american': to_american(d), 'links': links,
                      'via': sorted({x['books'][b]['via'] for x in per_leg})})
    books.sort(key=lambda r: -r['decimal'])
    shopped = None
    if all_priced:
        d = 1.0
        for x in per_leg:
            d *= x['best']['decimal']
        shopped = {'decimal': d, 'american': to_american(d)}
    est = None
    if not all_priced and n:
        d = 1.0
        notes = []
        for x in per_leg:
            if x['best']:
                d *= x['best']['decimal']
            else:
                pl = min(MAX_EST_PLAYER_P, max(0.01, x['p_ours']))
                d *= max(1.01, STD_BOOK_FACTOR / pl)
                notes.append(x['pick'])
        est = {'decimal': d, 'american': to_american(d), 'unpriced': notes}
    best_dec = books[0]['decimal'] if books else None
    p_fair = fair if all_fair and n else None
    report: Dict[str, Any] = {
        'legs': per_leg, 'n': n, 'n_priced': len(priced), 'all_priced': all_priced, 'books': books, 'best_book': books[0] if books else None,
        'shopped': shopped, 'estimate': est, 'p_ours': p_ours, 'p_market': p_fair,
        'fair_decimal_market': None if not p_fair else 1 / p_fair, 'fair_decimal_ours': None if not p_ours else 1 / p_ours,
        'stakes': None, 'ev_ours': None, 'house_edge': None, 'break_even': None, 'vig_per_leg': None}
    use = best_dec or (est['decimal'] if est else None)
    if use:
        report['stakes'] = {'win_100_needs': 100 / (use - 1), 'ten': payout(use, 10), 'hundred': payout(use, 100), 'decimal': use,
                            'estimated': best_dec is None}
        report['break_even'] = 1 / use
        if p_ours:
            report['ev_ours'] = p_ours * use - 1
    if best_dec and p_fair:
        report['house_edge'] = 1 - p_fair * best_dec  # what the book keeps on average at market-fair chances
        report['vig_per_leg'] = 1 - (p_fair * best_dec) ** (1 / n)
    return report

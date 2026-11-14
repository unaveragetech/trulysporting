"""Leg reliability, strategy presets and "what if I drop a leg" maths for the parlay generator.

Reliability is a transparent 5-95 heuristic of how much to trust a leg's chance, NOT a probability.  It rewards independent
agreement (a market price, several books, model and market saying the same thing, a long player history) and penalises thin
or one-sided evidence (model only, a questionable player, a short sample, a game far away where news can still change things).
"""
from typing import Any, Dict, List, Optional, Tuple

import pandas as pd

BOOK_KINDS = ('sportsbook', 'espn')


def _src_p(l: Any, kind: str) -> List[float]:
    return [s.p for s in l.sources if s.kind == kind and s.p is not None]


def reliability(l: Any, now: Optional[pd.Timestamp] = None) -> Dict[str, Any]:
    """Score one leg. Returns {'score', 'label', 'reasons': [(+/-points, text)]}."""
    now = now or pd.Timestamp.now(tz='UTC')
    score, why = 50.0, []

    def add(pts: float, text: str) -> None:
        nonlocal score
        score += pts
        why.append((pts, text))

    mkt = _src_p(l, 'market')
    mod = _src_p(l, 'model') + _src_p(l, 'engine')
    books = {q['source'] for q in l.quotes if q.get('kind') in BOOK_KINDS and q.get('exact', True)}
    if l.kind == 'player':
        n = int(l.info.get('games_used') or 0)
        if n >= 15:
            add(12, f'{n} recent games of history')
        elif n >= 10:
            add(6, f'{n} recent games of history')
        else:
            add(-6, f'only {n} recent games of history')
        hits = l.info.get('hits')
        if n and hits is not None:
            rate = hits / n
            if abs(rate - l.p) <= 0.12:
                add(6, f'history ({rate:.0%}) agrees with the estimate')
            else:
                add(-6, f'history ({rate:.0%}) differs from the estimate')
        if l.info.get('listed_questionable'):
            add(-20, 'player is listed questionable')
        add(-8, 'no sportsbook price to cross-check it')
        sd, mu = l.info.get('std_dev'), l.info.get('average')
        if sd and mu and sd / max(mu, 0.5) > 0.6:
            add(-5, 'very variable game to game')
    else:
        if mkt:
            add(20, 'a market price backs it')
            if len(mkt) >= 2:
                add(5, 'two independent markets agree on the base price')
        else:
            add(-15, 'no market price: model only')
        if mkt and mod:
            gap = abs(sum(mkt) / len(mkt) - sum(mod) / len(mod))
            if gap <= 0.05:
                add(10, 'model and market agree')
            elif gap >= 0.15:
                add(-10, f'model and market disagree by {gap:.0%}')
        if len(books) >= 3:
            add(10, f'{len(books)} sportsbooks price it')
        elif books:
            add(5, f'{len(books)} sportsbook prices it')
        inj = len(l.info.get('injuries_home', [])) + len(l.info.get('injuries_away', []))
        if inj >= 3:
            add(-5, f'{inj} injuries listed in this game')
        if l.kind == 'ml' and l.p >= 0.93:
            add(-3, 'near-certain favourites still lose sometimes')
    t = pd.to_datetime(l.start, utc=True, errors='coerce')
    if not pd.isna(t) and (t - now).total_seconds() > 36 * 3600:
        add(-5, 'game is 36+ hours away: lines and injury news can still move')
    score = max(5.0, min(95.0, score))
    return {'score': score, 'label': 'High' if score >= 75 else 'Medium' if score >= 55 else 'Low', 'reasons': why}


def leg_score(l: Any) -> float:
    """reliability(l)['score'], remembered on the leg (the search scores the same legs thousands of times)."""
    sig = (len(l.quotes), len(l.sources), l.p, bool(l.info))
    hit = getattr(l, '_rel_cache', None)
    if hit and hit[0] == sig:
        return hit[1]
    v = reliability(l)['score']
    try:
        l._rel_cache = (sig, v)
    except Exception:
        pass
    return v


def parlay_reliability(legs: List[Any]) -> float:
    """Half the average leg score, half the weakest leg's: a chain is only as good as its weakest link."""
    sc = [leg_score(l) for l in legs]
    return 0.0 if not sc else 0.5 * sum(sc) / len(sc) + 0.5 * min(sc)


def label_for(score: float) -> str:
    return 'High' if score >= 75 else 'Medium' if score >= 55 else 'Low'


def leg_odds(l: Any) -> Dict[str, Any]:
    """The numbers a bettor scans for one leg: our fair odds, the best price and book, and the edge."""
    import parlay_pricing as PP
    best = None
    for q in l.quotes:
        if q.get('kind') in BOOK_KINDS and q.get('exact', True) and (best is None or q['decimal'] > best['decimal']):
            best = q
    fair = PP.to_american(1 / l.p) if l.p else None
    return {'fair': fair, 'best_price': None if best is None else PP.to_american(best['decimal']),
            'best_book': None if best is None else best['source'], 'n_books': len({q['source'] for q in l.quotes
                                                                                      if q.get('kind') in BOOK_KINDS and q.get('exact', True)})}


def drop_one(legs: List[Any]) -> List[Dict[str, Any]]:
    """What the parlay looks like without each leg: chance, fair odds, estimated payout and reliability."""
    import parlay_pricing as PP
    out = []
    if len(legs) < 3:
        return out
    base_p = 1.0
    for l in legs:
        base_p *= l.p
    for i, l in enumerate(legs):
        rest = legs[:i] + legs[i + 1:]
        p = base_p / l.p
        rep = PP.price_report(rest, p)
        dec = (rep['best_book'] or rep['estimate'] or {}).get('decimal')
        out.append({'leg': l.pick, 'chance': p, 'gain': p - base_p, 'fair': PP.to_american(1 / p), 'decimal': dec,
                    'estimated': rep['best_book'] is None, 'reliability': parlay_reliability(rest)})
    return out


def weakest(legs: List[Any]) -> Optional[Any]:
    return min(legs, key=lambda l: l.p) if legs else None


# Strategy presets: every knob the generator exposes, so a user can start from one and tune it.
PRESETS: Dict[str, Dict[str, Any]] = {
    '🔒 Lock stack': dict(desc='Stack many very likely legs. Small payout, best chance of cashing.', k=(5, 9), min_p=0.80, rank='likely',
                          pmin=0.0, pmax=1.0, min_rel=0, priced=False, per_game=3, max_pl=3),
    '⚖️ Balanced': dict(desc='Likely legs you can trust: chance weighted by reliability.', k=(4, 6), min_p=0.70, rank='balanced',
                       pmin=0.0, pmax=1.0, min_rel=50, priced=False, per_game=3, max_pl=1),
    '🛡 Most reliable': dict(desc='Only legs with market backing and agreeing sources.', k=(3, 6), min_p=0.65, rank='reliable',
                            pmin=0.0, pmax=1.0, min_rel=65, priced=True, per_game=3, max_pl=0),
    '💎 Value hunter': dict(desc='Legs where we beat the sportsbook price, ranked by edge.', k=(3, 6), min_p=0.55, rank='value',
                           pmin=0.0, pmax=1.0, min_rel=45, priced=True, per_game=4, max_pl=0),
    '🎯 Longshot': dict(desc='Fewer sure things, bigger payout: parlay chance 8-35%.', k=(4, 8), min_p=0.55, rank='balanced',
                       pmin=0.08, pmax=0.35, min_rel=40, priced=False, per_game=4, max_pl=2),
    '🧱 Custom': dict(desc='Set every control yourself.'),
}
DEFAULT_PRESET = '⚖️ Balanced'

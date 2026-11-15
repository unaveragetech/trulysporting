"""Turn a checked parlay into links that put it on a sportsbook's betslip, plus a plain ticket to copy.

What we can and cannot do (see docs): no sportsbook publishes a documented "add these N legs" link.
  * DraftKings: its site reads a selection id list from ``?outcomes=`` (several joined with ``+``).  The ids come from the
    betslip links ESPN embeds for DraftKings' own lines, so they are exactly the markets we priced.  This is an unofficial
    behaviour, so the page always says to confirm every leg is on the slip.
  * Every other book: Unabated's own ``deepLink`` for each leg, used unchanged except for our partner tag (their rules: the path is
    never edited, and we never merge several into one link).  Each opens that one selection at the book.
  * Player milestones have no price feed, so no link can exist; they are listed to add by hand.
"""
from typing import Any, Dict, List, Optional

import parlay_pricing as PP

DK_BASE = 'https://sportsbook.draftkings.com/'
BOOK_KINDS = ('sportsbook', 'espn')


def dk_slip_url(sids: List[str]) -> Optional[str]:
    """One DraftKings link that loads every selection, or None if any id is missing."""
    if not sids or any(not s for s in sids):
        return None
    return DK_BASE + '?outcomes=' + '+'.join(sids)


def _leg_quote(l: Any, book: str) -> Optional[Dict]:
    """The exact quote for this leg at this book, preferring the one that carries a link."""
    qs = [q for q in l.quotes if q['source'] == book and q.get('kind') in BOOK_KINDS and q.get('exact', True)]
    if not qs:
        return None
    return max(qs, key=lambda q: (bool(q.get('link')), q['via'] == 'Unabated', q['decimal']))


def _sid(l: Any, book: str) -> Optional[str]:
    for q in l.quotes:
        if q['source'] == book and q.get('exact', True) and q.get('sid'):
            return q['sid']
    return None


def ticket_text(legs: List[Any], book: Optional[str], american: Optional[int], stake: float, decimal: Optional[float],
                manual: List[str]) -> str:
    lines = [f"{len(legs) + len(manual)}-leg parlay" + (f" at {book} ({american:+d})" if book and american else '')]
    for i, l in enumerate(legs, 1):
        q = _leg_quote(l, book) if book else None
        px = '' if not q else f" ({PP.to_american(q['decimal']):+d})"
        line = '' if not q or q.get('line') is None or l.kind == 'ml' else f" [{q['line']:+g}]"
        lines.append(f"{i}. {l.pick}{line}{px}  |  {l.matchup}")
    for m in manual:
        lines.append(f"+  {m}  (player prop: add by hand)")
    if decimal:
        ret, prof = PP.payout(decimal, stake)
        lines.append(f"Stake ${stake:,.2f} -> returns ${ret:,.2f} (profit ${prof:,.2f})")
    return '\n'.join(lines)


def build(legs: List[Any], res: Dict[str, Any], stake: float = 10.0) -> Dict[str, Any]:
    """Betslip plan from a venue check (``parlay_venues.evaluate`` output) on the same, freshly priced legs."""
    verifiable = [l for l in legs if l.kind in ('ml', 'spread', 'total')]
    manual = [l.pick for l in legs if l.kind not in ('ml', 'spread', 'total')]
    books = []
    for v in res.get('venues', []):
        if v['type'] != 'sportsbook' or v['status'] == 'no' or not v.get('decimal'):
            continue
        name = v['name']
        rows, sids = [], []
        for l in verifiable:
            q = _leg_quote(l, name)
            sid = _sid(l, name)
            sids.append(sid)
            rows.append({'pick': l.pick, 'game': l.matchup, 'price': None if not q else PP.to_american(q['decimal']),
                         'link': (q or {}).get('link'), 'sid': sid, 'line': (q or {}).get('line')})
        combined = dk_slip_url(sids) if name == 'DraftKings' else None
        books.append({'name': name, 'status': v['status'], 'decimal': v['decimal'], 'american': v['american'],
                      'combined': combined, 'legs': rows, 'linked': sum(1 for r in rows if r['link']),
                      'ticket': ticket_text(verifiable, name, v['american'], stake, v['decimal'], manual)})
    best = res.get('best')
    return {'ok': bool(books), 'best': best['name'] if best else None, 'books': books, 'manual': manual, 'stake': stake,
            'n': len(legs), 'general': res.get('general', []), 'closed': res.get('closed', [])}


def primary_action(plan: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """The one thing to click first: the best book's combined link if it exists, else None (use the per-leg links)."""
    for b in plan['books']:
        if b['name'] == plan['best']:
            return {'book': b['name'], 'url': b['combined'], 'all_legs': b['combined'] is not None}
    return None

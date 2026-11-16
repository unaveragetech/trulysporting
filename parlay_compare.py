"""Every place that sells each leg, side by side, and which places can take the whole parlay.

``matrix`` is pure data (tested); ``render`` draws it.  A book counts toward a parlay only when it quotes EVERY leg at the exact
line, fresh and sane (the checks in parlay_venues).  Everything a book quotes is still shown, including other lines and
exchanges, so nothing is hidden: you can see exactly why a book is in or out.
"""
from typing import Any, Dict, List, Optional

import pandas as pd
import streamlit as st

import parlay_pricing as PP

KINDS = ('sportsbook', 'espn', 'exchange')


def _best_quote(l: Any, book: str) -> Optional[Dict]:
    qs = [q for q in l.quotes if q['source'] == book and q.get('kind') in KINDS]
    if not qs:
        return None
    return max(qs, key=lambda q: (q.get('exact', True), bool(q.get('link')), q['via'] == 'Unabated', q['decimal']))


def matrix(legs: List[Any], venues: Optional[List[Dict]] = None) -> Dict[str, Any]:
    """Per leg and per book: the price, line, link and whether it is the exact bet; plus each book's coverage of the whole parlay."""
    verifiable = [l for l in legs if l.kind in ('ml', 'spread', 'total')]
    exch = set(PP.EXCHANGES.values())
    books = sorted({q['source'] for l in verifiable for q in l.quotes if q.get('kind') in KINDS},
                   key=lambda b: (b in exch, -sum(1 for l in verifiable if _best_quote(l, b)), b))
    n = len(verifiable)
    rows = []
    for l in verifiable:
        cells: Dict[str, Dict] = {}
        for b in books:
            q = _best_quote(l, b)
            if q:
                cells[b] = {'price': PP.to_american(q['decimal']), 'decimal': q['decimal'], 'line': q.get('line'), 'exact': q.get('exact', True),
                            'link': q.get('link'), 'via': q['via'], 'ts': q.get('ts'), 'note': q.get('note', ''), 'kind': q['kind']}
        ex = [c['decimal'] for c in cells.values() if c['exact']]
        top = max(ex) if ex else None
        for c in cells.values():
            c['best'] = bool(c['exact'] and top and abs(c['decimal'] - top) < 1e-9 and len(ex) > 1)
        rows.append({'leg': l, 'pick': l.pick, 'game': l.matchup, 'cells': cells, 'n_exact': len(ex)})
    vmap = {v['name']: v for v in (venues or [])}
    totals = {}
    for b in books:
        have = sum(1 for r in rows if b in r['cells'] and r['cells'][b]['exact'])
        v = vmap.get(b)
        dec = 1.0
        for r in rows:
            c = r['cells'].get(b)
            if c and c['exact']:
                dec *= c['decimal']
        full = have == n and n > 0
        totals[b] = {'covered': have, 'n': n, 'full': full, 'decimal': dec if full else None, 'american': PP.to_american(dec) if full else None,
                     'status': v['status'] if v else ('exchange' if b in exch else 'no'),
                     'type': 'exchange' if b in exch else 'sportsbook',
                     'missing': [r['pick'] for r in rows if not (b in r['cells'] and r['cells'][b]['exact'])]}
    return {'books': books, 'rows': rows, 'totals': totals, 'n': n}


def _cell_text(c: Optional[Dict]) -> str:
    if not c:
        return '—'
    t = f"{c['price']:+d}" if c['price'] is not None else '?'
    if c['line'] is not None:
        t += f" @ {c['line']:+g}"
    if not c['exact']:
        t += ' (other line)'
    return ('★ ' if c.get('best') else '') + t


def _age(ts: Optional[str]) -> str:
    t = pd.to_datetime(ts, utc=True, errors='coerce') if ts else pd.NaT
    if pd.isna(t):
        return ''
    m = (pd.Timestamp.now(tz='UTC') - t).total_seconds() / 60
    return 'just now' if m < 1 else f'{m:.0f} min ago'


def leg_header(l: Any) -> None:
    """Photo (player) or both team logos (game) next to the pick, with the chance."""
    info = l.info or {}
    c1, c2 = st.columns([1, 6])
    if l.kind == 'player' and info.get('headshot'):
        c1.image(info['headshot'], width=64)
    else:
        for u in (info.get('away_logo'), info.get('home_logo')):
            if u:
                c1.image(u, width=34)
    c2.markdown(f"**{l.pick}** · {l.matchup} · chance {l.p:.0%}")


def render(res: Dict[str, Any]) -> None:
    legs = res.get('legs') or []
    if not legs:
        return
    m = matrix(legs, res.get('venues'))
    if not m['books']:
        st.warning('No book or exchange returned a price for these games. They may not have odds posted yet; check again closer to the start.')
        return
    st.markdown('### 🏦 Every place, side by side')
    st.caption(f"Checked {_age(res.get('checked')) or 'now'} from live ESPN and Unabated boards, shared across all visitors. A book can take the "
               f"whole parlay only if it quotes all {m['n']} legs at the exact line.")
    t_ = m['totals']
    book_rows = []
    for b in sorted(m['books'], key=lambda b: (t_[b]['type'] == 'exchange', -t_[b]['covered'], -(t_[b]['decimal'] or 0))):
        t = t_[b]
        if t['type'] == 'exchange':
            verdict = 'Single bets only (not a parlay)'
        elif t['full']:
            verdict = {'ok': '✅ All legs, placeable', 'caution': '⚠️ All legs, verify at the book'}.get(t['status'], '❌ All legs quoted but failed a check')
        else:
            verdict = f"❌ Missing: {', '.join(t['missing'][:3])}" + ('…' if len(t['missing']) > 3 else '')
        book_rows.append({'Book': b, 'Legs quoted': f"{t['covered']} of {t['n']}",
                          'Parlay price': '—' if not t['american'] else f"{t['american']:+d}", 'Verdict': verdict})
    st.dataframe(pd.DataFrame(book_rows), hide_index=True, use_container_width=True)
    st.markdown('**Leg by leg** (★ = best price for that leg)')
    grid = [{'Leg': r['pick'], **{b: _cell_text(r['cells'].get(b)) for b in m['books']}} for r in m['rows']]
    st.dataframe(pd.DataFrame(grid), hide_index=True, use_container_width=True)
    for r in m['rows']:
        got = list(r['cells'].items())
        with st.expander(f"{r['pick']}: {sum(1 for _, c in got if c['exact'])} places"):
            leg_header(r['leg'])
            for b, c in sorted(got, key=lambda t: -t[1]['decimal']):
                a, bcol = st.columns([3, 2])
                tag = '' if c['exact'] else ' (a different line, not this bet)'
                a.markdown(f"**{b}** {_cell_text(c)}{tag} · {c['via']} {_age(c['ts'])}")
                if c['link'] and c['exact']:
                    bcol.link_button(f'Open at {b} ↗', c['link'], use_container_width=True)
                elif c['exact']:
                    bcol.caption('no direct link: search it at the book')

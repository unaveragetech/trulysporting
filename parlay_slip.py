"""UI: open a parlay at a sportsbook with the legs filled in, or copy it as a ticket."""
from typing import Any, Dict, List

import streamlit as st

import betslip as B
import parlay_compare as CMP
import parlay_detail as D
import parlay_pricing as PP
import parlay_venues as V

STATUS = {'ok': '✅ Placeable', 'caution': '⚠️ Verify at the book', 'no': '❌ Not placeable'}


def _links(book: Dict[str, Any]) -> None:
    rows = [r for r in book['legs']]
    for i, r in enumerate(rows, 1):
        px = '' if r['price'] is None else f" ({r['price']:+d})"
        if r['link']:
            st.link_button(f"Leg {i}: {r['pick']}{px} ↗", r['link'], use_container_width=True)
        else:
            st.markdown(f"- Leg {i}: **{r['pick']}**{px}: no link for this leg, search it at {book['name']}")


def render_slip(res: Dict[str, Any], key: str) -> None:
    plan = res.get('slip')
    if res.get('error') or not plan:
        st.error(f"Could not check sportsbooks right now ({res.get('error') or 'no data'}). Try again in a minute.")
        return
    if not plan['ok']:
        st.error('No sportsbook can be confirmed for this parlay right now, so there is nothing safe to open.'
                 + (' Closed legs: ' + ', '.join(plan['closed']) + '.' if plan['closed'] else ''))
        CMP.render(res)
        for v in res.get('venues', []):
            bad = [t for s, t in v['reasons'] if s == 'fail']
            if bad and v['type'] == 'sportsbook':
                st.markdown(f"**{v['name']}**\n\n" + '\n'.join(f'- ❌ {t}' for t in bad[:4]))
        return
    best = next(b for b in plan['books'] if b['name'] == plan['best']) if plan['best'] else plan['books'][0]
    ret, prof = PP.payout(best['decimal'], plan['stake'])
    st.markdown(f"**Best book: {best['name']} {best['american']:+d}** · {STATUS[best['status']]} · "
                f"\\${plan['stake']:,.2f} pays {D.mdm(ret)} (profit {D.mdm(prof)})")
    if best['combined']:
        st.link_button(f"🎟 Open {best['name']} with all {len(best['legs'])} legs on the slip ↗", best['combined'], type='primary',
                       use_container_width=True)
        st.caption(f"{best['name']} loads every leg from one link. This is an unofficial {best['name']} feature, so after it opens, "
                   f"check that all {len(best['legs'])} legs are on the slip and that each price matches before you place the bet.")
    else:
        st.markdown(f"{best['name']} has no one-click link for the whole parlay, so open each leg below. Each button adds that one selection "
                    f"at {best['name']}; add all {len(best['legs'])} and the slip becomes your parlay.")
        _links(best)
    if plan['manual']:
        st.warning('Add these by hand (no sportsbook price feed, so no link): ' + '; '.join(plan['manual']))
    st.markdown('**Copy this ticket** (use it to check the slip or to type the bet in)')
    st.code(best['ticket'], language=None)
    others = [b for b in plan['books'] if b is not best]
    if others:
        with st.expander(f'Other places that can take it ({len(others)})'):
            for b in others:
                ret2, _ = PP.payout(b['decimal'], plan['stake'])
                st.markdown(f"**{b['name']} {b['american']:+d}** · {STATUS[b['status']]} · \\${plan['stake']:,.2f} pays {D.mdm(ret2)}")
                if b['combined']:
                    st.link_button(f"🎟 Open {b['name']} with all legs ↗", b['combined'])
                else:
                    _links(b)
    CMP.render(res)
    for s, t in plan['general']:
        st.caption(('❌ ' if s == 'fail' else '⚠️ ') + t)
    st.caption('Links open the sportsbook in a new tab. TrulySporting never places a bet or sees your account: you review and confirm at the book. '
               'Sportsbook links from Unabated carry our partner tag, which may earn the site a commission at no cost to you. '
               'Prices move and books can reject or reprice a ticket. Must be 18+ (21+ in most states) and in a state where the book operates. '
               'Bet only what you can afford to lose; US help line 1-800-GAMBLER.')


def slip_dialog(legs: List[Any], key: str) -> None:
    """Dialog: live re-price, validate, then show the links. Opened from a parlay card."""
    @st.dialog('🎟 Open at a sportsbook', width='large')
    def _show():
        stake = st.number_input('Stake (\\$)', 1.0, 10000.0, 10.0, 1.0, key=f'slip_stake_{key}')
        with st.spinner('Checking live prices and lines…'):
            res = V.check_legs(legs, key, stake=float(stake))
        render_slip(res, key)
    _show()

"""Everything we know about a parlay, laid out for the user: price and cost, every source, every leg's facts."""
from typing import Any, Dict, List, Optional

import pandas as pd
import streamlit as st

import parlay_pricing as PP
import parlays as P

KIND_BADGE = {'model': '📐', 'market': '💰', 'live': '🔴', 'player': '👤', 'engine': '🏈'}
KIND_LABEL = {'sportsbook': 'Sportsbook', 'espn': 'Sportsbook (via ESPN)', 'exchange': 'Exchange / prediction market'}


def am(decimal: Optional[float]) -> str:
    a = PP.to_american(decimal) if decimal else None
    return '—' if a is None else f'{a:+d}'


def money(x: float) -> str:
    return f'${x:,.2f}'


def mdm(x: float) -> str:
    """money() for markdown text: a bare $ pair would be read as math."""
    return money(x).replace('$', '\\$')


def price_line(rep: Dict) -> str:
    """One line for a parlay card: the best price we can find and what it pays."""
    bb = rep.get('best_book')
    if bb:
        ret, prof = PP.payout(bb['decimal'], 10)
        s = f"💵 **{bb['book']} {am(bb['decimal'])}**: \\$10 pays {mdm(ret)} (profit {mdm(prof)})"
        if rep.get('house_edge') is not None:
            s += f" · fair price {am(rep['fair_decimal_market'])} · the book keeps about {rep['house_edge']:.0%}"
        if rep.get('shopped') and rep['shopped']['decimal'] > bb['decimal'] * 1.005:
            s += f" · line-shopping ceiling {am(rep['shopped']['decimal'])}"
        return s
    est = rep.get('estimate')
    if est:
        ret, prof = PP.payout(est['decimal'], 10)
        return (f"💵 **Estimated ~{am(est['decimal'])}**: \\$10 would pay about {mdm(ret)}. {rep['n_priced']} of {rep['n']} legs have "
                f"real sportsbook prices; the rest are estimated with a standard margin.")
    return '💵 No sportsbook prices found for these legs yet.'


def _quotes_table(quotes: List[Dict], best: Optional[Dict]) -> pd.DataFrame:
    rows = []
    bd = best['decimal'] if best else None
    for q in quotes:
        diff = '' if bd is None or q['kind'] == 'exchange' else ('best' if abs(q['decimal'] - bd) < 1e-9 else f"{100 * (q['decimal'] / bd - 1):+.1f}%")
        rows.append({'Source': q['source'], 'Type': KIND_LABEL.get(q['kind'], q['kind']), 'Price': f"{q['price']:+.0f}",
                     'Line': '—' if q.get('line') is None else f"{q['line']:+g}", 'vs best book': diff,
                     'Data from': q['via'], 'Updated': (q.get('ts') or '')[11:19] + ' UTC' if q.get('ts') else 'at last refresh',
                     'Open': q.get('link')})
    return pd.DataFrame(rows)


def _facts_table(d: Dict) -> pd.DataFrame:
    return pd.DataFrame([{'Item': k, 'Value': '—' if v in (None, '') else v} for k, v in d.items()])


def render_leg_details(l: P.Leg, tz) -> None:
    """Sources, every price, and the game / team / player facts behind one leg."""
    st.markdown('**Where the chance comes from**')
    st.dataframe(pd.DataFrame([{'Source': f"{KIND_BADGE.get(s.kind, '•')} {s.name}", 'Chance': '—' if s.p is None else f'{s.p:.0%}',
                                'What it says': s.detail} for s in l.sources]), hide_index=True, use_container_width=True)
    for n in l.notes:
        st.caption(n)
    exact = [q for q in l.quotes if q.get('exact', True)]
    if exact:
        rep = PP.price_report([l])
        st.markdown('**Prices for exactly this bet**')
        st.dataframe(_quotes_table(rep['legs'][0]['quotes'], rep['legs'][0]['best']), hide_index=True, use_container_width=True,
                     column_config={'Open': st.column_config.LinkColumn('Open', display_text='Open ↗')})
        fp = rep['legs'][0]['p_fair_market']
        if fp is not None:
            st.caption(f"Market-fair chance (margin removed, averaged over books quoting both sides): **{fp:.1%}**. "
                       f"Our chance: **{l.p:.1%}**.")
    near = [q for q in l.quotes if not q.get('exact', True)]
    if near:
        with st.expander('Same market, different line (not the same bet)'):
            st.dataframe(_quotes_table(near, None), hide_index=True, use_container_width=True)
    elif not exact and l.kind == 'player':
        st.caption('Player milestone prices are not in our data. Sportsbooks sell these as alternate player props; check the price '
                   'there. Any payout shown for this leg is an estimate.')
    info = l.info or {}
    if l.kind == 'player':
        st.markdown('**Player history behind the number**')
        st.dataframe(_facts_table({
            'Player / team': f"{info.get('player')} ({info.get('team')})", 'Stat needed': f"{info.get('stat')} ≥ {info.get('threshold', 0):g}",
            'Games used': f"{info.get('games_used')} of the team's last {info.get('team_games')}",
            'Hit it in': f"{info.get('hits')} of {info.get('games_used')} games", 'Average / std dev':
            f"{info.get('average', 0):.1f} / {info.get('std_dev', 0):.1f}", 'Opponent adjustment': f"x{info.get('opponent_factor', 1):.2f}",
            'Expected this game': f"{info.get('expected', 0):.1f}",
            'Allowance for not playing a full role': f"{100 * info.get('availability_allowance', 0):.0f}%",
            'Listed questionable': 'yes (chance cut 20%)' if info.get('listed_questionable') else 'no'}),
            hide_index=True, use_container_width=True)
        vals = info.get('recent_values') or []
        if vals:
            st.caption('Recent games (oldest to newest left to right): ' + ', '.join(f'{v:g}' for v in vals[::-1]))
        game = info.get('game') or {}
    else:
        game = info
    if game:
        st.markdown('**Game facts**')
        lines = game.get('lines') or {}
        st.dataframe(_facts_table({
            'Game': game.get('matchup'), 'Starts': pd.to_datetime(game.get('start'), utc=True, errors='coerce').tz_convert(tz).strftime('%a %b %d, %I:%M %p')
            if game.get('start') else None, 'TV': game.get('tv'), 'ESPN book': game.get('espn_book'),
            'Spread (home)': lines.get('spread (home)'), 'Total': lines.get('total'), 'Moneyline (home / away)':
            f"{lines.get('home moneyline')} / {lines.get('away moneyline')}", 'Kalshi home win': game.get('kalshi_home_win'),
            'NFL engine home win': game.get('engine_home_win'), 'Weight on our model vs the market': game.get('model_weight_vs_market')}),
            hide_index=True, use_container_width=True)
        model = game.get('model')
        if model:
            st.caption('Team-form model: ' + ', '.join(f'{k.replace("_", " ")} {v:g}' for k, v in model.items()))
        fh, fa = game.get('form_home') or {}, game.get('form_away') or {}
        if fh or fa:
            c1, c2 = st.columns(2)
            for col, nm, f in ((c1, 'Home team form', fh), (c2, 'Away team form', fa)):
                col.markdown(f'*{nm}*')
                col.dataframe(_facts_table({'Games': f.get('n'), 'Record': f"{f.get('wins')}-{f.get('losses')}" if f else None,
                                            'Points for / against': f"{f.get('pf')} / {f.get('pa')}" if f else None,
                                            'Margin (season / last 5)': f"{f.get('margin')} / {f.get('last5')}" if f else None,
                                            'Rating': f.get('rating'), 'Last 5': f.get('streak')}), hide_index=True, use_container_width=True)
        for side, nm in (('injuries_home', 'Home'), ('injuries_away', 'Away')):
            inj = game.get(side) or []
            if inj:
                st.caption(f'{nm} injury report: ' + ', '.join(f"{x.get('name')} ({x.get('status')})" for x in inj))


def render_pricing(rep: Dict, built_at: str = '') -> None:
    """The cost of the parlay: placeable books, line-shopping ceiling, fair price, margin and expected value."""
    st.markdown('### 💵 What it costs and pays')
    c1, c2, c3, c4 = st.columns(4)
    bb = rep.get('best_book')
    est = rep.get('estimate')
    use = bb['decimal'] if bb else (est['decimal'] if est else None)
    c1.metric('Best price you can place' if bb else 'Estimated price', am(use) if use else '—',
              bb['book'] if bb else ('estimate' if est else 'no prices'))
    c2.metric('Fair price (no margin)', am(rep['fair_decimal_market']) if rep.get('fair_decimal_market') else '—', 'from market prices')
    c3.metric('Our fair price', am(rep['fair_decimal_ours']) if rep.get('fair_decimal_ours') else '—', f"{rep['p_ours']:.1%} chance" if rep.get('p_ours') else '')
    c4.metric('Break-even chance', f"{rep['break_even']:.1%}" if rep.get('break_even') else '—', 'needed to profit')
    if rep.get('stakes'):
        s = rep['stakes']
        ret10, prof10 = s['ten']
        ret100, prof100 = s['hundred']
        tag = ' (estimated)' if s['estimated'] else ''
        st.markdown(f"- **\\$10 stake{tag}** returns {mdm(ret10)} (profit {mdm(prof10)}); **\\$100** returns {mdm(ret100)} (profit {mdm(prof100)}).\n"
                    f"- To win **\\$100 profit{tag}** you stake {mdm(s['win_100_needs'])}.")
    if rep.get('house_edge') is not None:
        st.markdown(f"- **Cost of the margin:** if every leg is priced fairly by the market, the book keeps about **{rep['house_edge']:.1%}** of "
                    f"each dollar on this ticket (about {rep['vig_per_leg']:.1%} per leg, compounding with each leg).")
    if rep.get('ev_ours') is not None:
        sign = 'above' if rep['ev_ours'] > 0 else 'below'
        st.markdown(f"- **If our chance is right:** expected value is **{rep['ev_ours']:+.1%}** per dollar. That is {sign} break-even; "
                    "treat it as a guide, not a promise, since our chance is an estimate.")
    if bb is None and est:
        st.warning(f"{rep['n_priced']} of {rep['n']} legs have real sportsbook prices. Unpriced: {', '.join(est['unpriced'])}. "
                   'The payout above uses a standard 4.5% margin per unpriced leg and is an estimate, not a quote.')
    elif bb is None:
        st.warning('No sportsbook quotes were found for these legs.')
    if rep.get('books'):
        st.markdown('**Where this exact parlay is priced** (a book must offer every leg at the same line)')
        st.dataframe(pd.DataFrame([{'Book': b['book'], 'Parlay price': am(b['decimal']), 'Multiplier': f"{b['decimal']:.2f}x",
                                    '$10 pays': money(10 * b['decimal']), '$100 pays': money(100 * b['decimal']),
                                    'vs best': 'best' if i == 0 else f"{100 * (b['decimal'] / rep['books'][0]['decimal'] - 1):+.1f}%",
                                    'Data from': ' + '.join(b['via'])} for i, b in enumerate(rep['books'])]),
                     hide_index=True, use_container_width=True)
        if rep.get('shopped') and rep['shopped']['decimal'] > rep['books'][0]['decimal'] * 1.005:
            st.caption(f"Taking the best price for each leg from different books would pay {am(rep['shopped']['decimal'])} "
                       f"({rep['shopped']['decimal']:.2f}x), but most books only price a parlay inside one book, so that is a ceiling, "
                       'not a ticket you can place.')
    elif rep.get('all_priced'):
        st.caption('No single book prices every leg at these exact lines, so there is no one-book parlay price. Individual leg prices are below.')
    ex = [(x['pick'], q) for x in rep['legs'] for q in x['exchanges']]
    if ex:
        st.caption('Exchanges and prediction markets (Kalshi, Novig, Polymarket) price single events, not parlays, so they are shown '
                   'on each leg but excluded from the parlay price.')
    st.caption(f"Prices: ESPN's embedded book and Unabated's multi-book feed (delayed at least 15 seconds), checked {built_at or 'at the last refresh'}. "
               "Sportsbook links go through TrulySporting's Unabated partner code, which may earn the site a commission at no cost to you. "
               'Lines move and books can reject or reprice a ticket; always confirm the final price at the book.')


METHOD = [
    'A sportsbook parlay pays the product of its legs\' decimal prices, so each leg\'s margin compounds.',
    'Fair chance of a leg = its implied probability divided by both sides\' implied probabilities added together (margin removed). '
    'The fair parlay chance is the product of the legs\' fair chances.',
    'The placeable price is the best book that quotes every leg at the same line. Mixing books leg by leg is shown only as a ceiling.',
    'Exchange and prediction-market prices (Kalshi includes an estimated fee of about 0.07 × P × (1 − P) per \\$1 contract) are single-bet '
    'prices and never part of a parlay price.',
    'Legs without a sportsbook price (player milestones) are estimated from our chance with a standard 4.5% margin and labelled as estimates.',
    'Expected value compares our chance with the payout; our chance is an estimate from team results, markets and player history.']


def why_dialog(p: P.Parlay, rank: int, tz, built_at: str = '') -> None:
    @st.dialog(f'Parlay #{rank}: full breakdown' if rank else 'Your parlay: full breakdown', width='large')
    def _show():
        rep = PP.price_report(p.legs, p.p)
        ex = P.explain_parlay(p)
        st.markdown(f"### {p.k} legs · {p.p:.1%} chance to hit")
        st.markdown(f"**How the chance is built:** {ex['formula']}")
        render_pricing(rep, built_at)
        st.markdown('### 🧩 The legs')
        st.caption('Open a leg to see every source, every price we found, and the game, team and player facts behind it.')
        for i, l in enumerate(p.legs, 1):
            with st.expander(f"{i}. {l.pick} · {l.p:.0%} · {l.matchup} ({l.league})", expanded=False):
                render_leg_details(l, tz)
        st.markdown('### 🧮 How we picked and priced')
        st.markdown('From every game still to be played in a league that is running, each leg must clear the minimum chance you set. The search '
                    'keeps the combinations with the highest joint probability, uses at most one leg per game, and drops near-duplicates. '
                    'Legs for games that already started are removed.')
        for m in METHOD:
            st.markdown(f'- {m}')
        st.markdown('**Assumptions and limits**')
        for a in ex['assumptions']:
            if 'Live legs' not in a:
                st.markdown(f'- {a}')
        st.caption('Entertainment and analysis only, not betting advice. Must be 18+. If you wager, set limits. US help line: 1-800-GAMBLER.')
    _show()

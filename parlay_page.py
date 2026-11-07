"""Streamlit page for the parlay builder (logic lives in parlays.py)."""
import time
from typing import Any, Callable, Dict, Tuple

import pandas as pd
import streamlit as st

import parlays as P

_ESPN_TO_NFLVERSE = {'WSH': 'WAS', 'LAR': 'LA'}
_TYPE_LABELS = {'ml': 'Winner', 'spread': 'Spread', 'total': 'Game total', 'player': 'Player milestones'}
_KIND_BADGE = {'model': '📐', 'market': '💰', 'live': '🔴', 'player': '👤', 'engine': '🏈'}


def _engine_probs() -> Dict[Tuple[str, str], float]:
    """NFL engine home-win probabilities, only if the engine is already loaded (never forces a load)."""
    try:
        from nfl_engine.runtime import RT
        if RT.state != 'ready':
            return {}
        inv = {v: k for k, v in _ESPN_TO_NFLVERSE.items()}
        return {(inv.get(r.home, r.home), inv.get(r.away, r.away)): float(r.p_home) for r in RT.slate().itertuples()}
    except Exception:
        return {}


def _fair(p: float) -> str:
    a = P.prob_to_american(p)
    return f'{a:+d}' if a else '—'


def _legs_frame(pz: P.Parlay) -> pd.DataFrame:
    return pd.DataFrame([{
        'Leg': ('🔴 ' if l.live else '') + l.pick, 'Game': l.matchup, 'League': l.league,
        'Chance': f'{l.p:.0%}', 'Book price': '—' if l.price is None else f'{l.price:+.0f}',
        'Data': ' '.join(f"{_KIND_BADGE.get(s.kind, '•')} {s.name}" for s in l.sources)} for l in pz.legs])


def _why_dialog(p: P.Parlay, rank: int) -> None:
    @st.dialog(f'Why parlay #{rank}', width='large')
    def _show():
        ex = P.explain_parlay(p)
        st.markdown(f'### {p.k} legs · {p.p:.1%} chance')
        st.markdown(f"**How the number is built:** {ex['formula']}")
        st.markdown(f"**Fair price:** {ex['fair_odds']}")
        if ex['market']:
            st.markdown(f"**Sportsbook:** {ex['market']}")
        st.markdown('**Why these legs were chosen:** from every live and upcoming game we price, each leg must clear the '
                    'minimum chance you set; the search keeps the combinations with the highest joint probability, uses at most '
                    'one leg per game, and drops near-duplicates so you see real alternatives.')
        for l in p.legs:
            with st.expander(f"{'🔴 ' if l.live else ''}{l.pick} · {l.p:.0%} · {l.matchup} ({l.league})", expanded=False):
                st.dataframe(pd.DataFrame([{'Source': f"{_KIND_BADGE.get(s.kind, '•')} {s.name}",
                                            'Chance': '—' if s.p is None else f'{s.p:.0%}', 'What it says': s.detail}
                                           for s in l.sources]), hide_index=True, use_container_width=True)
                for n in l.notes:
                    st.caption(n)
        st.markdown('**Assumptions and limits**')
        for a in ex['assumptions']:
            st.markdown(f'- {a}')
        st.caption('Data: ESPN scoreboards and embedded lines, Kalshi game markets, team results and player box scores stored by '
                   'this app, and the NFL engine when loaded. Entertainment and analysis only; if you wager, set limits. '
                   'US help line: 1-800-GAMBLER.')
    _show()


def render_parlay_page(db: Any, worker: Any, season_for: Callable[[str], int], label: Callable[[str], str]) -> None:
    from live import fetch_all_games

    st.markdown('## 🎰 Parlay Lab')
    st.caption('The most likely multi-leg combinations from live and upcoming games across every league we can price. '
               'Every leg shows where its probability comes from; press **Why this parlay** for the full working. '
               'Estimates from public data, for entertainment and analysis, not betting advice. Must be 18+.')

    # what is on right now, so the defaults skip leagues with nothing to price
    try:
        board = fetch_all_games(tuple(P.MODEL_LEAGUES))
    except Exception:
        board = pd.DataFrame()
    live_n, soon = {}, {}
    if not board.empty:
        live_n = board[board['state'] == 'in'].groupby('ep').size().to_dict()
        start = pd.to_datetime(board['start'], utc=True, errors='coerce')
        up = board[(board['state'] == 'pre') & (start < pd.Timestamp.now(tz='UTC') + pd.Timedelta(hours=24))]
        soon = up.groupby('ep').size().to_dict()
    active = [e for e in P.MODEL_LEAGUES if live_n.get(e) or soon.get(e)]
    st.markdown(f"🔴 **{sum(live_n.values())}** live and 🕒 **{sum(soon.values())}** upcoming (next 24h) games across the "
                f"{len(P.MODEL_LEAGUES)} leagues we can price"
                + (f" · active now: {', '.join(label(e) for e in active)}" if active else ''))

    with st.expander('⚙️ Parlay settings', expanded=False):
        c1, c2, c3 = st.columns(3)
        kmin, kmax = c1.slider('Legs per parlay', 2, 10, (4, 7), key='pl_k')
        top = c2.slider('How many parlays', 3, 20, 10, key='pl_top')
        rank_lbl = c3.radio('Rank by', ['Most likely', 'Best value vs sportsbook'], key='pl_rank')
        eps = st.multiselect('Leagues', P.MODEL_LEAGUES, default=active or P.MODEL_LEAGUES[:1], format_func=label, key='pl_eps')
        d1, d2, d3, d4 = st.columns(4)
        hours = d1.slider('Upcoming within (hours)', 3, 72, 24, key='pl_hours')
        include_live = d2.toggle('Include live games', True, key='pl_live')
        min_p = d3.slider('Min chance per leg', 0.50, 0.95, 0.60, 0.01, key='pl_minp')
        max_pl = d4.slider('Max player legs per parlay', 0, 4, 2, key='pl_maxpl')
        types_lbl = st.multiselect('Leg types', list(_TYPE_LABELS.values()), default=list(_TYPE_LABELS.values()), key='pl_types')
        per_league = st.slider('Games per league to consider', 4, 25, 8, key='pl_perleague')
        req_mkt = st.toggle('Winner legs need a market price (recommended)', True, key='pl_reqmkt',
                            help='Games with no sportsbook or Kalshi price are skipped for winner legs, so the chance is never from team form alone.')
    types = tuple(k for k, v in _TYPE_LABELS.items() if v in types_lbl)
    rank = 'value' if rank_lbl.startswith('Best value') else 'likely'
    if not eps or not types:
        st.info('Pick at least one league and one leg type.')
        return

    sig = (kmin, kmax, top, rank, tuple(sorted(eps)), hours, include_live, round(min_p, 2), max_pl, types, per_league, req_mkt)
    rebuild = st.button('🔄 Rebuild with latest data', key='pl_rebuild')
    built = st.session_state.get('pl_built')
    if rebuild or not built or built['sig'] != sig:
        if rebuild:
            P._CACHE.clear()
        with st.status('Building parlays…', expanded=True) as status:
            legs, info = P.collect_legs(db, worker, season_for, label, list(eps), hours, include_live, per_league, types,
                                        _engine_probs(), progress=lambda m: status.write(m), require_market=req_mkt)
            pz = P.build_parlays(legs, kmin, kmax, top, min_p, max_pl, rank)
            games = sum(v['games'] for v in info['leagues'].values())
            status.update(label=f'{len(legs)} candidate legs from {games} games, {len(pz)} parlays', state='complete', expanded=False)
        built = st.session_state['pl_built'] = {'sig': sig, 'parlays': pz, 'info': info, 'legs': len(legs),
                                                'at': time.strftime('%H:%M:%S')}
    pz, info = built['parlays'], built['info']

    if not pz:
        st.warning('Not enough legs clear the filters. Try lowering the minimum chance, adding leagues, widening the time '
                   'window or reducing the leg count. Off-season leagues have nothing to price.')
    for i, p in enumerate(pz, 1):
        with st.container(border=True):
            mk = '' if p.market_decimal is None else f' · sportsbook pays ~{p.market_decimal:.1f}x (edge {p.ev:+.0%})'
            st.markdown(f'**#{i} · {p.k}-leg parlay** · hit chance **{p.p:.1%}** · fair odds {_fair(p.p)}{mk}')
            st.dataframe(_legs_frame(p), hide_index=True, use_container_width=True)
            if st.button('🔍 Why this parlay', key=f'pl_why_{i}'):
                _why_dialog(p, i)
    if pz:
        cov = ' · '.join(f"{v['label']}: {v['games']} games" for v in info['leagues'].values())
        st.caption(f"Built {built['at']} from {built['legs']} candidate legs. Coverage: {cov}. Legs from different games are "
                   'treated as independent; one leg per game per parlay; 🔴 legs are live propositions on the pre-game line.')

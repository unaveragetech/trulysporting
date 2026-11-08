"""Streamlit page for the parlay builder: top parlays, build-your-own, and tracking saved parlays to their result."""
import time
from concurrent.futures import ThreadPoolExecutor
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

import pandas as pd
import streamlit as st

import parlay_track as T
import parlays as P
from sporting_shared import viewer_tz

_ESPN_TO_NFLVERSE = {'WSH': 'WAS', 'LAR': 'LA'}
_TYPE_LABELS = {'ml': 'Winner', 'spread': 'Spread', 'total': 'Game total', 'player': 'Player milestones'}
_KIND_BADGE = {'model': '📐', 'market': '💰', 'live': '🔴', 'player': '👤', 'engine': '🏈'}
_STATUS = {'won': '✅ Won', 'lost': '❌ Lost', 'busted': '⚠️ Busted (a leg can no longer win)', 'void': '⚪ Void',
           'live': '🔴 In progress', 'pending': '🟡 Waiting for games', 'push': '➖ Push'}
_LEG_ICON = {'won': '✅', 'lost': '❌', 'push': '➖', 'void': '⚪', 'live': '🔴', 'pending': '🟡'}


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


def _local(ts, tz) -> str:
    t = pd.to_datetime(ts, utc=True, errors='coerce')
    return '—' if pd.isna(t) else t.tz_convert(tz).strftime('%a %I:%M %p').replace(' 0', ' ')


def _flags(l: P.Leg) -> str:
    f = []
    if l.price is not None:
        f.append('💰 priced')
    if any(s.kind == 'market' for s in l.sources):
        f.append('💰 market-backed')
    if any(s.kind in ('model', 'engine') for s in l.sources):
        f.append('📐 model')
    if l.kind == 'player':
        f.append('👤 player')
    if l.edge is not None and l.edge >= 0.03:
        f.append('⭐ edge')
    return ' · '.join(f)


def _legs_frame(pz: P.Parlay, tz) -> pd.DataFrame:
    return pd.DataFrame([{
        'Leg': l.pick, 'Game': l.matchup, 'League': l.league, 'Starts': _local(l.start, tz),
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
        st.markdown('**Why these legs were chosen:** from every game still to be played in a league that is running, each leg must '
                    'clear the minimum chance you set; the search keeps the combinations with the highest joint probability, uses '
                    'at most one leg per game, and drops near-duplicates so you see real alternatives. Legs that can no longer be '
                    'bet (game started) are removed.')
        for l in p.legs:
            with st.expander(f"{l.pick} · {l.p:.0%} · {l.matchup} ({l.league})", expanded=False):
                st.dataframe(pd.DataFrame([{'Source': f"{_KIND_BADGE.get(s.kind, '•')} {s.name}",
                                            'Chance': '—' if s.p is None else f'{s.p:.0%}', 'What it says': s.detail}
                                           for s in l.sources]), hide_index=True, use_container_width=True)
                for n in l.notes:
                    st.caption(n)
        st.markdown('**Assumptions and limits**')
        for a in ex['assumptions']:
            if 'Live legs' not in a:
                st.markdown(f'- {a}')
        st.caption('Data: ESPN scoreboards and embedded lines, Kalshi game markets, team results and player box scores stored by '
                   'this app, and the NFL engine when loaded. Entertainment and analysis only; if you wager, set limits. '
                   'US help line: 1-800-GAMBLER.')
    _show()


# ── Shared settings and the leg pool ─────────────────────────────────────────

def _settings(label: Callable[[str], str], board: pd.DataFrame) -> Optional[Dict]:
    hours = st.session_state.get('pl_hours', 24)
    with st.expander('⚙️ Leagues and filters', expanded=False):
        d1, d2, d3 = st.columns(3)
        hours = d1.slider('Games starting within (hours)', 3, 72, 24, key='pl_hours')
        min_p = d2.slider('Min chance per leg', 0.50, 0.95, 0.60, 0.01, key='pl_minp')
        per_league = d3.slider('Games per league to consider', 4, 25, 8, key='pl_perleague')
        elig = P.eligible_leagues(board, hours, P.MODEL_LEAGUES)
        eps = st.multiselect('Leagues running now', list(elig), default=list(elig), key='pl_eps',
                             format_func=lambda e: f'{label(e)} ({elig[e]} games)')
        types_lbl = st.multiselect('Leg types', list(_TYPE_LABELS.values()), default=list(_TYPE_LABELS.values()), key='pl_types')
        req_mkt = st.toggle('Winner legs need a market price (recommended)', True, key='pl_reqmkt',
                            help='Games with no sportsbook or Kalshi price are skipped for winner legs.')
    elig = P.eligible_leagues(board, hours, P.MODEL_LEAGUES)
    idle = [label(e) for e in P.MODEL_LEAGUES if e not in elig]
    if idle:
        st.caption('Not included (no games to bet on in this window): ' + ', '.join(idle))
    if not elig:
        st.info('No league we can price has games to bet on in this window, so there is nothing to build. Try a longer window.')
        return None
    types = tuple(k for k, v in _TYPE_LABELS.items() if v in types_lbl)
    eps = [e for e in eps if e in elig]
    if not eps or not types:
        st.info('Pick at least one running league and one leg type.')
        return None
    return {'hours': hours, 'min_p': min_p, 'per_league': per_league, 'eps': eps, 'types': types, 'req_mkt': req_mkt}


def _pool(db, worker, season_for, label, cfg: Dict, force: bool = False) -> Tuple[List[P.Leg], Dict]:
    sig = (tuple(sorted(cfg['eps'])), cfg['hours'], cfg['per_league'], cfg['types'], cfg['req_mkt'])
    cur = st.session_state.get('pl_pool')
    if force or not cur or cur['sig'] != sig:
        if force:
            P._CACHE.clear()
        with st.status('Reading games and pricing legs…', expanded=True) as status:
            legs, info = P.collect_legs(db, worker, season_for, label, list(cfg['eps']), cfg['hours'], False, cfg['per_league'],
                                        cfg['types'], _engine_probs(), progress=lambda m: status.write(m), require_market=cfg['req_mkt'])
            games = sum(v['games'] for v in info['leagues'].values())
            status.update(label=f'{len(legs)} bettable legs from {games} games', state='complete', expanded=False)
        cur = st.session_state['pl_pool'] = {'sig': sig, 'legs': legs, 'info': info, 'at': time.strftime('%H:%M:%S')}
    # games may have started since the pool was built
    return P.drop_unbettable(cur['legs']), cur['info']


# ── View 1: top parlays ──────────────────────────────────────────────────────

def _save_parlay(p: P.Parlay, name: str, source: str) -> None:
    rec = T.new_record([P.leg_to_dict(l) for l in p.legs], name, p.p, source)
    T.store_save((st.session_state.get('pl_saved') or []) + [rec])


def _top_view(legs: List[P.Leg], info: Dict, cfg: Dict, tz) -> None:
    with st.expander('⚙️ Parlay options', expanded=False):
        c1, c2, c3, c4 = st.columns(4)
        kmin, kmax = c1.slider('Legs per parlay', 2, 10, (4, 7), key='pl_k')
        top = c2.slider('How many parlays', 3, 20, 10, key='pl_top')
        rank_lbl = c3.radio('Rank by', ['Most likely', 'Best value vs sportsbook'], key='pl_rank')
        max_pl = c4.slider('Max player legs', 0, 4, 2, key='pl_maxpl')
    rank = 'value' if rank_lbl.startswith('Best value') else 'likely'
    pz = P.build_parlays(legs, kmin, kmax, top, cfg['min_p'], max_pl, rank)
    saved_sigs = {tuple(sorted(l['key'] for l in r['legs'])) for r in (st.session_state.get('pl_saved') or [])}
    if not pz:
        st.warning('Not enough legs clear the filters. Try lowering the minimum chance, adding leagues, widening the time '
                   'window or reducing the leg count.')
    for i, p in enumerate(pz, 1):
        with st.container(border=True):
            mk = '' if p.market_decimal is None else f' · sportsbook pays ~{p.market_decimal:.2f}x (edge {p.ev:+.0%})'
            last = max((pd.to_datetime(l.start, utc=True) for l in p.legs))
            st.markdown(f'**#{i} · {p.k}-leg parlay** · hit chance **{p.p:.1%}** · fair odds {_fair(p.p)}{mk}')
            st.dataframe(_legs_frame(p, tz), hide_index=True, use_container_width=True)
            st.caption(f'Last game starts {_local(last, tz)}; the parlay resolves when the last game ends.')
            b1, b2, _ = st.columns([1, 1, 3])
            if b1.button('🔍 Why this parlay', key=f'pl_why_{i}'):
                _why_dialog(p, i)
            done = tuple(sorted(l.key for l in p.legs)) in saved_sigs
            if b2.button('✅ Tracking' if done else '💾 Track this parlay', key=f'pl_save_{i}', disabled=done):
                _save_parlay(p, f'Top parlay #{i}', 'top')
                st.rerun()
    if pz:
        cov = ' · '.join(f"{v['label']}: {v['games']} games" for v in info['leagues'].values())
        st.caption(f'Coverage: {cov}. Legs from different games are treated as independent; one leg per game per parlay. '
                   f"Legs for games that already started are dropped ({info.get('dropped_unbettable', 0)} removed when built).")


# ── View 2: build your own ───────────────────────────────────────────────────

_SORTS = {'Highest chance': ('Chance', False), 'Soonest start': ('_start', True), 'Biggest edge vs market': ('_edge', False),
          'League, then start': ('League', True)}


def _builder_view(legs: List[P.Leg], cfg: Dict, tz) -> None:
    st.markdown('Pick any legs, one per game, and see your parlay\'s chance and when it will resolve.')
    c1, c2, c3, c4 = st.columns([2, 2, 2, 2])
    sort_lbl = c1.selectbox('Sort legs by', list(_SORTS), key='pl_sort')
    kinds = c2.multiselect('Leg type', list(_TYPE_LABELS.values()), default=[_TYPE_LABELS[k] for k in cfg['types']], key='pl_b_types')
    flag = c3.multiselect('Only show', ['💰 priced by a book', '💰 market-backed', '👤 player legs only', '⭐ edge vs market', '🔥 chance 80%+'],
                          key='pl_b_flags')
    q = c4.text_input('Search team or player', key='pl_b_q', placeholder='e.g. Lakers, Jokic')
    kind_keys = {k for k, v in _TYPE_LABELS.items() if v in kinds}
    rows = []
    for l in legs:
        if l.kind not in kind_keys:
            continue
        if '💰 priced by a book' in flag and l.price is None:
            continue
        if '💰 market-backed' in flag and not any(s.kind == 'market' for s in l.sources):
            continue
        if '👤 player legs only' in flag and l.kind != 'player':
            continue
        if '⭐ edge vs market' in flag and not (l.edge is not None and l.edge >= 0.03):
            continue
        if '🔥 chance 80%+' in flag and l.p < 0.8:
            continue
        if q and q.lower() not in f'{l.pick} {l.matchup} {l.league}'.lower():
            continue
        rows.append({'key': l.key, 'Add': False, 'Leg': l.pick, 'Game': l.matchup, 'League': l.league,
                     'Starts': _local(l.start, tz), '_start': pd.to_datetime(l.start, utc=True, errors='coerce'),
                     'Chance': round(100 * l.p), 'Edge': None if l.edge is None else round(100 * l.edge, 1),
                     '_edge': -1 if l.edge is None else l.edge, 'Book price': '—' if l.price is None else f'{l.price:+.0f}',
                     'Flags': _flags(l)})
    if not rows:
        st.info('No legs match these filters.')
        return
    df = pd.DataFrame(rows)
    col, asc = _SORTS[sort_lbl]
    df = df.sort_values(col, ascending=asc, kind='stable').reset_index(drop=True)
    sel: Set[str] = set(st.session_state.get('pl_sel', set()))
    df['Add'] = df['key'].isin(sel)
    shown = df.set_index('key')[['Add', 'Leg', 'Game', 'League', 'Starts', 'Chance', 'Edge', 'Book price', 'Flags']]
    edited = st.data_editor(
        shown, hide_index=True, use_container_width=True, height=420, key=f'pl_editor_{abs(hash((sort_lbl, tuple(kinds), tuple(flag), q)))}',
        disabled=[c for c in shown.columns if c != 'Add'],
        column_config={'Add': st.column_config.CheckboxColumn('Add', width='small'),
                       'Chance': st.column_config.NumberColumn('Chance %', format='%d%%'),
                       'Edge': st.column_config.NumberColumn('Edge vs market', format='%+.1f pts')})
    visible = set(shown.index)
    sel = (sel - visible) | set(edited.index[edited['Add']])
    st.session_state['pl_sel'] = sel
    by_key = {l.key: l for l in legs}
    chosen = [by_key[k] for k in sel if k in by_key]
    gone = len(sel) - len(chosen)
    if gone:
        st.session_state['pl_sel'] = {k for k in sel if k in by_key}
        st.caption(f'{gone} selected leg(s) were removed because their game started or they are no longer available.')
    if not chosen:
        st.caption('Tick **Add** on the legs you want. Legs for games that already started never appear.')
        return
    chosen.sort(key=lambda l: pd.to_datetime(l.start, utc=True))
    games = [l.game_id for l in chosen]
    dupes = sorted({l.matchup for l in chosen if games.count(l.game_id) > 1})
    with st.container(border=True):
        st.markdown(f"#### Your parlay · {len(chosen)} leg{'s' if len(chosen) != 1 else ''}")
        if dupes:
            st.error('Two legs from the same game are correlated and the chance would be wrong: ' + ', '.join(dupes)
                     + '. Keep one per game.')
        pz = P._parlay(chosen, 'likely')
        mk = '' if pz.market_decimal is None else f' · sportsbook pays ~{pz.market_decimal:.2f}x (edge {pz.ev:+.0%})'
        st.markdown(f'Hit chance **{pz.p:.1%}** · fair odds {_fair(pz.p)}{mk}')
        st.dataframe(_legs_frame(pz, tz), hide_index=True, use_container_width=True)
        plan_rec = {'legs': [P.leg_to_dict(l) for l in chosen]}
        plan = T.resolution_plan(plan_rec, {(l.ep, str(l.game_id)): {'state': 'pre', 'start': l.start} for l in chosen})
        st.markdown(f"**Resolves:** when the last game ends, {T.fmt_when(plan['resolves_at'], tz)}. "
                    f"First game can end {T.fmt_when(plan['first_end'], tz)}.")
        c1, c2, c3 = st.columns([3, 1, 1])
        name = c1.text_input('Name (optional)', key='pl_name', placeholder='My Saturday parlay')
        if c2.button('💾 Save to My parlays', type='primary', disabled=bool(dupes), key='pl_savecustom'):
            _save_parlay(pz, name, 'custom')
            st.session_state['pl_sel'] = set()
            st.session_state['pl_flash'] = 'Saved. Open **My parlays** to follow it to the final result.'
            st.rerun()  # the browser copy is written on the next run
        if c3.button('Clear', key='pl_clear'):
            st.session_state['pl_sel'] = set()
            st.rerun()


# ── View 3: my parlays ───────────────────────────────────────────────────────

def _fetch_all(records: List[Dict]) -> Dict[Tuple[str, str], Dict]:
    need = {(l['ep'], str(l['game_id'])) for r in records if not (r.get('result') or {}).get('settled') for l in r['legs']}
    if not need:
        return {}
    with ThreadPoolExecutor(max_workers=8) as pool:
        return dict(zip(need, pool.map(lambda k: T.fetch_game(*k), list(need))))


def _record_card(r: Dict, games: Dict, tz, now) -> Optional[Dict]:
    """Render one saved parlay; returns an updated record if it just settled."""
    res = r.get('result')
    updated = None
    if res and res.get('settled'):
        g = res
    else:
        g = T.grade_parlay(r, games)
        if g['settled']:
            updated = {**r, 'result': {'status': g['status'], 'settled': True, 'settled_at': now.isoformat(),
                                       'legs': [{'status': x['status'], 'detail': x['detail']} for x in g['legs']]}}
    plan = None if g.get('settled') else T.resolution_plan(r, games, now)
    with st.container(border=True):
        top = st.columns([4, 1])
        top[0].markdown(f"**{r['name']}** · {len(r['legs'])} legs · chance when saved **{r['p_saved']:.1%}** · "
                        f"saved {_local(r['created'], tz)}")
        top[0].markdown(f"**{_STATUS.get(g['status'], g['status'])}**")
        if top[1].button('🗑 Delete', key=f"pl_del_{r['id']}"):
            T.store_save([x for x in st.session_state['pl_saved'] if x['id'] != r['id']])
            st.rerun()
        rows = []
        for i, leg in enumerate(r['legs']):
            gl = g['legs'][i]
            ends = ''
            if plan:
                pr = next((x for x in plan['games'] if x['game'] == leg['matchup']), None)
                ends = 'final' if pr is None or pr['ends'] is None else T.fmt_when(pr['ends'], tz, now)
            rows.append({'': _LEG_ICON.get(gl['status'], ''), 'Leg': leg['pick'], 'Game': leg['matchup'],
                         'Result so far': gl['detail'], 'Chance': f"{leg['p']:.0%}",
                         'Starts': _local(leg.get('start'), tz), 'Expected finish': ends if not g.get('settled') else 'final'})
        st.dataframe(pd.DataFrame(rows), hide_index=True, use_container_width=True)
        if g.get('settled'):
            when = _local(res['settled_at'], tz) if res and res.get('settled_at') else _local(now, tz)
            st.caption(f"All games over. Settled {when}: **{g['status'].upper()}**.")
        else:
            if g['status'] == 'lost':
                st.caption('A leg already lost, so this parlay is lost. Remaining games are still being tracked.')
            if plan and plan['resolves_at'] is not None:
                st.caption(f"Resolves when the last game ends: {T.fmt_when(plan['resolves_at'], tz, now)}. "
                           f"Earliest a game can end: {T.fmt_when(plan['first_end'], tz, now)}.")
            elif g.get('all_over'):
                st.caption('All games are over; finalizing.')
    return updated


def _my_view(saved: Optional[List[Dict]], tz) -> None:
    if saved is None:
        st.info('Loading your saved parlays…')
        return
    if not saved:
        st.info('Nothing saved yet. Press **Track this parlay** on a top parlay, or build your own, and it will be followed to '
                'the final result here. Parlays live in this browser only.')
        return
    pending = any(not (r.get('result') or {}).get('settled') for r in saved)

    @st.fragment(run_every=45 if pending else None)
    def _body():
        recs = st.session_state.get('pl_saved') or []
        now = pd.Timestamp.now(tz='UTC')
        games = _fetch_all(recs)
        changed = {}
        order = sorted(recs, key=lambda r: ((r.get('result') or {}).get('settled', False), r['created']), reverse=False)
        for r in order:
            upd = _record_card(r, games, tz, now)
            if upd:
                changed[r['id']] = upd
        if changed:
            T.store_save([changed.get(r['id'], r) for r in recs])
            st.rerun()
        tr = T.track_record(recs)
        if tr['legs']:
            with st.expander(f"📊 Track record: {tr['parlays_won']}/{tr['parlays']} parlays won, {tr['legs_won']}/{tr['legs']} legs hit "
                             f"(we predicted {tr['avg_predicted']:.0%})"):
                st.dataframe(pd.DataFrame([{'Predicted chance': b['range'], 'Legs': b['legs'], 'Average predicted': f"{b['predicted']:.0%}",
                                            'Actually hit': f"{b['actual']:.0%}"} for b in tr['buckets']]), hide_index=True)
        st.caption('Updates every 45 seconds while games are on. Void legs (postponed, or a player who did not play) drop out and '
                   'the parlay is graded on the rest, as at a sportsbook.' if pending else 'All saved parlays are settled.')
    _body()


# ── Page ─────────────────────────────────────────────────────────────────────

def render_parlay_page(db: Any, worker: Any, season_for: Callable[[str], int], label: Callable[[str], str]) -> None:
    from live import fetch_all_games
    tz = viewer_tz()
    st.markdown('## 🎰 Parlay Lab')
    st.caption('Top parlays and your own, from games that can still be bet on, in leagues that are running. Every leg shows its data '
               'sources, and saved parlays are followed to the final result. Estimates from public data, for entertainment and '
               'analysis, not betting advice. Must be 18+.')
    saved = T.store_sync()
    flash = st.session_state.pop('pl_flash', None)
    if flash:
        st.success(flash)
    n_open = 0 if not saved else sum(1 for r in saved if not (r.get('result') or {}).get('settled'))
    view = st.segmented_control('View', ['🎰 Top parlays', '🛠 Build your own', f'📒 My parlays ({n_open} open)' if n_open else '📒 My parlays'],
                                key='pl_view', default='🎰 Top parlays', label_visibility='collapsed') or '🎰 Top parlays'
    if view.startswith('📒'):
        _my_view(saved, tz)
        return
    try:
        board = fetch_all_games(tuple(P.MODEL_LEAGUES))
    except Exception:
        board = pd.DataFrame()
    cfg = _settings(label, board)
    if cfg is None:
        return
    rebuild = st.button('🔄 Refresh games and prices', key='pl_rebuild')
    legs, info = _pool(db, worker, season_for, label, cfg, rebuild)
    st.caption(f"{len(legs)} bettable legs ready (built {st.session_state['pl_pool']['at']}).")
    if view.startswith('🛠'):
        _builder_view([l for l in legs if l.p >= cfg['min_p']], cfg, tz)
    else:
        _top_view(legs, info, cfg, tz)

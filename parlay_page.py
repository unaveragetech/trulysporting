"""Streamlit page for the parlay builder: top parlays, build-your-own, and tracking saved parlays to their result."""
import time
from concurrent.futures import ThreadPoolExecutor
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

import pandas as pd
import streamlit as st

import parlay_detail as D
import parlay_pricing as PP
import parlay_rel as R
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


# ── Shared settings and the leg pool ─────────────────────────────────────────

def _settings(label: Callable[[str], str], board: pd.DataFrame) -> Optional[Dict]:
    hours = st.session_state.get('pl_hours', 24)
    with st.expander('⚙️ Leagues and filters', expanded=False):
        d1, d2, d3 = st.columns(3)
        hours = d1.slider('Games starting within (hours)', 3, 72, 24, key='pl_hours')
        min_p = d2.slider('Min chance per leg', 0.50, 0.95, step=0.01, key='pl_minp')
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
    rp = PP.price_report(p.legs, p.p)
    use = rp['best_book']['decimal'] if rp.get('best_book') else (rp['estimate']['decimal'] if rp.get('estimate') else None)
    rec['price'] = {'book': rp['best_book']['book'] if rp.get('best_book') else None, 'decimal': use, 'estimated': not rp.get('best_book'),
                    'fair_decimal': rp.get('fair_decimal_market'), 'house_edge': rp.get('house_edge'), 'at': pd.Timestamp.now(tz='UTC').isoformat()}
    T.store_save((st.session_state.get('pl_saved') or []) + [rec])


_RANKS = {'Most likely': 'likely', 'Balanced (chance x reliability)': 'balanced', 'Most reliable': 'reliable',
          'Best value vs sportsbook': 'value'}
_RANK_HELP = {'likely': 'Highest hit chance first.', 'balanced': 'Chance, discounted when the evidence behind a leg is thin.',
              'reliable': 'Legs with the strongest, most agreeing evidence first.', 'value': 'Largest edge over the sportsbook price first.'}


def _apply_preset() -> None:
    """Copy a preset's numbers into the controls (runs as a widget callback, before the controls are drawn)."""
    ss = st.session_state
    d = R.PRESETS.get(ss.get('pl_preset'))
    if not d or 'k' not in d:
        return
    ss['pl_k'] = d['k']
    ss['pl_minp'] = d['min_p']
    ss['pl_rank'] = next(k for k, v in _RANKS.items() if v == d['rank'])
    ss['pl_band'] = (int(d['pmin'] * 100), int(d['pmax'] * 100))
    ss['pl_minrel'] = d['min_rel']
    ss['pl_priced'] = d['priced']
    ss['pl_pergame'] = d['per_game']
    ss['pl_maxpl'] = d['max_pl']


def _legs_frame(pz: P.Parlay, tz) -> pd.DataFrame:
    rows = []
    for i, l in enumerate(pz.legs, 1):
        o = R.leg_odds(l)
        rel = R.reliability(l)
        rows.append({'#': i, 'Leg': l.pick, 'Game': l.matchup, 'League': l.league, 'Starts': _local(l.start, tz),
                     'Chance': round(100 * l.p), 'Our odds': '—' if o['fair'] is None else f"{o['fair']:+d}",
                     'Best price': '—' if o['best_price'] is None else f"{o['best_price']:+d}",
                     'Book': o['best_book'] or ('no price' if l.kind != 'player' else 'no feed'),
                     'Reliability': round(rel['score']), 'Edge': None if l.edge is None else round(100 * l.edge, 1),
                     'Data': ' '.join(f"{_KIND_BADGE.get(s.kind, '•')}" for s in l.sources)})
    return pd.DataFrame(rows)


_LEG_COLS = {'#': st.column_config.NumberColumn('#', width='small'),
             'Chance': st.column_config.ProgressColumn('Chance', min_value=0, max_value=100, format='%d%%', width='small',
                                                       help='Our estimated chance this leg wins.'),
             'Our odds': st.column_config.TextColumn('Our odds', help='The fair American odds for our chance, with no margin.', width='small'),
             'Best price': st.column_config.TextColumn('Best price', help='Best sportsbook price we found for this exact bet.', width='small'),
             'Reliability': st.column_config.ProgressColumn('Reliability', min_value=0, max_value=100, format='%d', width='small',
                                                            help='How far to trust the chance (5-95). Not a probability. Open the breakdown for the reasons.'),
             'Edge': st.column_config.NumberColumn('Edge', format='%+.1f pts', width='small',
                                                   help='Our chance minus the market chance. Positive means we like it more than the books do.')}


def _show_legs(pz: P.Parlay, tz) -> None:
    st.dataframe(_legs_frame(pz, tz), hide_index=True, use_container_width=True, column_config=_LEG_COLS)


def _headline(p: P.Parlay, rep: Dict) -> None:
    """The numbers a bettor looks at first, side by side."""
    bb, est = rep.get('best_book'), rep.get('estimate')
    use = bb['decimal'] if bb else (est['decimal'] if est else None)
    c1, c2, c3, c4, c5 = st.columns(5)
    c1.metric('Hit chance', f'{p.p:.1%}', f'fair odds {_fair(p.p)}', delta_color='off')
    if use:
        ret, prof = PP.payout(use, 10)
        c2.metric('\\$10 pays' if not est or bb else '\\$10 pays (est.)', money_plain(ret), (bb['book'] + ' ' + D.am(use)) if bb else f'~{D.am(use)} estimate',
                  delta_color='off')
    else:
        c2.metric('\\$10 pays', '—', 'no price found', delta_color='off')
    be = rep.get('break_even')
    c3.metric('Break-even', f'{be:.1%}' if be else '—', 'chance needed to profit', delta_color='off')
    ev = rep.get('ev_ours')
    c4.metric('Expected value', '—' if ev is None else f'{ev:+.1%}', 'per dollar staked, if we are right', delta_color='off')
    c5.metric('Reliability', f'{R.label_for(p.rel)}', f'{p.rel:.0f} / 100', delta_color='off')


def money_plain(x: float) -> str:
    return f'${x:,.2f}'


def _top_view(legs: List[P.Leg], info: Dict, cfg: Dict, tz) -> None:
    ss = st.session_state
    st.markdown('**Strategy**')
    st.segmented_control('Strategy', list(R.PRESETS), key='pl_preset', on_change=_apply_preset, label_visibility='collapsed')
    st.caption(R.PRESETS.get(ss.get('pl_preset') or R.DEFAULT_PRESET, {}).get('desc', ''))
    with st.expander('⚙️ Tune the generator (every control)', expanded=False):
        c1, c2, c3, c4 = st.columns(4)
        kmin, kmax = c1.slider('Legs per parlay', 2, 12, key='pl_k')
        top = c2.slider('How many parlays', 3, 25, 10, key='pl_top')
        rank_lbl = c3.selectbox('Rank by', list(_RANKS), key='pl_rank')
        max_pl = c4.slider('Max player legs', 0, 4, key='pl_maxpl')
        d1, d2, d3, d4 = st.columns(4)
        band = d1.slider('Parlay hit chance between (%)', 0, 100, key='pl_band',
                         help='Keep only parlays whose combined chance falls in this band. Lower bands mean bigger payouts: try 8-35% for longshots.')
        min_rel = d2.slider('Min reliability per leg', 0, 90, step=5, key='pl_minrel', help='Drops legs whose evidence is thin (0 keeps all).')
        per_game = d3.slider('Leg options per game', 1, 6, key='pl_pergame', help='How many different legs from one game the search may choose between.')
        priced = d4.toggle('Only legs a sportsbook prices', key='pl_priced', help='Skips player milestones and anything without a book quote.')
        st.caption(_RANK_HELP[_RANKS[rank_lbl]] + ' One leg per game per parlay; legs from different games are treated as independent.')
        labels = {l.key: f'{l.pick} ({l.matchup}, {l.p:.0%})' for l in sorted(legs, key=lambda x: -x.p)}
        locked = st.multiselect('🔒 Lock these legs into every parlay (optional)', list(labels), format_func=labels.get, key='pl_lock',
                                help='Every parlay will include these legs. Other legs from the same games are not used.')
    locked = [k for k in (ss.get('pl_lock') or []) if k in labels]
    rank = _RANKS[rank_lbl]
    pz = P.build_parlays(legs, kmin, kmax, top, cfg['min_p'], max_pl, rank, options_per_game=per_game, min_parlay_p=band[0] / 100,
                         max_parlay_p=band[1] / 100, min_rel=min_rel, must_include=tuple(locked), require_priced=priced)
    saved_sigs = {tuple(sorted(l['key'] for l in r['legs'])) for r in (st.session_state.get('pl_saved') or [])}
    if not pz:
        st.warning('No parlay matches these settings. Try a lower minimum chance, a wider hit-chance band, a lower minimum reliability, '
                   'more leagues, a longer time window, fewer legs, or unlock a locked leg.')
        _diagnose(legs, cfg, min_rel, priced, kmin, max_pl)
    strategy = ss.get('pl_preset') or ''
    for i, p in enumerate(pz, 1):
        with st.container(border=True):
            rep_ = PP.price_report(p.legs, p.p)
            last = max((pd.to_datetime(l.start, utc=True) for l in p.legs))
            first = min((pd.to_datetime(l.start, utc=True) for l in p.legs))
            st.markdown(f"**#{i} · {p.k}-leg parlay** &nbsp; `{strategy}`" if strategy and 'Custom' not in strategy else f'**#{i} · {p.k}-leg parlay**')
            _headline(p, rep_)
            wk = R.weakest(p.legs)
            if p.k >= 3 and wk is not None:
                st.caption(f"Weakest link: **{wk.pick}** at {wk.p:.0%}. Without it the chance rises to {p.p / wk.p:.1%}. "
                           f"Games run {_local(first, tz)} to {_local(last, tz)}; it resolves when the last game ends.")
            if rep_.get('best_book') is None:
                st.caption(f"💵 {rep_['n_priced']} of {rep_['n']} legs have real sportsbook prices; the price above estimates the rest with a standard margin. "
                           'Open the full breakdown for each leg.')
            _show_legs(p, tz)
            b1, b2, b3 = st.columns([1, 1, 3])
            if b1.button('🔍 Full breakdown', key=f'pl_why_{i}'):
                D.why_dialog(p, i, tz, st.session_state.get('pl_pool', {}).get('at', ''))
            done = tuple(sorted(l.key for l in p.legs)) in saved_sigs
            if b2.button('✅ Tracking' if done else '💾 Track this parlay', key=f'pl_save_{i}', disabled=done):
                _save_parlay(p, f'Top parlay #{i}', 'top')
                st.rerun()
            rows = R.drop_one(p.legs)
            if rows:
                with b3.popover('✂️ What if I drop a leg?'):
                    st.caption('Each row is this parlay without that leg.')
                    st.dataframe(pd.DataFrame([{'Without': r_['leg'], 'Chance': f"{r_['chance']:.1%}", 'Gain': f"{100 * r_['gain']:+.1f} pts",
                                                'Fair odds': f"{r_['fair']:+d}" if r_['fair'] else '—',
                                                '\\$10 pays': ('~' if r_['estimated'] else '') + (money_plain(10 * r_['decimal']) if r_['decimal'] else '—'),
                                                'Reliability': f"{r_['reliability']:.0f}"} for r_ in rows]),
                                 hide_index=True, use_container_width=True)
    if pz:
        cov = ' · '.join(f"{v['label']}: {v['games']} games" for v in info['leagues'].values())
        st.caption(f'Coverage: {cov}. Legs from different games are treated as independent; one leg per game per parlay. '
                   f"Legs for games that already started are dropped ({info.get('dropped_unbettable', 0)} removed when built). "
                   'Reliability is a 5-95 heuristic of how much to trust each chance (market backing, agreeing sources, sample size, news risk); '
                   'it is not a probability.')


def _diagnose(legs: List[P.Leg], cfg: Dict, min_rel: int, priced: bool, kmin: int, max_pl: int) -> None:
    """Say which limit is binding when no parlay can be built."""
    ok = [l for l in legs if l.p >= cfg['min_p']]
    if min_rel:
        ok = [l for l in ok if R.leg_score(l) >= min_rel]
    if priced:
        ok = [l for l in ok if l.price is not None or any(q.get('kind') in ('sportsbook', 'espn') for q in l.quotes)]
    game_legs = {l.game_id for l in ok if l.kind != 'player'}
    player_only = {l.game_id for l in ok if l.kind == 'player'} - game_legs
    reach = len(game_legs) + min(max_pl, len(player_only))
    st.caption(f"{len(legs)} legs in the pool; {len(ok)} pass your minimum chance{' and the other filters' if (min_rel or priced) else ''}, "
               f"from {len({l.game_id for l in ok})} games. {len(game_legs)} of those games have a winner, spread or total leg and "
               f"{len(player_only)} more only a player leg. With at most {max_pl} player leg(s) you can reach {reach} legs; you asked for "
               f"at least {kmin}." + (' Raise **Max player legs** or lower the minimum chance to get more.' if reach < kmin else ''))


# ── View 2: build your own ───────────────────────────────────────────────────

_SORTS = {'Highest chance': ('Chance', False), 'Most reliable': ('Reliability', False), 'Best price first': ('_price', False), 'Soonest start': ('_start', True), 'Biggest edge vs market': ('_edge', False),
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
        o_ = R.leg_odds(l)
        rows.append({'key': l.key, 'Add': False, 'Leg': l.pick, 'Game': l.matchup, 'League': l.league,
                     'Starts': _local(l.start, tz), '_start': pd.to_datetime(l.start, utc=True, errors='coerce'),
                     'Chance': round(100 * l.p), 'Edge': None if l.edge is None else round(100 * l.edge, 1),
                     '_edge': -1 if l.edge is None else l.edge, 'Book price': '—' if l.price is None else f'{l.price:+.0f}',
                     'Our odds': '—' if o_['fair'] is None else f"{o_['fair']:+d}",
                     'Best price': '—' if o_['best_price'] is None else f"{o_['best_price']:+d}", 'Book': o_['best_book'] or '',
                     '_price': -9999 if o_['best_price'] is None else o_['best_price'],
                     'Reliability': round(R.reliability(l)['score']), 'Flags': _flags(l), 'gid': l.game_id})
    if not rows:
        st.info('No legs match these filters.')
        return
    df = pd.DataFrame(rows)
    col, asc = _SORTS[sort_lbl]
    df = df.sort_values(col, ascending=asc, kind='stable').reset_index(drop=True)
    sel: Set[str] = set(st.session_state.get('pl_sel', set()))
    q1, q2, q3 = st.columns([2, 2, 3])
    n_stack = q1.number_input('Quick stack size', 2, 12, 5, key='pl_stackn', help='How many legs the stack buttons add.')
    if q2.button('🔒 Stack the most likely legs', key='pl_stack_likely', help='Adds the N highest-chance legs, one per game, from the legs shown.'):
        st.session_state['pl_sel'] = set(df.sort_values('Chance', ascending=False).drop_duplicates('gid').head(int(n_stack))['key'])
        st.rerun()
    if q3.button('🛡 Stack the most reliable legs (chance 70%+)', key='pl_stack_rel', help='Adds the N most reliable legs that clear 70%, one per game.'):
        st.session_state['pl_sel'] = set(df[df['Chance'] >= 70].sort_values(['Reliability', 'Chance'], ascending=False)
                                         .drop_duplicates('gid').head(int(n_stack))['key'])
        st.rerun()
    df['Add'] = df['key'].isin(sel)
    shown = df.set_index('key')[['Add', 'Leg', 'Game', 'League', 'Starts', 'Chance', 'Our odds', 'Best price', 'Book', 'Reliability', 'Edge', 'Flags']]
    edited = st.data_editor(
        shown, hide_index=True, use_container_width=True, height=420, key=f'pl_editor_{abs(hash((sort_lbl, tuple(kinds), tuple(flag), q)))}',
        disabled=[c for c in shown.columns if c != 'Add'],
        column_config={'Add': st.column_config.CheckboxColumn('Add', width='small'),
                       'Chance': st.column_config.NumberColumn('Chance %', format='%d%%'),
                       'Our odds': st.column_config.TextColumn('Our odds', help='Fair American odds for our chance, no margin.'),
                       'Best price': st.column_config.TextColumn('Best price', help='Best sportsbook price found for this exact bet.'),
                       'Reliability': st.column_config.NumberColumn('Reliability', format='%d', help='How far to trust the chance, 5-95. Not a probability.'),
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
        _headline(pz, PP.price_report(pz.legs, pz.p))
        _show_legs(pz, tz)
        if st.button('🔍 Full breakdown: price, sources and every fact', key='pl_b_detail'):
            D.why_dialog(pz, 0, tz, st.session_state.get('pl_pool', {}).get('at', ''))
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


_VSTAT = {'ok': '✅ Placeable', 'caution': '⚠️ Verify at the book', 'no': '❌ Not placeable'}


def _venue_box(r: Dict, tz) -> None:
    """Best sportsbook for a watched parlay, from a live re-price and hard validity checks."""
    import parlay_venues as V
    res = V.check_record(r)
    when = _local(res['checked'], tz)
    if res.get('error'):
        st.caption(f"🏦 Could not check sportsbooks right now ({res['error']}).")
        return
    b = res['best']
    if b:
        ret, prof = PP.payout(b['decimal'], 10)
        line = (f"🏦 **Best book: {b['name']} {D.am(b['decimal'])}** · {_VSTAT[b['status']]} · \\$10 pays {D.mdm(ret)}"
                + (f" (price covers the {res['n_verified']} verifiable legs)" if res.get('unpriced_legs') else ''))
        (st.success if b['status'] == 'ok' else st.warning)(line)
    else:
        st.error('🏦 No sportsbook can be confirmed for this parlay right now. ' + ('Closed legs: ' + ', '.join(res['closed']) + '. ' if res.get('closed') else '')
                 + 'See the checks below.')
    with st.expander(f'Where can this be bought? Checked {when}'):
        rows = [{'Venue': v['name'], 'Type': 'Sportsbook parlay' if v['type'] == 'sportsbook' else 'Single bets only (not a parlay)',
                 'Status': _VSTAT[v['status']], 'Price': D.am(v['decimal']) if v['decimal'] else '—',
                 '$10 pays': D.money(10 * v['decimal']) if v['decimal'] else '—', 'Legs verified': f"{v['covered']}/{v['n']}",
                 'Data from': ' + '.join(v['via'])} for v in res['venues']]
        if rows:
            st.dataframe(pd.DataFrame(rows), hide_index=True, use_container_width=True)
        for v in res['venues']:
            bad = [t for s_, t in v['reasons'] if s_ == 'fail']
            warn = [t for s_, t in v['reasons'] if s_ == 'warn']
            if bad or warn:
                st.markdown(f"**{v['name']}**\n\n" + '\n'.join([f'- ❌ {t}' for t in bad] + [f'- ⚠️ {t}' for t in warn]))
            links = [x for x in v.get('links', []) if x]
            if links and v['status'] != 'no':
                st.caption('Open at the book: ' + ' · '.join(f'[leg {i + 1}]({u})' for i, u in enumerate(links)))
        for s_, t in res['general']:
            st.caption(('❌ ' if s_ == 'fail' else '⚠️ ') + t)
        st.caption('A venue is called placeable only when it quotes every verifiable leg at the exact saved line, with fresh, sane prices '
                   '(two sides add to a normal margin, under 30 minutes old), no game has started, and no leg is a same-game or player '
                   'prop. Books can still reject or reprice a ticket: confirm the price at the book before betting. Exchanges and prediction '
                   'markets only sell single bets, so they are shown as a separate-bets route, never as the best parlay book.')


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
        pr_ = r.get('price')
        if pr_ and pr_.get('decimal'):
            ret, prof = PP.payout(pr_['decimal'], 10)
            who = pr_['book'] if pr_.get('book') else 'estimated'
            top[0].caption(f"Price when saved ({_local(pr_['at'], tz)}): {who} {D.am(pr_['decimal'])}, \\$10 would pay "
                           f"{D.mdm(ret)} if it hits." + (' (estimate; some legs had no sportsbook price)' if pr_.get('estimated') else ''))
        if not g.get('settled'):
            _venue_box(r, tz)
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
    if 'pl_k' not in st.session_state:  # first visit: start from the default strategy
        st.session_state.setdefault('pl_preset', R.DEFAULT_PRESET)
        _apply_preset()
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

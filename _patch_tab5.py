"""One-shot patch: replaces TAB 5 Section A + B with improved charts + new Section C"""
import re

content = open('sporting.py', encoding='utf-8').read()

OLD_START = "            # \u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\n            # SECTION A \u2014 POLL RANKINGS (college leagues only)"
OLD_END = "_r5s_dfig, use_container_width=True)\n\n    # \u2500\u2500 TAB 6: NETWORK / COORDINATOR"

si = content.find(OLD_START)
ei = content.find(OLD_END)
assert si != -1, "Could not find start marker"
assert ei != -1, "Could not find end marker"

# Include to the end of "use_container_width=True)" for the end marker
ei_end = ei + len("_r5s_dfig, use_container_width=True)")

new_sections = r"""            # ══════════════════════════════════════════════════
            # SECTION A — POLL RANKINGS  (college leagues only)
            # ══════════════════════════════════════════════════
            if _r5_has_polls:
                st.markdown("### 📊 Poll Rankings")
                _r5_df = db.get_rankings_df(_r5_ep)

                if _r5_df.empty:
                    st.info("No rankings — click **🔄 Rankings** or **🔄 Both**.")
                else:
                    _r5_polls = _r5_df['poll'].unique().tolist()
                    _r5_poll_tabs = st.tabs(_r5_polls)

                    for _r5_pi, _r5_poll in enumerate(_r5_polls):
                        with _r5_poll_tabs[_r5_pi]:
                            _r5_pdf = (_r5_df[_r5_df['poll'] == _r5_poll]
                                       .sort_values('rank').head(25).copy())

                            if _r5_pdf.empty:
                                st.info("No data for this poll.")
                                continue

                            # ── 4-column metrics ──────────────
                            _r5_top = _r5_pdf.iloc[0]
                            _m1, _m2, _m3, _m4 = st.columns(4)
                            _m1.metric("#1 Team", _r5_top['team'])
                            _m2.metric("Record", _r5_top.get('record', ''))
                            _m3.metric("1st-Place Votes", int(_r5_top.get('first_place_votes', 0)))
                            _m4.metric("Teams Ranked", len(_r5_pdf))
                            st.divider()

                            # ── Movement arrows ───────────────
                            def _r5_arrow(row):
                                prev = row.get('previous_rank', 0) or 0
                                cur  = row.get('rank', 0)
                                if not prev:  return '🔵 NEW'
                                d = int(prev) - int(cur)
                                if d > 0:     return f'🟢 ▲{d}'
                                if d < 0:     return f'🔴 ▼{abs(d)}'
                                return '⚪ –'

                            _r5_disp = _r5_pdf.copy()
                            _r5_disp['Move'] = _r5_disp.apply(_r5_arrow, axis=1)

                            _r5_filt = st.text_input(
                                "🔍 Filter teams",
                                key=f"r5_filt_{_r5_pi}_{_r5_ep}",
                                placeholder="Type team name…",
                            )
                            if _r5_filt:
                                _r5_disp = _r5_disp[
                                    _r5_disp['team'].str.contains(_r5_filt, case=False, na=False)]

                            st.dataframe(
                                _r5_disp[['rank', 'Move', 'team', 'record',
                                          'points', 'first_place_votes']].rename(columns={
                                    'rank': 'Rank', 'team': 'Team', 'record': 'Record',
                                    'points': 'Points', 'first_place_votes': '1st Votes',
                                }),
                                use_container_width=True, hide_index=True,
                            )

                            # ── Chart row: Voting-points gradient bar + 1st-votes bar ──
                            _r5_ch1, _r5_ch2 = st.columns(2)

                            with _r5_ch1:
                                n_teams = len(_r5_pdf)
                                def _fade(hex_c, factor):
                                    h = _r5_safe_color(hex_c).lstrip('#')
                                    r2, g2, b2 = (int(h[i:i+2], 16) for i in (0, 2, 4))
                                    r3 = int(r2 * factor + 255 * (1 - factor))
                                    g3 = int(g2 * factor + 255 * (1 - factor))
                                    b3 = int(b2 * factor + 255 * (1 - factor))
                                    return f'rgb({r3},{g3},{b3})'
                                _r5_bar_cols = [
                                    _fade(row.get('team_color', ''), 0.95 - 0.45 * i / max(n_teams - 1, 1))
                                    for i, (_, row) in enumerate(_r5_pdf.iterrows())
                                ]
                                _r5_pfig = go.Figure(go.Bar(
                                    x=_r5_pdf['team'], y=_r5_pdf['points'],
                                    marker=dict(color=_r5_bar_cols, line=dict(width=0)),
                                    text=('#' + _r5_pdf['rank'].astype(int).astype(str)),
                                    textposition='outside', textfont=dict(size=10, color='#444'),
                                    hovertemplate='<b>#%{text} %{x}</b><br>Voting Points: <b>%{y:,}</b><extra></extra>',
                                ))
                                _r5_pfig.update_layout(**_r5_base_layout(
                                    title=dict(text=f'📊 {_r5_poll} — Voting Points', font=dict(size=13)),
                                    height=370,
                                    xaxis=dict(tickangle=-38, tickfont=dict(size=10), **_R5_AXIS),
                                    yaxis=dict(**_R5_AXIS),
                                    margin=dict(t=50, b=90, l=30, r=10),
                                    showlegend=False,
                                ))
                                st.plotly_chart(_r5_pfig, use_container_width=True)

                            with _r5_ch2:
                                _r5_fpv = (_r5_pdf[_r5_pdf['first_place_votes'] > 0]
                                           .sort_values('first_place_votes'))
                                if not _r5_fpv.empty:
                                    _r5_fpv_cols = [_r5_safe_color(r.get('team_color', ''))
                                                   for _, r in _r5_fpv.iterrows()]
                                    _r5_ffig = go.Figure(go.Bar(
                                        x=_r5_fpv['first_place_votes'], y=_r5_fpv['team'],
                                        orientation='h',
                                        marker=dict(color=_r5_fpv_cols, line=dict(width=0)),
                                        text=_r5_fpv['first_place_votes'].astype(int),
                                        textposition='outside',
                                        hovertemplate='<b>%{y}</b><br>1st-Place Votes: <b>%{x}</b><extra></extra>',
                                    ))
                                    _r5_ffig.update_layout(**_r5_base_layout(
                                        title=dict(text='🥇 1st-Place Votes', font=dict(size=13)),
                                        height=370,
                                        xaxis=dict(**_R5_AXIS),
                                        yaxis=dict(autorange='reversed', tickfont=dict(size=10), **_R5_AXIS),
                                        margin=dict(t=50, b=20, l=160, r=40),
                                        showlegend=False,
                                    ))
                                    st.plotly_chart(_r5_ffig, use_container_width=True)
                                else:
                                    st.info("No 1st-place vote data.")

                            # ── Rank movement history ─────────
                            _r5_hist = db.get_rankings_history_df(_r5_ep, _r5_poll)
                            if not _r5_hist.empty and _r5_hist['snapshot_date'].nunique() > 1:
                                st.markdown("**📈 Top-10 Rank Movement Over Time**")
                                _r5_top10_ta = (_r5_hist[_r5_hist['rank'] <= 10]['team_abbr'].unique().tolist())
                                _r5_hfig = go.Figure()
                                for _r5_ta in _r5_top10_ta:
                                    _r5_tdf = (_r5_hist[_r5_hist['team_abbr'] == _r5_ta].sort_values('snapshot_date'))
                                    _c = _r5_safe_color(_r5_tdf['team_color'].iloc[0])
                                    _r5_hfig.add_trace(go.Scatter(
                                        x=_r5_tdf['snapshot_date'], y=_r5_tdf['rank'],
                                        mode='lines+markers', name=_r5_ta,
                                        line=dict(color=_c, width=3, shape='spline'),
                                        marker=dict(size=8, color=_c, line=dict(width=2, color='white')),
                                        hovertemplate=f'<b>{_r5_ta}</b><br>Date: %{{x}}<br>Rank: <b>#%{{y}}</b><extra></extra>',
                                    ))
                                _r5_hfig.update_layout(**_r5_base_layout(
                                    title=dict(text='📈 Rank Movement (Top-10)', font=dict(size=13)),
                                    height=430,
                                    yaxis=dict(autorange='reversed', title='Rank', dtick=1,
                                               range=[10.5, 0.5], **_R5_AXIS),
                                    xaxis=dict(**_R5_AXIS),
                                    legend=dict(orientation='h', y=-0.22, font=dict(size=11)),
                                    margin=dict(t=55, b=80, l=50, r=10),
                                ))
                                st.plotly_chart(_r5_hfig, use_container_width=True)
                                st.caption(f"{_r5_hist['snapshot_date'].nunique()} snapshots · Each 🔄 Rankings load adds a new data point.")
                            elif not _r5_hist.empty:
                                st.caption("📅 Load on multiple days to build the rank-movement chart.")

            # ══════════════════════════════════════════════════
            # SECTION B — STANDINGS (all leagues)
            # ══════════════════════════════════════════════════
            st.markdown("### 📋 Standings")
            _r5s_df = db.get_standings_df(_r5_cat, _r5_spt)

            if _r5s_df.empty:
                st.info("No standings yet — click **🔄 Standings** or **🔄 Both**.")
            else:
                _r5s_best  = _r5s_df.sort_values('win_pct', ascending=False).iloc[0]
                _r5s_most  = _r5s_df.sort_values('wins',    ascending=False).iloc[0]
                _r5s_diff  = _r5s_df.sort_values('diff',    ascending=False).iloc[0]
                _r5s_worst = _r5s_df.sort_values('win_pct', ascending=True).iloc[0]
                _s1, _s2, _s3, _s4 = st.columns(4)
                _s1.metric("Best Win %",   f"{_r5s_best['team_abbr']}  {_r5s_best['win_pct']*100:.1f}%")
                _s2.metric("Most Wins",    f"{_r5s_most['team_abbr']}  {int(_r5s_most['wins'])}W")
                _s3.metric("Best Pt Diff", f"{_r5s_diff['team_abbr']}  {_r5s_diff['diff']:+.1f}")
                _s4.metric("Worst Win %",  f"{_r5s_worst['team_abbr']}  {_r5s_worst['win_pct']*100:.1f}%")

                _r5s_search = st.text_input(
                    "🔍 Filter teams", key=f"r5s_search_{_r5_ep}",
                    placeholder="Team name or abbreviation…",
                )
                st.divider()

                for _conf, _cdf in _r5s_df.groupby('conference'):
                    _cdf = _cdf.sort_values('win_pct', ascending=False)
                    if _r5s_search:
                        _cdf = _cdf[
                            _cdf['team_name'].str.contains(_r5s_search, case=False, na=False) |
                            _cdf['team_abbr'].str.contains(_r5s_search, case=False, na=False)
                        ]
                    if _cdf.empty:
                        continue
                    st.markdown(f"**{_conf}**")
                    _show = _cdf[['team_abbr', 'team_name', 'wins', 'losses']].copy()
                    _show['W%']  = (_cdf['win_pct'] * 100).round(1)
                    _show['GB']  = _cdf['gb']
                    if _cdf['ot_losses'].sum() > 0:
                        _show['OTL'] = _cdf['ot_losses'].astype(int)
                    if _cdf['ppg'].sum() > 0:
                        _show['PPG']  = _cdf['ppg'].round(1)
                        _show['OPP']  = _cdf['opp_ppg'].round(1)
                        _show['DIFF'] = _cdf['diff'].round(1)
                    if _cdf['pts'].sum() > 0:
                        _show['PTS']  = _cdf['pts'].astype(int)
                    if _cdf['streak'].apply(bool).any():
                        _show['Streak'] = _cdf['streak']
                    if _cdf['playoff_seed'].sum() > 0:
                        _show['Seed'] = _cdf['playoff_seed'].astype(int)
                    _show = _show.rename(columns={
                        'team_abbr': 'Abbr', 'team_name': 'Team',
                        'wins': 'W', 'losses': 'L',
                    })

                    def _r5s_hl(s):
                        if s.name == 'W%':
                            top = s.max()
                            return ['background-color:#d4edda;font-weight:bold'
                                    if v == top else '' for v in s]
                        if s.name == 'DIFF':
                            return ['color:#1a8a1a' if v > 0 else
                                    'color:#c0392b' if v < 0 else ''
                                    for v in s]
                        return ['' for _ in s]

                    st.dataframe(_show.style.apply(_r5s_hl),
                                 use_container_width=True, hide_index=True)

                st.divider()

                # ── Chart row 1: Wins + Win% ──────────────────
                _sc1, _sc2 = st.columns(2)
                with _sc1:
                    _srt = _r5s_df.sort_values('wins', ascending=False)
                    _cfig = go.Figure(go.Bar(
                        x=_srt['team_abbr'], y=_srt['wins'],
                        marker=dict(color=[_r5_safe_color(c) for c in _srt['team_color']], line=dict(width=0)),
                        text=_srt['wins'].astype(int), textposition='outside', textfont=dict(size=10),
                        hovertemplate='<b>%{x}</b><br>Wins: <b>%{y}</b><extra></extra>',
                    ))
                    _cfig.update_layout(**_r5_base_layout(
                        title=dict(text='🏆 Wins by Team', font=dict(size=13)),
                        height=380,
                        xaxis=dict(tickangle=-45, tickfont=dict(size=10), **_R5_AXIS),
                        yaxis=dict(**_R5_AXIS),
                        margin=dict(t=50, b=90, l=30, r=10), showlegend=False,
                    ))
                    st.plotly_chart(_cfig, use_container_width=True)

                with _sc2:
                    _wpct = _r5s_df.sort_values('win_pct', ascending=False)
                    _wfig = go.Figure(go.Bar(
                        x=_wpct['team_abbr'],
                        y=(_wpct['win_pct'] * 100).round(1),
                        marker=dict(color=[_r5_safe_color(c) for c in _wpct['team_color']], line=dict(width=0)),
                        text=(_wpct['win_pct'] * 100).round(1).astype(str) + '%',
                        textposition='outside', textfont=dict(size=10),
                        hovertemplate='<b>%{x}</b><br>Win%%: <b>%{y:.1f}%%</b><extra></extra>',
                    ))
                    _wfig.update_layout(**_r5_base_layout(
                        title=dict(text='📊 Win % by Team', font=dict(size=13)),
                        height=380,
                        xaxis=dict(tickangle=-45, tickfont=dict(size=10), **_R5_AXIS),
                        yaxis=dict(title='Win %', range=[0, 110], **_R5_AXIS),
                        margin=dict(t=50, b=90, l=30, r=10), showlegend=False,
                    ))
                    st.plotly_chart(_wfig, use_container_width=True)

                # ── Chart row 2: PPG scatter + Pt-diff bar ────
                _sc3, _sc4 = st.columns(2)
                if _r5s_df['ppg'].sum() > 0:
                    with _sc3:
                        _avg_ppg = _r5s_df['ppg'].mean()
                        _avg_opp = _r5s_df['opp_ppg'].mean()
                        _ppg_max = _r5s_df['ppg'].max()
                        _opp_min = _r5s_df['opp_ppg'].min()
                        _ppg_min = _r5s_df['ppg'].min()
                        _opp_max = _r5s_df['opp_ppg'].max()
                        _sfig = go.Figure(go.Scatter(
                            x=_r5s_df['opp_ppg'], y=_r5s_df['ppg'],
                            mode='markers+text',
                            marker=dict(
                                color=[_r5_safe_color(c) for c in _r5s_df['team_color']],
                                size=15, line=dict(width=1.5, color='rgba(0,0,0,0.25)'), opacity=0.88,
                            ),
                            text=_r5s_df['team_abbr'], textposition='top center',
                            textfont=dict(size=10, color='#222'),
                            hovertemplate='<b>%{text}</b><br>PPG: <b>%{y:.1f}</b><br>Opp PPG: <b>%{x:.1f}</b><extra></extra>',
                        ))
                        _sfig.add_hline(y=_avg_ppg, line_dash='dot',
                                        line_color='rgba(100,100,100,0.5)',
                                        annotation_text='Avg PPG', annotation_font_size=10)
                        _sfig.add_vline(x=_avg_opp, line_dash='dot',
                                        line_color='rgba(100,100,100,0.5)',
                                        annotation_text='Avg OPP', annotation_font_size=10)
                        _sfig.add_annotation(x=_opp_min + (_avg_opp - _opp_min)*0.5,
                                             y=_ppg_max, text='ELITE',
                                             font=dict(size=11, color='rgba(39,174,96,0.5)'), showarrow=False)
                        _sfig.add_annotation(x=_opp_max - (_opp_max - _avg_opp)*0.5,
                                             y=_ppg_min + 0.5, text='REBUILD',
                                             font=dict(size=11, color='rgba(231,76,60,0.5)'), showarrow=False)
                        _sfig.update_layout(**_r5_base_layout(
                            title=dict(text='🎯 Offense vs Defense', font=dict(size=13)),
                            height=420,
                            xaxis=dict(title='Opp PPG  ◀ better defense', **_R5_AXIS),
                            yaxis=dict(title='PPG  ▲ better offense', **_R5_AXIS),
                            margin=dict(t=50, b=55, l=60, r=10),
                        ))
                        st.plotly_chart(_sfig, use_container_width=True)

                    with _sc4:
                        _ddf = _r5s_df.sort_values('diff', ascending=False)
                        _dcols = ['#27ae60' if v >= 0 else '#e74c3c' for v in _ddf['diff']]
                        _dfig = go.Figure(go.Bar(
                            x=_ddf['team_abbr'], y=_ddf['diff'],
                            marker=dict(color=_dcols, line=dict(width=0)),
                            text=_ddf['diff'].round(1), textposition='outside',
                            textfont=dict(size=10),
                            hovertemplate='<b>%{x}</b><br>Pt Diff: <b>%{y:+.1f}</b><extra></extra>',
                        ))
                        _dfig.add_hline(y=0, line_color='rgba(0,0,0,0.3)', line_width=1.5)
                        _dfig.update_layout(**_r5_base_layout(
                            title=dict(text='📉 Point Differential', font=dict(size=13)),
                            height=420,
                            xaxis=dict(tickangle=-45, tickfont=dict(size=10), **_R5_AXIS),
                            yaxis=dict(**_R5_AXIS),
                            margin=dict(t=50, b=90, l=35, r=10), showlegend=False,
                        ))
                        st.plotly_chart(_dfig, use_container_width=True)

            # ══════════════════════════════════════════════════
            # SECTION C — ANIMATED SEASON REPLAY  🎬
            # ══════════════════════════════════════════════════
            st.markdown("### 🎬 Season Replay — Game by Game")
            st.caption(
                "Pick any team and watch their season unfold game-by-game "
                "with a live record tracker. Use the slider or Play button."
            )

            _r5c_teams_df = db.get_teams_df(_r5_ep)
            if _r5c_teams_df.empty:
                st.info(
                    "No team roster loaded for this league. "
                    "Go to the **🏟 Teams** tab, select this league, "
                    "click **🔄 Load Teams**, then return here."
                )
            else:
                _r5c_c1, _r5c_c2, _r5c_c3 = st.columns([4, 1, 1])
                with _r5c_c1:
                    _r5c_team_opts = {
                        str(r['team_id']): f"{r['team_abbr']}  —  {r['team_name']}"
                        for _, r in _r5c_teams_df.iterrows()
                    }
                    _r5c_ids = list(_r5c_team_opts.keys())
                    _r5c_sel_id = st.selectbox(
                        "Team", _r5c_ids,
                        format_func=lambda x: _r5c_team_opts.get(x, x),
                        key="r5c_team_id",
                    )
                import datetime as _dt2
                _r5c_cur_yr = _dt2.datetime.now().year
                with _r5c_c2:
                    _r5c_season = st.selectbox(
                        "Season",
                        list(range(_r5c_cur_yr, _r5c_cur_yr - 5, -1)),
                        key="r5c_season",
                    )
                with _r5c_c3:
                    st.write("")
                    if st.button("🔄 Load Schedule", key="r5c_load"):
                        with st.spinner("Fetching schedule…"):
                            worker.fetch_team_schedule(
                                _r5_cat, _r5_spt, _r5c_sel_id, _r5c_season)
                        st.rerun()

                _r5c_row   = _r5c_teams_df[_r5c_teams_df['team_id'].astype(str) == str(_r5c_sel_id)]
                _r5c_abbr  = _r5c_row.iloc[0]['team_abbr']  if not _r5c_row.empty else _r5c_sel_id
                _r5c_name  = _r5c_row.iloc[0]['team_name']  if not _r5c_row.empty else _r5c_sel_id
                _r5c_color = _r5_safe_color(
                    '#' + str(_r5c_row.iloc[0].get('color', '') or '1a73e8')
                    if not _r5c_row.empty else '', '#1a73e8')

                _r5c_sched = db.get_team_schedule_games(
                    _r5_cat, _r5_spt, _r5c_sel_id, _r5c_season)
                _r5c_done = (
                    pd.DataFrame() if _r5c_sched.empty
                    else _r5c_sched[_r5c_sched['completed']]
                    .sort_values('date').reset_index(drop=True)
                )

                if _r5c_done.empty:
                    st.info(
                        f"No completed games found for **{_r5c_name}** "
                        f"({_r5c_season}). Click **🔄 Load Schedule** above."
                    )
                else:
                    _r5c_done = _r5c_done.copy()
                    _r5c_done['game_num']   = range(1, len(_r5c_done) + 1)
                    _r5c_done['col']        = _r5c_done['won'].map({True: '#27ae60', False: '#e74c3c'})
                    _r5c_done['result_str'] = _r5c_done['won'].map({True: 'WIN ✓', False: 'LOSS ✗'})
                    _r5c_done['ha_str']     = _r5c_done['home_away'].map({'H': 'Home', 'A': 'Away'})
                    _r5c_done['date_str']   = (
                        _r5c_done['date'].dt.strftime('%b %d')
                        if hasattr(_r5c_done['date'], 'dt')
                        else _r5c_done['date'].astype(str)
                    )
                    _r5c_n       = len(_r5c_done)
                    _r5c_max_abs = max(abs(_r5c_done['diff'].max()),
                                       abs(_r5c_done['diff'].min()), 1) * 1.35

                    # ── bar trace builder ─────────────────────
                    def _r5c_trace(sub):
                        _cd = sub[['opponent', 'my_score', 'opp_score',
                                   'result_str', 'ha_str', 'date_str']].values
                        return go.Bar(
                            x=sub['game_num'].tolist(),
                            y=sub['diff'].tolist(),
                            marker=dict(
                                color=sub['col'].tolist(),
                                line=dict(width=0),
                                opacity=0.88,
                            ),
                            text=sub['opponent'].tolist(),
                            textposition='outside',
                            textfont=dict(size=9, color='#444'),
                            customdata=_cd,
                            hovertemplate=(
                                '<b>Game %{x}</b>  ·  %{customdata[5]}<br>'
                                'vs <b>%{customdata[0]}</b>  (%{customdata[4]})<br>'
                                'Score: <b>%{customdata[1]:.0f}–%{customdata[2]:.0f}</b><br>'
                                '<b>%{customdata[3]}</b>  Margin: %{y:+.0f}'
                                '<extra></extra>'
                            ),
                            showlegend=False,
                            name='',
                        )

                    # ── build one frame per game ───────────────
                    _r5c_frames = []
                    for _fi in range(1, _r5c_n + 1):
                        _sub = _r5c_done.iloc[:_fi]
                        _w   = int(_sub['won'].sum())
                        _l   = int((~_sub['won']).sum())
                        _pct = _w / (_w + _l) * 100 if (_w + _l) > 0 else 0
                        _r5c_frames.append(go.Frame(
                            data=[_r5c_trace(_sub)],
                            layout=go.Layout(
                                title_text=(
                                    f"🎬  {_r5c_name}  |  "
                                    f"Game {_fi} / {_r5c_n}  ·  "
                                    f"Record: {_w}W – {_l}L  ({_pct:.0f}%)"
                                ),
                            ),
                            name=str(_fi),
                        ))

                    # ── animated figure ────────────────────────
                    _r5c_fig = go.Figure(
                        data=[_r5c_trace(_r5c_done.iloc[:1])],
                        frames=_r5c_frames,
                    )
                    _r5c_fig.update_layout(
                        title=dict(
                            text=(f"🎬  {_r5c_name}  ·  Season {_r5c_season}  "
                                  f"|  Click ▶ Play to watch the season unfold"),
                            font=dict(size=14, color='#1a1a2e',
                                      family="'Segoe UI',Arial,sans-serif"),
                        ),
                        height=490,
                        paper_bgcolor='rgba(0,0,0,0)',
                        plot_bgcolor='rgba(246,248,252,1)',
                        font=_R5_FONT,
                        hoverlabel=_R5_HOVER,
                        xaxis=dict(
                            title='Game #',
                            dtick=max(1, _r5c_n // 16),
                            range=[0, _r5c_n + 2],
                            **_R5_AXIS,
                        ),
                        yaxis=dict(
                            title='Point Margin',
                            range=[-_r5c_max_abs, _r5c_max_abs],
                            **_R5_AXIS,
                        ),
                        shapes=[dict(
                            type='line', x0=0, x1=1, xref='paper',
                            y0=0, y1=0, yref='y',
                            line=dict(color='rgba(80,80,80,0.4)', width=1.5, dash='dot'),
                        )],
                        updatemenus=[dict(
                            type='buttons',
                            showactive=False,
                            y=1.16, x=0.62, xanchor='left',
                            direction='left',
                            pad=dict(t=0, r=8),
                            bgcolor='rgba(246,248,252,0.95)',
                            bordercolor='rgba(0,0,0,0.12)',
                            font=dict(size=13),
                            buttons=[
                                dict(
                                    label='  ▶  Play  ',
                                    method='animate',
                                    args=[None, dict(
                                        frame=dict(duration=450, redraw=True),
                                        fromcurrent=True,
                                        transition=dict(duration=200,
                                                        easing='cubic-in-out'),
                                    )],
                                ),
                                dict(
                                    label='  ⏸  Pause  ',
                                    method='animate',
                                    args=[[None], dict(
                                        frame=dict(duration=0, redraw=False),
                                        mode='immediate',
                                        transition=dict(duration=0),
                                    )],
                                ),
                            ],
                        )],
                        sliders=[dict(
                            active=0,
                            currentvalue=dict(
                                prefix='Game ',
                                visible=True,
                                xanchor='center',
                                font=dict(size=12, color='#444'),
                            ),
                            pad=dict(b=15, t=55),
                            bgcolor='rgba(240,240,240,0.7)',
                            bordercolor='rgba(0,0,0,0.1)',
                            tickcolor='rgba(0,0,0,0.2)',
                            font=dict(size=9, color='#666'),
                            steps=[
                                dict(
                                    method='animate',
                                    args=[[str(_si + 1)], dict(
                                        mode='immediate',
                                        frame=dict(duration=0, redraw=True),
                                        transition=dict(duration=0),
                                    )],
                                    label=str(_si + 1),
                                )
                                for _si in range(_r5c_n)
                            ],
                        )],
                        margin=dict(t=110, b=80, l=55, r=20),
                    )
                    st.plotly_chart(_r5c_fig, use_container_width=True)

                    # ── Season summary metrics ─────────────────
                    st.divider()
                    _r5c_wins_total = int(_r5c_done['won'].sum())
                    _r5c_loss_total = int((~_r5c_done['won']).sum())
                    _r5c_avg_diff   = _r5c_done['diff'].mean()
                    _r5c_biggest_w  = (
                        _r5c_done[_r5c_done['won']]['diff'].max()
                        if _r5c_done['won'].any() else float('nan')
                    )
                    _sm1, _sm2, _sm3, _sm4 = st.columns(4)
                    _sm1.metric("Final Record",
                                f"{_r5c_wins_total}W – {_r5c_loss_total}L")
                    _sm2.metric("Win %",
                                f"{_r5c_wins_total / _r5c_n * 100:.1f}%")
                    _sm3.metric("Avg Margin", f"{_r5c_avg_diff:+.1f}")
                    _sm4.metric("Biggest Win",
                                f"+{_r5c_biggest_w:.0f}"
                                if not pd.isna(_r5c_biggest_w) else "N/A")

                    # ── Static breakdown charts ────────────────
                    _r5c_bc1, _r5c_bc2 = st.columns(2)

                    with _r5c_bc1:
                        # W-L stacked bar vs each opponent
                        _opp_grp = (
                            _r5c_done.groupby('opponent')['won']
                            .agg(W='sum', L=lambda x: (~x).sum())
                            .reset_index()
                            .sort_values('W', ascending=True)
                        )
                        _opp_fig = go.Figure()
                        _opp_fig.add_trace(go.Bar(
                            x=_opp_grp['W'], y=_opp_grp['opponent'],
                            orientation='h', name='WIN',
                            marker=dict(color='#27ae60', line=dict(width=0)),
                            hovertemplate='<b>%{y}</b><br>Wins: <b>%{x}</b><extra></extra>',
                        ))
                        _opp_fig.add_trace(go.Bar(
                            x=_opp_grp['L'], y=_opp_grp['opponent'],
                            orientation='h', name='LOSS',
                            marker=dict(color='#e74c3c', line=dict(width=0)),
                            hovertemplate='<b>%{y}</b><br>Losses: <b>%{x}</b><extra></extra>',
                        ))
                        _opp_fig.update_layout(**_r5_base_layout(
                            title=dict(text='W-L vs Each Opponent', font=dict(size=13)),
                            barmode='stack',
                            height=max(300, len(_opp_grp) * 22 + 80),
                            xaxis=dict(title='Games', **_R5_AXIS),
                            yaxis=dict(autorange='reversed', tickfont=dict(size=10), **_R5_AXIS),
                            legend=dict(orientation='h', y=1.08, font=dict(size=11)),
                            margin=dict(t=55, b=30, l=90, r=10),
                        ))
                        st.plotly_chart(_opp_fig, use_container_width=True)

                    with _r5c_bc2:
                        # Home vs Away W/L grouped bar
                        _ha_grp = (_r5c_done.groupby(['home_away', 'won'])
                                   .size().reset_index(name='count'))
                        _ha_fig = go.Figure()
                        for _ha_loc, _ha_color, _ha_won in [
                            ('H', '#27ae60', True), ('H', '#a8e0b1', False),
                            ('A', '#3498db', True), ('A', '#f1a9a0', False),
                        ]:
                            _sub2 = _ha_grp[(_ha_grp['home_away'] == _ha_loc) &
                                            (_ha_grp['won'] == _ha_won)]
                            _cnt  = int(_sub2['count'].sum()) if not _sub2.empty else 0
                            _lbl  = ('Home' if _ha_loc == 'H' else 'Away') + (
                                ' WIN' if _ha_won else ' LOSS')
                            _ha_fig.add_trace(go.Bar(
                                x=[_lbl], y=[_cnt], name=_lbl,
                                marker=dict(color=_ha_color, line=dict(width=0)),
                                text=[_cnt], textposition='outside',
                                textfont=dict(size=12),
                                hovertemplate=(
                                    f'<b>{_lbl}</b><br>Games: {_cnt}<extra></extra>'
                                ),
                            ))
                        _ha_fig.update_layout(**_r5_base_layout(
                            title=dict(text='Home vs Away Performance',
                                       font=dict(size=13)),
                            barmode='group', height=360,
                            xaxis=dict(**_R5_AXIS),
                            yaxis=dict(title='Games', **_R5_AXIS),
                            legend=dict(orientation='h', y=-0.25,
                                        font=dict(size=10)),
                            margin=dict(t=55, b=80, l=40, r=10),
                            showlegend=True,
                        ))
                        st.plotly_chart(_ha_fig, use_container_width=True)

                    # ── Rolling 5-game scoring trend ──────────
                    _r5c_roll = _r5c_done.copy()
                    _r5c_roll['roll_pts'] = (
                        _r5c_roll['my_score'].rolling(5, min_periods=1).mean())
                    _r5c_roll['roll_opp'] = (
                        _r5c_roll['opp_score'].rolling(5, min_periods=1).mean())
                    _rl_fig = go.Figure()
                    _rl_fig.add_trace(go.Scatter(
                        x=_r5c_roll['game_num'], y=_r5c_roll['roll_pts'],
                        name=f'{_r5c_abbr} (rolling 5)',
                        mode='lines+markers',
                        line=dict(color=_r5c_color, width=2.5, shape='spline'),
                        marker=dict(size=6, color=_r5c_color,
                                    line=dict(width=1.5, color='white')),
                        hovertemplate=(
                            'Game %{x}<br>'
                            f'{_r5c_abbr} rolling PPG: <b>%{{y:.1f}}</b>'
                            '<extra></extra>'
                        ),
                    ))
                    _rl_fig.add_trace(go.Scatter(
                        x=_r5c_roll['game_num'], y=_r5c_roll['roll_opp'],
                        name='Opponent (rolling 5)',
                        mode='lines+markers',
                        line=dict(color='#e74c3c', width=2.5,
                                  shape='spline', dash='dot'),
                        marker=dict(size=6, color='#e74c3c',
                                    line=dict(width=1.5, color='white')),
                        hovertemplate=(
                            'Game %{x}<br>'
                            'Opp rolling PPG: <b>%{y:.1f}</b>'
                            '<extra></extra>'
                        ),
                    ))
                    _rl_fig.update_layout(**_r5_base_layout(
                        title=dict(
                            text=f'📈 {_r5c_name} — Rolling 5-Game Scoring Trend',
                            font=dict(size=13)),
                        height=340,
                        xaxis=dict(title='Game #', **_R5_AXIS),
                        yaxis=dict(title='Points (rolling avg)', **_R5_AXIS),
                        legend=dict(orientation='h', y=1.12, font=dict(size=11)),
                        margin=dict(t=65, b=40, l=55, r=10),
                    ))
                    st.plotly_chart(_rl_fig, use_container_width=True)

    # ── TAB 6: NETWORK / COORDINATOR ─────────────────────────"""

# Find and replace
old_chunk_start = content.find(OLD_START)
old_chunk_end   = content.find(OLD_END) + len(OLD_END.split('\n\n')[0]) + \
                  len('\n\n    # \u2500\u2500 TAB 6: NETWORK / COORDINATOR')

# Simpler: find the end marker exactly
tab6_marker = "\n\n    # \u2500\u2500 TAB 6: NETWORK / COORDINATOR \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500"
tab6_pos = content.find(tab6_marker)
assert tab6_pos != -1, "Could not find TAB 6 marker"

new_content = content[:old_chunk_start] + new_sections + content[tab6_pos:]
open('sporting.py', 'w', encoding='utf-8').write(new_content)
print(f"Replaced {tab6_pos - old_chunk_start} chars. New file length: {len(new_content)}")

"""Streamlit page for the NFL simulation engine: live engine-vs-actual play grading,
simulated slate, player matchups and the nightly tuning job."""
import time
from typing import Optional

import pandas as pd
import streamlit as st

REFRESH_SECONDS = 20
_KIND = {"run": "Run", "comp": "Pass complete", "inc": "Pass incomplete", "sack": "Sack",
         "int": "Interception", "punt": "Punt", "fg": "Field goal"}


def _pct(x: Optional[float], d: int = 0) -> str:
    return "–" if x is None or x != x else f"{100 * x:.{d}f}%"


def _num(x: Optional[float], d: int = 1) -> str:
    return "–" if x is None or x != x else f"{x:.{d}f}"


@st.cache_resource(show_spinner=False)
def _runtime():
    """Process-wide engine: loads the model and ratings in a background thread and starts the nightly job."""
    from nfl_engine.runtime import RT
    RT.ensure()
    RT.scheduler.start()
    return RT


def _ready(rt) -> bool:
    rt.ensure()
    if rt.state == "ready":
        return True
    if rt.state == "loading":
        st.info("Engine is loading ratings (about a minute after a restart)…")
        time.sleep(3)
        st.rerun()
    st.error(rt.error or f"Engine state: {rt.state}")
    return False


# ── Live ──────────────────────────────────────────────────────

@st.cache_data(ttl=15, show_spinner=False)
def _scoreboard():
    from nfl_engine import liveplay
    return liveplay.scoreboard()


def _game_label(g) -> str:
    when = f"Q{g['period']} {g['clock']}" if g["state"] == "in" else (g.get("detail") or g.get("status") or "")
    return f"{g['away']} {g['away_score']} @ {g['home']} {g['home_score']} — {when}"


def _summary_table(s: dict) -> None:
    rows = [("Pass rate", s.get("pass_rate_pred"), s.get("pass_rate_act"), True),
            ("Yards per play", s.get("yards_pred"), s.get("yards_act"), False),
            ("First-down / TD rate", s.get("first_pred"), s.get("first_act"), True),
            ("Completion %", s.get("comp_pred"), s.get("comp_act"), True),
            ("Sack % of dropbacks", s.get("sack_pred"), s.get("sack_act"), True),
            ("Turnovers (total)", s.get("to_pred"), s.get("to_act"), False)]
    df = pd.DataFrame([{
        f"Whole-game check ({s['n']} plays)": lab,
        "Engine expected": _pct(e, 1) if p else _num(e, 2),
        "Live actual": _pct(a, 1) if p else _num(a, 2),
        "Gap": "–" if e is None or a is None else (f"{100 * (a - e):+.1f} pts" if p else f"{a - e:+.2f}"),
    } for lab, e, a, p in rows])
    st.dataframe(df, hide_index=True, use_container_width=True)
    st.caption(f"Calibration: {_pct(s.get('pit_lo10'))} of plays gained fewer yards than the engine's 10th "
               f"percentile and {_pct(s.get('pit_hi10'))} more than its 90th. A well-calibrated engine shows about 10% each.")


def _play_rows(plays: list) -> pd.DataFrame:
    out = []
    for p in plays:
        pr = p.get("pred")
        if not pr:
            continue
        sc = p.get("score") or {}
        dec = pr.get("dec")
        eng = f"pass {_pct(pr['p_pass'])} · exp {_num(pr['exp_yards'])} yds ({_num(pr['y_p10'], 0)}…{_num(pr['y_p90'], 0)}) · 1st/TD {_pct(pr['p_first'])}"
        if dec:
            eng += f" · 4th: go {_pct(dec['go'])} punt {_pct(dec['punt'])} FG {_pct(dec['fg'])}"
        act = _KIND.get(p["cat"], p["cat"])
        if p["cat"] not in ("punt", "fg"):
            act += f" · {p.get('yards') or 0} yds" + (" · conversion" if sc.get("converted") else "") + (" · TD" if p.get("td") else "")
        if dec and sc.get("dec_actual"):
            act += f" (4th: {sc['dec_actual']})"
        sur = sc.get("surprise") or 0
        out.append({"Clock": f"Q{p['period']} {p['clock']}", "Situation": f"{p['off']} {p['down']}&{p['ytg']} @{p['yl']}",
                    "Play": p["text"], "ENGINE (pre-snap)": eng, "LIVE (actual)": act,
                    "Yard pct": None if sc.get("yard_pct") is None else round(100 * sc["yard_pct"]),
                    "Surprise": round(sur, 1), "_hot": sur})
    return pd.DataFrame(out)


def _live_body(rt) -> None:
    from nfl_engine import liveplay
    games = _scoreboard()
    if not games:
        st.info("No NFL games on the ESPN scoreboard right now.")
        return
    started = [g for g in games if g["state"] in ("in", "post")]
    st.caption(f"{sum(g['state'] == 'in' for g in games)} live · {sum(g['state'] == 'post' for g in games)} final · "
               f"{sum(g['state'] == 'pre' for g in games)} upcoming · updated {time.strftime('%H:%M:%S')}")
    if not started:
        st.dataframe(pd.DataFrame([{"Game": f"{g['away']} @ {g['home']}", "Status": g.get("detail") or g.get("status")}
                                   for g in games]), hide_index=True, use_container_width=True)
        return
    default = next((i for i, g in enumerate(started) if g["state"] == "in"), 0)
    g = started[st.selectbox("Game", range(len(started)), index=default, format_func=lambda i: _game_label(started[i]),
                             key="nfl_game")]
    try:
        row, spec, pred = rt.predictor(g["home"], g["away"], g["start"])
    except Exception as exc:  # noqa: BLE001
        st.warning(f"No engine prediction for this game: {exc}")
        return
    log = liveplay.process_event(g["event"], pred, spec, g["home"])
    summ = liveplay.summarize_log(log)
    c1, c2, c3 = st.columns(3)
    if g["state"] == "in":
        c1.metric("Engine home win", _pct(liveplay.live_win_prob(rt.bundle.league, spec, log["_plays_parsed"], 250)))
        try:
            wp = liveplay._get(f"{liveplay.ESPN}/summary?event={g['event']}", 20).get("winprobability") or []
            c2.metric("ESPN home win", _pct(wp[-1]["homeWinPercentage"]) if wp else "–")
        except Exception:  # noqa: BLE001
            c2.metric("ESPN home win", "–")
    c3.metric("Plays graded", summ.get("n", 0), f"avg surprise {_num(summ.get('mean_surprise'), 2)}")
    if summ.get("n"):
        _summary_table(summ)
    plays = sorted(log["plays"].values(), key=lambda p: -p["seq"])[:300]
    df = _play_rows(plays)
    if df.empty:
        st.caption("No graded plays yet.")
        return
    hot = df.pop("_hot")
    st.dataframe(df.style.apply(lambda r: ["background-color: rgba(240,113,120,.18)" if hot[r.name] > 2.3 else
                                           "background-color: rgba(240,180,41,.12)" if hot[r.name] > 1.5 else "" for _ in r], axis=1),
                 hide_index=True, use_container_width=True, height=520)


@st.fragment(run_every=REFRESH_SECONDS)
def _live_fragment(rt) -> None:
    _live_body(rt)


# ── Slate ─────────────────────────────────────────────────────

def _slate_tab(rt) -> pd.DataFrame:
    with st.spinner("Simulating the slate (first load can take ~30s)…"):
        df = rt.slate()
    if df.empty:
        st.info("No unplayed games on the schedule.")
        return df
    show = pd.DataFrame({
        "Day": df["day"].astype(str), "Matchup": df["away"] + " @ " + df["home"],
        "QBs": df["away_qb"].astype(str) + " / " + df["home_qb"].astype(str),
        "Proj": df["proj_away"].round(0).astype(int).astype(str) + "–" + df["proj_home"].round(0).astype(int).astype(str),
        "Home win": (100 * df["p_home"]).round(0).astype(int).astype(str) + "%",
        "Mkt spread": df["market_spread"], "Model spread": df["model_spread"].round(1),
        "Edge": df["edge_spread"].round(1), "Mkt total": df["market_total"], "Model total": df["model_total"].round(1),
        "Flags": df["flags"].map(lambda f: ", ".join(f)),
    })
    st.dataframe(show, hide_index=True, use_container_width=True)
    st.caption("Calibrated Monte-Carlo projections vs the market. Exploratory analytics, not betting advice.")
    return df


# ── Players ───────────────────────────────────────────────────

def _stat(res: dict, pid: str, key: str, d: int = 1) -> str:
    p = next((x for x in res["players"] if x["id"] == pid), None)
    s = (p or {}).get("stats", {})
    return _num(s[key]["mean"], d) if key in s and s[key] else "0.0"


def _players_tab(rt, slate: pd.DataFrame) -> None:
    from nfl_engine.players import project_players
    if slate.empty:
        return
    games = {f"{r.away} @ {r.home} ({r.day})": (r.home, r.away) for r in slate.itertuples()}
    home, away = games[st.selectbox("Game", list(games), key="nfl_pg")]
    _row, spec, _p = rt.predictor(home, away)
    teams = {t: rt.players.teams.get(t) for t in (home, away)}
    if not all(teams.values()):
        st.warning("Roster data is not available for this game.")
        return
    out = [f"{o['name']} ({t}, {o['reason']})" for t in (home, away) for o in teams[t].out]
    if out:
        st.caption("Out / unavailable: " + " · ".join(out))
    recs = [(x, t) for t in (home, away) for x in teams[t].rec]
    c1, c2 = st.columns(2)
    sel = recs[c1.selectbox("Offensive player", range(len(recs)), key="nfl_pl",
                            format_func=lambda i: f"{recs[i][0].name} ({recs[i][0].pos}, {recs[i][1]}) – {_pct(recs[i][0].w)} of targets")]
    star, off_team = sel
    def_team = away if off_team == home else home
    defs = [None] + list(teams[def_team].defs)
    d = defs[c2.selectbox("Defender to shadow him", range(len(defs)), key="nfl_def",
                          format_func=lambda i: "(no assigned defender – team coverage)" if defs[i] is None else
                          f"{defs[i].name} ({defs[i].pos}, {def_team}) – PBU {_pct(defs[i].pbu_w)}, INT {_pct(defs[i].int_w)}")]
    c3, c4 = st.columns(2)
    force = c3.select_slider("His share of his team's targets", [0.15, 0.2, 0.25, 0.3, 0.4], value=0.25, format_func=lambda x: f"{x:.0%}")
    sims = c4.select_slider("Simulations", [200, 400, 800], value=400)
    if not st.button("Simulate matchup", type="primary"):
        return
    qbs = (_row.home_qb_name or "QB", _row.away_qb_name or "QB")
    with st.spinner(f"Simulating {sims} games twice (baseline vs spotlight)…"):
        base = project_players(rt.bundle.league, spec, rt.players, home, away, qbs, n=sims, seed=1)
        side = 0 if off_team == home else 1
        focus = project_players(rt.bundle.league, spec, rt.players, home, away, qbs, n=sims, seed=1,
                                override={side: star.id}, shadow={1 - side: d.id} if d else {}, force=force)
    rows = [("Targets", "targets", 1), ("Receptions", "rec", 1), ("Receiving yards", "rec_yds", 1),
            ("Receiving TD", "rec_td", 2), ("Carries", "car", 1), ("Rushing yards", "rush_yds", 1)]
    st.markdown(f"#### {star.name}: baseline vs spotlight")
    st.dataframe(pd.DataFrame([{"Stat per game": l, "Baseline": _stat(base, star.id, k, dp), "Spotlight": _stat(focus, star.id, k, dp)}
                               for l, k, dp in rows]), hide_index=True, use_container_width=True)
    if d:
        st.markdown(f"#### {d.name} (shadowing)")
        st.dataframe(pd.DataFrame([{"Stat per game": l, "Baseline": _stat(base, d.id, k, 2), "Matchup": _stat(focus, d.id, k, 2)}
                                   for l, k in (("Pass breakups", "pbu"), ("Interceptions", "ints"), ("Sacks", "sacks"))]),
                     hide_index=True, use_container_width=True)
        st.caption("Defender impact is inferred from sack / PBU / INT share (public data has no coverage tracking). Directional only.")

    def tot(p, k):
        return (p["stats"].get(k) or {}).get("mean", 0) or 0
    top = sorted((p for p in base["players"] if p["stats"].get("targets") or p["stats"].get("car") or p["stats"].get("att")),
                 key=lambda p: -(tot(p, "rec_yds") + tot(p, "rush_yds") + tot(p, "pass_yds")))[:14]
    st.markdown(f"#### Projected player lines ({away} @ {home}, avg {_num(base['score']['away'], 0)}–{_num(base['score']['home'], 0)})")
    st.dataframe(pd.DataFrame([{
        "Player": p["name"], "Team": p["team"], "Pos": p["role"], "Pass yds": _num(tot(p, "pass_yds"), 0) if tot(p, "pass_yds") else "",
        "Comp/Att": f"{_num(tot(p, 'comp'))}/{_num(tot(p, 'att'))}" if tot(p, "att") else "",
        "Rush": f"{_num(tot(p, 'car'))} for {_num(tot(p, 'rush_yds'), 0)}" if tot(p, "car") else "",
        "Rec": f"{_num(tot(p, 'rec'))} for {_num(tot(p, 'rec_yds'), 0)}" if tot(p, "rec") else "",
        "Tgt": _num(tot(p, "targets")) if tot(p, "targets") else "",
        "TD": _num(tot(p, "rec_td") + tot(p, "rush_td") + tot(p, "pass_td"), 2)} for p in top]),
        hide_index=True, use_container_width=True)


# ── Tuning ────────────────────────────────────────────────────

def _tuning_tab(rt) -> None:
    from nfl_engine import livetune
    stt = livetune.load_state()
    st.markdown(f"Next run: **{rt.scheduler.next_run()}**" + (f" · {rt.scheduler.waiting_reason}" if rt.scheduler.waiting_reason else "")
                + (" · running…" if stt.get("running") else ""))
    st.caption(f"Last completed: {stt.get('last_run_date') or 'never'}. Runs once per night after every game on the scoreboard is final.")
    c1, c2 = st.columns([1, 3])
    hour = c1.number_input("Run hour (local, 0 = midnight)", 0, 23, int(stt.get("hour", 0)))
    if c1.button("Save hour"):
        stt["hour"] = int(hour)
        livetune.save_state(stt)
        st.rerun()
    force = c2.checkbox("Even if games are live")
    if c2.button("Run tuning now", type="primary"):
        if not force and livetune._games_active_or_pending(__import__("datetime").datetime.now()):
            st.error("Games are still in progress; tick 'Even if games are live' to tune anyway.")
        else:
            with st.spinner("Running tuning job…"):
                st.json(livetune.nightly(rt, force=True))
    st.markdown("##### Live corrections applied to every simulation")
    adj = dict(livetune.LIVE_ADJ)
    if adj:
        st.dataframe(pd.DataFrame([{"Lever": k, "Adjustment": f"{v:+.4f}"} for k, v in adj.items()]), hide_index=True)
    else:
        st.caption("No live corrections yet. The first nightly run after 30 or more graded plays creates them.")
    st.markdown("##### Run history")
    hist = (stt.get("history") or [])[::-1]
    if hist:
        st.dataframe(pd.DataFrame([{"Started": h.get("started"), "Status": h.get("status"),
                                    "Live plays used": (h.get("live") or {}).get("plays", 0),
                                    "Games added": (h.get("refresh") or {}).get("games_added_to_residuals", ""),
                                    "Seconds": h.get("seconds")} for h in hist]), hide_index=True)
    else:
        st.caption("No runs yet.")


# ── Entry point ───────────────────────────────────────────────

def render_nfl_engine_page() -> None:
    st.markdown("## 🏈 NFL Engine")
    st.caption("Play-by-play simulator trained on completed games. **Engine** columns are what the model predicted "
               "before the snap; **Live** columns are what actually happened. Every graded play feeds the nightly tuning job.")
    try:
        rt = _runtime()
    except Exception as exc:  # noqa: BLE001
        st.error(f"NFL engine unavailable: {exc}")
        return
    if not _ready(rt):
        return
    b = rt.bundle
    test = (b.report.get("test") or {}).get("sim_calibrated") or {}
    st.caption(f"Model trained through {b.train_end}"
               + (f" · held-out win accuracy {_pct(test.get('win_acc'), 1)} · margin MAE {_num(test.get('margin_mae'), 2)}" if test else "")
               + f" · loaded {rt.loaded_at}")
    t_live, t_slate, t_players, t_tune = st.tabs(["Live: engine vs actual", "Slate", "Player matchups", "Nightly tuning"])
    with t_live:
        _live_fragment(rt)
    with t_slate:
        slate = _slate_tab(rt)
    with t_players:
        _players_tab(rt, rt.slate())
    with t_tune:
        _tuning_tab(rt)

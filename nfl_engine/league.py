"""League-wide behavioural model learned from historical play-by-play.

Everything the simulator needs that is *not* team specific lives here: play-calling tendencies,
fourth-down decisions, outcome distributions by field zone and distance, kicking, penalties,
clock burn, and weather sensitivity.  Team/player/coach/opponent specifics are layered on top by
``ratings`` and ``matchup``.
"""

from __future__ import annotations

import math
from bisect import bisect_left
from dataclasses import dataclass, field

import numpy as np
import pandas as pd
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.linear_model import LinearRegression, LogisticRegression

# ---------------------------------------------------------------- shared situation helpers


TD_Y = 1000  # sentinel in yardage pools: this sample ended in a touchdown (yardage was censored by the end zone)
ZONE_EDGES = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 20, 25, 30, 35, 40, 45, 50, 60, 70, 80, 90, 99]
NZ = len(ZONE_EDGES)


def zone(yl: float) -> int:
    """Fine field-position bin: single yards near the goal line, wider bins further out."""
    return min(bisect_left(ZONE_EDGES, yl), NZ - 1)


def ytg_bucket(ytg: float) -> int:
    return 0 if ytg <= 1 else 1 if ytg <= 3 else 2 if ytg <= 7 else 3


def clock_mode(sd: float, qtr: int, hsr: float) -> int:
    """0 normal, 1 milking a lead, 2 hurry-up."""
    if qtr == 4:
        if sd < 0 and hsr <= 480:
            return 2
        if sd > 0 and hsr <= 420:
            return 1
    elif qtr == 2 and hsr <= 120:
        return 2
    return 0


def era_of(season: int) -> int:
    return 0 if season <= 2023 else 1 if season == 2024 else 2


def pc_feats(down, ytg, yl, sd, qtr, hsr, gsr, wind_ex, cold, dome):
    lt = math.log(ytg if ytg >= 1 else 1.0)
    d2, d3, d4 = down == 2, down == 3, down == 4
    sdc = max(-21.0, min(21.0, sd)) / 10.0
    trail, lead = max(0.0, -sdc), max(0.0, sdc)
    late4 = qtr == 4 and hsr <= 480
    two = qtr in (2, 4) and hsr <= 120
    tfrac = min(gsr, 3600) / 3600.0
    return [
        d2, d3, d4, lt, d2 * lt, d3 * lt, d4 * lt, yl / 100.0, yl <= ytg, sdc,
        trail * late4, lead * late4, trail * two, lead * two, sdc * (1 - tfrac),
        qtr == 2 and hsr <= 120, wind_ex, cold, dome, ytg <= 2,
    ]


def fg_feats(dist, wind_ex, cold, dome):
    return [dist, dist * dist / 100.0, wind_ex, cold, dome]


SD_VALS = np.array([-24, -16, -11, -8, -5, -3, -1, 0, 1, 3, 5, 8, 11, 16, 24])
GSR_VALS = np.array([3300, 2700, 2100, 1800, 1500, 1200, 900, 600, 420, 300, 180, 90, 30])
YTG_MAX = 15
SD_IDX = np.array([int(np.abs(SD_VALS - s).argmin()) for s in range(-30, 31)])  # sd+30 -> idx
GSR_IDX = np.array([int(np.abs(GSR_VALS - g).argmin()) for g in range(0, 3611, 10)])  # gsr//10 -> idx


# ---------------------------------------------------------------- pbp preparation


def weather_cols(df: pd.DataFrame) -> pd.DataFrame:
    dome = df["roof"].isin(["dome", "closed"]).astype(float)
    wind = df["wind"].fillna(df.loc[dome == 0, "wind"].median() if (dome == 0).any() else 5.0)
    temp = df["temp"].fillna(df.loc[dome == 0, "temp"].median() if (dome == 0).any() else 60.0)
    df["dome"] = dome
    df["wind_ex"] = np.where(dome == 1, 0.0, np.clip(wind - 8, 0, 25) / 10.0)
    df["cold"] = np.where(dome == 1, 0.0, np.clip(40 - temp, 0, 40) / 10.0)
    return df


def prepare_pbp(pbp: pd.DataFrame) -> pd.DataFrame:
    """Sort, flag play families, and derive burn/next-play columns used everywhere."""
    df = pbp[(pbp["season_type"].isin(["REG", "POST"])) & (pbp["play_deleted"].fillna(0) == 0)].copy()
    df = df.sort_values(["game_id", "play_id"]).reset_index(drop=True)
    df = weather_cols(df)
    pt = df["play_type"]
    df["scrim"] = pt.isin(["pass", "run"]) & (df["aborted_play"].fillna(0) == 0) & df["down"].notna()
    df["scramble"] = df["scrim"] & (df["qb_scramble"] == 1)
    df["dropback"] = df["scrim"] & ((df["qb_dropback"] == 1) | df["scramble"])
    df["dsg_run"] = df["scrim"] & (df["rush_attempt"] == 1) & ~df["dropback"]
    df["sacked"] = df["dropback"] & (df["sack"] == 1)
    df["att"] = df["dropback"] & (df["pass_attempt"] == 1) & ~df["sacked"] & ~df["scramble"]
    df["comp"] = df["att"] & (df["complete_pass"] == 1)
    df["is_int"] = df["att"] & (df["interception"] == 1)
    df["no_play_pen"] = (pt == "no_play") & (df["penalty"] == 1) & df["down"].notna() & df["posteam"].notna()
    df["off_pen"] = df["no_play_pen"] & (df["penalty_team"] == df["posteam"])
    df["def_pen"] = df["no_play_pen"] & (df["penalty_team"] == df["defteam"])
    g = df.groupby("game_id", sort=False)
    nxt_gsr = g["game_seconds_remaining"].shift(-1)
    nxt_drive = g["drive"].shift(-1)
    burn = df["game_seconds_remaining"] - nxt_gsr
    ok = (nxt_drive == df["drive"]) & burn.between(1, 60) & (df["qtr"] <= 4)
    df["burn"] = np.where(ok, burn, np.nan)
    df["nxt_yl"] = g["yardline_100"].shift(-1)
    df["nxt_pos"] = g["posteam"].shift(-1)
    sd = df["score_differential"].fillna(0)
    hsr = df["half_seconds_remaining"].fillna(0)
    td = (df["touchdown"] == 1) & df["scrim"] & (df["yards_gained"] >= df["yardline_100"])
    df["y_run"] = np.where(td, TD_Y, df["rushing_yards"])
    df["y_comp"] = np.where(td, TD_Y, df["passing_yards"])
    df["mode"] = [clock_mode(s, int(q) if q == q else 1, h) for s, q, h in zip(sd, df["qtr"], hsr)]
    df["zone"] = [zone(y) if y == y else NZ - 1 for y in df["yardline_100"]]
    df["ytgb"] = [ytg_bucket(y) if y == y else 3 for y in df["ydstogo"]]
    return df


# ---------------------------------------------------------------- league model


@dataclass
class League:
    pc_model: LogisticRegression | None = None
    fourth_grid: np.ndarray | None = None  # [ytg, yl, sd, gsr, 3]  (go, punt, fg)
    fg_model: LogisticRegression | None = None
    rates: dict = field(default_factory=dict)  # (zone, ytgb) -> dict(sack, scr, comp, int)
    run_pool: dict = field(default_factory=dict)
    comp_pool: dict = field(default_factory=dict)
    sack_pool: list = field(default_factory=list)
    scr_pool: dict = field(default_factory=dict)
    int_air: list = field(default_factory=list)
    int_ret: list = field(default_factory=list)
    off_pen_pool: list = field(default_factory=list)
    def_pen_pool: list = field(default_factory=list)  # (yards, auto_first_down)
    off_pen_rate: float = 0.0
    def_pen_rate: float = 0.0
    burn_pool: dict = field(default_factory=dict)  # (mode, cat) -> list
    punt_pool: dict = field(default_factory=dict)  # bin -> list of net yards
    kick_pool: dict = field(default_factory=dict)  # era -> list of receiving yardline_100
    fum_rate: float = 0.0
    xp_rate: float = 0.94
    two_rate: float = 0.48
    wx: dict = field(default_factory=dict)  # stat -> (b_wind, b_cold, b_dome)
    wx_mean: tuple = (0.0, 0.0, 0.0)
    base: dict = field(default_factory=dict)  # league-average level of each rated stat


def punt_bin(yl: float) -> int:
    return 0 if yl <= 45 else 1 if yl <= 60 else 2 if yl <= 75 else 3


def _smooth(num: float, den: float, prior: float, m: float = 40.0) -> float:
    return (num + m * prior) / (den + m)


def fit_league(pbp: pd.DataFrame, seed: int = 0, rules_pbp: pd.DataFrame | None = None) -> League:
    """Fit on ``pbp``; ``rules_pbp`` (all seasons) only feeds the kickoff-rule eras, which are public rules."""
    df = prepare_pbp(pbp)
    L = League()
    L.wx_mean = (float(df["wind_ex"].mean()), float(df["cold"].mean()), float(df["dome"].mean()))

    # ---- play-calling: P(dropback | situation, weather)
    sc = df[df["scrim"] & df["qtr"].between(1, 4)].copy()
    sc = sc[sc["score_differential"].notna() & sc["yardline_100"].notna()]
    X = np.array(
        [pc_feats(d, y, yl, sd, int(q), h, g, w, c, dm) for d, y, yl, sd, q, h, g, w, c, dm in zip(
            sc["down"], sc["ydstogo"], sc["yardline_100"], sc["score_differential"], sc["qtr"],
            sc["half_seconds_remaining"], sc["game_seconds_remaining"], sc["wind_ex"], sc["cold"], sc["dome"])],
        dtype=float)
    L.pc_model = LogisticRegression(C=5.0, max_iter=400).fit(X, sc["dropback"].astype(int))

    # ---- fourth down decisions (lookup grid)
    f4 = df[(df["down"] == 4) & df["play_type"].isin(["pass", "run", "punt", "field_goal"])]
    f4 = f4[f4["score_differential"].notna() & f4["yardline_100"].notna() & (f4["qtr"] <= 4)]
    y4 = np.where(f4["play_type"].isin(["pass", "run"]), 0, np.where(f4["play_type"] == "punt", 1, 2))
    X4 = np.c_[np.minimum(f4["ydstogo"], YTG_MAX), f4["yardline_100"], np.clip(f4["score_differential"], -28, 28),
               f4["game_seconds_remaining"]]
    hgb = HistGradientBoostingClassifier(max_iter=160, max_depth=5, min_samples_leaf=40, learning_rate=0.08,
                                         random_state=seed).fit(X4, y4)
    ytg_g, yl_g, sd_g, gsr_g = np.meshgrid(np.arange(1, YTG_MAX + 1), np.arange(1, 100), SD_VALS, GSR_VALS,
                                           indexing="ij")
    grid = hgb.predict_proba(np.c_[ytg_g.ravel(), yl_g.ravel(), sd_g.ravel(), gsr_g.ravel()])
    L.fourth_grid = grid.reshape(YTG_MAX, 99, len(SD_VALS), len(GSR_VALS), 3).astype(np.float32)

    # ---- field goals
    fg = df[(df["field_goal_attempt"] == 1) & df["field_goal_result"].notna()]
    dist = fg["kick_distance"].fillna(fg["yardline_100"] + 17)
    Xf = np.array([fg_feats(d, w, c, dm) for d, w, c, dm in zip(dist, fg["wind_ex"], fg["cold"], fg["dome"])])
    L.fg_model = LogisticRegression(C=10.0, max_iter=300).fit(Xf, (fg["field_goal_result"] == "made").astype(int))

    # ---- extra points / two-point
    xp = df[df["extra_point_attempt"] == 1]
    xp = xp[xp["season"] >= 2015]
    L.xp_rate = float((xp["extra_point_result"] == "good").mean())
    tp = df[df["two_point_attempt"] == 1]
    L.two_rate = float((tp["two_point_conv_result"] == "success").mean())

    # ---- situational rates & pools
    dbk = df[df["dropback"]]
    ov = dict(sack=dbk["sacked"].mean(), scr=dbk["scramble"].mean())
    atts = df[df["att"]]
    ov["comp"], ov["int"] = atts["comp"].mean(), atts["is_int"].mean()
    for (z, b), grp in dbk.groupby(["zone", "ytgb"]):
        a = grp[grp["att"]]
        L.rates[(z, b)] = dict(
            sack=_smooth(grp["sacked"].sum(), len(grp), ov["sack"]),
            scr=_smooth(grp["scramble"].sum(), len(grp), ov["scr"]),
            comp=_smooth(a["comp"].sum(), len(a), ov["comp"]),
            int=_smooth(a["is_int"].sum(), len(a), ov["int"], 200.0),
        )
    for z in range(NZ):
        for b in range(4):
            L.rates.setdefault((z, b), dict(ov))

    runs = df[df["dsg_run"] & df["rushing_yards"].notna()]
    cps = df[df["comp"] & df["passing_yards"].notna()]
    def pooled(frame, col, z, b):
        lo = 0
        for widen in range(0, 4):  # widen to neighbouring zones until the pool is big enough
            sel = frame[(frame["zone"] >= z - widen) & (frame["zone"] <= z + widen)]
            at = sel[sel["ytgb"] == b][col]
            if len(at) >= 80:
                return at.astype(int).tolist()
            lo = len(sel)
        return sel[col].astype(int).tolist()

    for z in range(NZ):
        for b in range(4):
            L.run_pool[(z, b)] = pooled(runs, "y_run", z, b)
            L.comp_pool[(z, b)] = pooled(cps, "y_comp", z, b)
    sacks = df[df["sacked"] & df["yards_gained"].notna()]
    L.sack_pool = sacks["yards_gained"].clip(-20, 0).astype(int).tolist()
    scr = df[df["scramble"] & ~df["sacked"] & df["rushing_yards"].notna()]
    for z in range(NZ):
        s = scr[(scr["zone"] >= z - 1) & (scr["zone"] <= z + 1)]["y_run"]
        L.scr_pool[z] = (s if len(s) >= 40 else scr["y_run"]).astype(int).tolist()
    ints = df[df["is_int"]]
    L.int_air = ints["air_yards"].fillna(10).clip(0, 50).astype(int).tolist()
    L.int_ret = ints["return_yards"].fillna(0).clip(0, 100).astype(int).tolist()
    L.fum_rate = float(df[df["scrim"]]["fumble_lost"].fillna(0).mean())

    # ---- penalties
    n_snap = float(df["scrim"].sum() + df["no_play_pen"].sum())
    L.off_pen_rate = float(df["off_pen"].sum() / n_snap)
    L.def_pen_rate = float(df["def_pen"].sum() / n_snap)
    op = df[df["off_pen"]]["penalty_yards"].fillna(5).abs().clip(5, 15)
    L.off_pen_pool = op.astype(int).tolist()
    dp = df[df["def_pen"]]
    L.def_pen_pool = list(zip(dp["penalty_yards"].fillna(5).abs().clip(0, 40).astype(int),
                              dp["first_down_penalty"].fillna(0).astype(int)))

    # ---- clock burn
    sb = df[df["scrim"] & df["burn"].notna() & (df["qb_kneel"] != 1)]
    cat = np.where(sb["sacked"], "sack", np.where(sb["dsg_run"] | sb["scramble"], "run",
                                                  np.where(sb["comp"], "comp", "inc")))
    for (m, c), grp in sb.assign(cat=cat).groupby(["mode", "cat"]):
        L.burn_pool[(int(m), c)] = grp["burn"].astype(int).tolist()
    for m in range(3):
        for c in ("sack", "run", "comp", "inc"):
            L.burn_pool.setdefault((m, c), L.burn_pool.get((0, c), [30]))
    pen_b = df[df["no_play_pen"] & df["burn"].notna()]
    L.burn_pool[(0, "pen")] = pen_b["burn"].astype(int).tolist() or [12]

    # ---- punts and kickoffs
    pu = df[(df["punt_attempt"] == 1) & (df["punt_blocked"].fillna(0) == 0) & df["kick_distance"].notna()]
    net = (pu["kick_distance"] - pu["return_yards"].fillna(0)).clip(5, 80)
    for b in range(4):
        sel = net[[punt_bin(y) == b for y in pu["yardline_100"]]]
        L.punt_pool[b] = sel.astype(int).tolist()
    kdf = df if rules_pbp is None else prepare_pbp(rules_pbp)
    ko = kdf[(kdf["kickoff_attempt"] == 1) & kdf["nxt_yl"].notna() & (kdf["nxt_pos"] == kdf["posteam"])]
    for e in range(3):
        s = ko[ko["season"].map(era_of) == e]["nxt_yl"]
        if len(s) >= 100:
            L.kick_pool[e] = s.clip(5, 99).round().astype(int).tolist()
    for e in range(3):
        if e not in L.kick_pool:
            near = sorted(L.kick_pool, key=lambda k: abs(k - e))
            L.kick_pool[e] = L.kick_pool[near[0]]

    # ---- weather sensitivity (linear on outcomes)
    def wfit(frame, y):
        Xw = frame[["wind_ex", "cold", "dome"]].to_numpy(float)
        m = LinearRegression().fit(Xw, y.astype(float))
        return tuple(float(c) for c in m.coef_)

    L.wx["comp"] = wfit(atts, atts["comp"])
    L.wx["int"] = wfit(atts, atts["is_int"])
    L.wx["sack"] = wfit(dbk, dbk["sacked"])
    cp = cps
    L.wx["ypcomp"] = wfit(cp, cp["passing_yards"])
    L.wx["ypr"] = wfit(runs, runs["rushing_yards"])
    return L

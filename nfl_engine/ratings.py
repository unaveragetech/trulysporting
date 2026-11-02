"""Opponent-adjusted, time-decayed team / quarterback / coach ratings, built strictly pre-game.

Walks the schedule chronologically; every game gets a snapshot of what was known *before* kickoff,
then ratings are updated with what happened.  That makes backtests leak-free by construction.
"""

from __future__ import annotations

import math
from collections import defaultdict
from dataclasses import dataclass, field

import numpy as np
import pandas as pd

from nfl_engine.league import (
    GSR_IDX, SD_IDX, YTG_MAX, League, fg_feats, pc_feats, prepare_pbp)

# stat -> (numerator col, denominator col, prior strength k in events, has_defense, opp_adjusted)
STATS: dict[str, tuple[str, str, float, bool]] = {
    "sack": ("sack", "db", 400.0, True),
    "scr": ("scr", "db", 300.0, True),
    "comp": ("comp", "att", 350.0, True),
    "int": ("int", "att", 1300.0, True),
    "ypcomp": ("comp_yds", "comp", 200.0, True),
    "ypr": ("ru_yds", "ru", 600.0, True),
    "fum": ("fum", "n_scrim", 3000.0, True),
    "pen": ("offpen", "snaps", 1100.0, True),  # defensive side uses defpen
}
OFF_ONLY = {"burn": ("burn_sum", "burn_n", 100.0), "proe": ("pc_resid", "pc_n", 250.0),
            "fgx": ("fg_resid", "fg_n", 100.0)}
COACH_STAT = {"go": ("go_resid", "go_n", 25.0)}
QB_STATS = ("sack", "scr", "comp", "int", "ypcomp")


@dataclass
class RatingParams:
    half_life: float = 16.0  # games
    carry: float = 0.6  # fraction of evidence kept across seasons
    k_scale: float = 1.0
    qb_k_scale: float = 1.0
    qb_carry: float = 0.85
    coach_carry: float = 0.8
    base_half_life: float = 800.0  # team-games for the league average


# ---------------------------------------------------------------- observations from pbp


def _add_model_cols(df: pd.DataFrame, L: League) -> pd.DataFrame:
    """Residual of observed behaviour vs the league model (play-calling, 4th down, FG)."""
    ok = df["scrim"] & df["qtr"].between(1, 4) & df["score_differential"].notna() & (df["mode"] == 0) & (
        df["qb_kneel"] != 1)
    sub = df[ok]
    X = np.array([pc_feats(d, y, yl, sd, int(q), h, g, w, c, dm) for d, y, yl, sd, q, h, g, w, c, dm in zip(
        sub["down"], sub["ydstogo"], sub["yardline_100"], sub["score_differential"], sub["qtr"],
        sub["half_seconds_remaining"], sub["game_seconds_remaining"], sub["wind_ex"], sub["cold"], sub["dome"])],
        dtype=float)
    df["pc_resid"] = np.nan
    if len(sub):
        df.loc[sub.index, "pc_resid"] = sub["dropback"].astype(float).to_numpy() - L.pc_model.predict_proba(X)[:, 1]

    f4 = df["down"].eq(4) & df["play_type"].isin(["pass", "run", "punt", "field_goal"]) & df[
        "score_differential"].notna() & df["yardline_100"].notna() & (df["qtr"] <= 4)
    s4 = df[f4]
    iy = np.minimum(s4["ydstogo"].astype(int), YTG_MAX).clip(lower=1) - 1
    il = s4["yardline_100"].astype(int).clip(1, 99) - 1
    isd = SD_IDX[(s4["score_differential"].clip(-30, 30).astype(int) + 30).to_numpy()]
    ig = GSR_IDX[(s4["game_seconds_remaining"].clip(0, 3600) // 10).astype(int).to_numpy()]
    p_go = L.fourth_grid[iy.to_numpy(), il.to_numpy(), isd, ig, 0]
    df["go_resid"] = np.nan
    df.loc[s4.index, "go_resid"] = s4["play_type"].isin(["pass", "run"]).astype(float).to_numpy() - p_go

    fg = df[(df["field_goal_attempt"] == 1) & df["field_goal_result"].notna()]
    dist = fg["kick_distance"].fillna(fg["yardline_100"] + 17)
    Xf = np.array([fg_feats(d, w, c, dm) for d, w, c, dm in zip(dist, fg["wind_ex"], fg["cold"], fg["dome"])])
    df["fg_resid"] = np.nan
    if len(fg):
        df.loc[fg.index, "fg_resid"] = (fg["field_goal_result"] == "made").astype(float).to_numpy() - \
            L.fg_model.predict_proba(Xf)[:, 1]
    return df


def build_observations(pbp: pd.DataFrame, L: League) -> tuple[pd.DataFrame, pd.DataFrame, pd.DataFrame]:
    """Returns (team-game offense table, qb-game table, play frame)."""
    df = _add_model_cols(prepare_pbp(pbp), L)
    s = df[df["scrim"]]
    k = ["game_id", "posteam"]
    g = s.groupby(k)
    tg = pd.DataFrame({
        "db": g["dropback"].sum(), "sack": g["sacked"].sum(), "scr": g["scramble"].sum(),
        "att": g["att"].sum(), "comp": g["comp"].sum(), "int": g["is_int"].sum(),
        "ru": g["dsg_run"].sum(), "ru_yds": s[s["dsg_run"]].groupby(k)["rushing_yards"].sum(),
        "comp_yds": s[s["comp"]].groupby(k)["passing_yards"].sum(),
        "n_scrim": g.size(), "fum": g["fumble_lost"].sum(),
    }).fillna(0.0)
    tg["offpen"] = df[df["off_pen"]].groupby(k).size().reindex(tg.index).fillna(0)
    tg["defpen"] = df[df["def_pen"]].groupby(k).size().reindex(tg.index).fillna(0)
    tg["snaps"] = tg["n_scrim"] + df[df["no_play_pen"]].groupby(k).size().reindex(tg.index).fillna(0)
    b = s[s["burn"].notna() & (s["mode"] == 0) & (s["qb_kneel"] != 1)].groupby(k)["burn"]
    tg["burn_sum"], tg["burn_n"] = b.sum().reindex(tg.index).fillna(0), b.count().reindex(tg.index).fillna(0)
    p = df[df["pc_resid"].notna()].groupby(k)["pc_resid"]
    tg["pc_resid"], tg["pc_n"] = p.sum().reindex(tg.index).fillna(0), p.count().reindex(tg.index).fillna(0)
    q = df[df["go_resid"].notna()].groupby(k)["go_resid"]
    tg["go_resid"], tg["go_n"] = q.sum().reindex(tg.index).fillna(0), q.count().reindex(tg.index).fillna(0)
    f = df[df["fg_resid"].notna()].groupby(k)["fg_resid"]
    tg["fg_resid"], tg["fg_n"] = f.sum().reindex(tg.index).fillna(0), f.count().reindex(tg.index).fillna(0)
    tg = tg.reset_index().rename(columns={"posteam": "team"})

    # quarterback layer: dropbacks / scrambles credited to the game's primary passer
    d = s[s["dropback"]].copy()
    mode_pass = d[d["passer_player_id"].notna()].groupby(k)["passer_player_id"].agg(lambda x: x.mode().iat[0])
    d["qb"] = d["passer_player_id"].fillna(d.set_index(k).index.map(mode_pass).to_series().reset_index(drop=True))
    d = d[d["qb"].notna()]
    kq = ["game_id", "posteam", "qb"]
    gq = d.groupby(kq)
    qbg = pd.DataFrame({
        "db": gq.size(), "sack": gq["sacked"].sum(), "scr": gq["scramble"].sum(), "att": gq["att"].sum(),
        "comp": gq["comp"].sum(), "int": gq["is_int"].sum(),
        "comp_yds": d[d["comp"]].groupby(kq)["passing_yards"].sum(),
    }).fillna(0.0).reset_index().rename(columns={"posteam": "team"})
    return tg, qbg, df


# ---------------------------------------------------------------- the rating book


@dataclass
class Snapshot:
    off: dict  # stat -> dev (team support, qb excluded)
    deff: dict
    qb: dict  # stat -> dev of the starting quarterback
    qb_id: str | None
    qb_games: float
    coach_go: float
    coach: str | None
    off_pen: float = 0.0
    games: float = 0.0


@dataclass
class Book:
    params: RatingParams
    base: dict = field(default_factory=dict)
    snaps: dict = field(default_factory=dict)  # game_id -> {'home': Snapshot, 'away': Snapshot, 'base': dict}
    # live state (after the last processed game) for upcoming games
    state: dict = field(default_factory=dict)


class _Acc:
    """Decayed numerator/denominator accumulator keyed by (entity, stat)."""

    def __init__(self):
        self.num: dict = defaultdict(float)
        self.den: dict = defaultdict(float)

    def dev(self, key, k):
        d = self.den.get(key, 0.0)
        return self.num.get(key, 0.0) / (d + k) if d else 0.0

    def add(self, key, n, w, lam):
        self.num[key] = self.num[key] * lam + n
        self.den[key] = self.den[key] * lam + w

    def scale(self, keys, f):
        for key in keys:
            if key in self.num:
                self.num[key] *= f
                self.den[key] *= f


def build_book(games: pd.DataFrame, tg: pd.DataFrame, qbg: pd.DataFrame, P: RatingParams) -> Book:
    """Process all *played* games in order, storing pre-game snapshots for every game incl. upcoming."""
    lam = 0.5 ** (1.0 / P.half_life)
    lam_b = 0.5 ** (1.0 / P.base_half_life)
    obs = {(r.game_id, r.team): r for r in tg.itertuples(index=False)}
    qbs: dict = defaultdict(list)
    for r in qbg.itertuples(index=False):
        qbs[(r.game_id, r.team)].append(r)

    off, dfn, qb, coach = _Acc(), _Acc(), _Acc(), _Acc()
    base_num: dict = defaultdict(float)
    base_den: dict = defaultdict(float)
    last_season = None
    book = Book(params=P)

    def base_of(stat):
        bd = base_den.get(stat, 0.0)
        return base_num[stat] / bd if bd else 0.0

    def ks(stat, defense=False):
        k = (STATS[stat][2] if stat in STATS else OFF_ONLY[stat][2]) * P.k_scale
        return k * (1.3 if defense and stat in ("comp", "int", "ypcomp", "ypr") else 1.0)

    def snap_for(team, qid, cname):
        s = {st: off.dev((team, st), ks(st)) for st in list(STATS) + list(OFF_ONLY)}
        d = {st: dfn.dev((team, st), ks(st, True)) for st in STATS}
        qd = {st: qb.dev((qid, st), STATS[st][2] * P.qb_k_scale) if qid else 0.0 for st in QB_STATS}
        return Snapshot(off=s, deff=d, qb=qd, qb_id=qid, qb_games=qb.den.get((qid, "sack"), 0.0) if qid else 0.0,
                        coach_go=coach.dev((cname, "go"), COACH_STAT["go"][2] * P.k_scale) if cname else 0.0,
                        coach=cname, games=off.den.get((team, "sack"), 0.0))

    for day, grp in games.groupby("gameday", sort=True):
        season = int(grp["season"].iat[0])
        if last_season is not None and season != last_season:
            off.scale(list(off.num), P.carry)
            dfn.scale(list(dfn.num), P.carry)
            qb.scale(list(qb.num), P.qb_carry)
            coach.scale(list(coach.num), P.coach_carry)
        last_season = season
        # 1) snapshots before any of today's results are known
        for r in grp.itertuples(index=False):
            hs = snap_for(r.home_team, getattr(r, "home_qb_id", None), getattr(r, "home_coach", None))
            as_ = snap_for(r.away_team, getattr(r, "away_qb_id", None), getattr(r, "away_coach", None))
            book.snaps[r.game_id] = {"home": hs, "away": as_, "base": {s: base_of(s) for s in list(STATS) + list(OFF_ONLY)}}
        # 2) learn from the games that have been played
        for r in grp.itertuples(index=False):
            if not (r.home_score == r.home_score):
                continue
            for team, opp, cname in ((r.home_team, r.away_team, r.home_coach), (r.away_team, r.home_team, r.away_coach)):
                o, e = obs.get((r.game_id, team)), obs.get((r.game_id, opp))
                if o is None or e is None:
                    continue
                qlist = qbs.get((r.game_id, team), [])
                tot_db = max(sum(x.db for x in qlist), 1.0)
                for st, (nc, dc, _k, has_def) in STATS.items():
                    n, w = getattr(o, nc), getattr(o, dc)
                    if w <= 0:
                        continue
                    b = base_of(st)
                    opp_def = dfn.dev((opp, st), ks(st, True))
                    team_off = off.dev((team, st), ks(st))
                    qpart = 0.0
                    if st in QB_STATS and qlist:
                        qpart = sum((x.db / tot_db) * qb.dev((x.qb, st), STATS[st][2] * P.qb_k_scale) for x in qlist)
                    off.add((team, st), n - w * (b + opp_def + qpart), w, lam)  # excess over expectation
                    if st == "pen":  # penalties are committed, not forced: no cross-adjustment
                        dfn.add((opp, st), o.defpen - o.snaps * b, o.snaps, lam)
                    else:
                        dfn.add((opp, st), n - w * (b + team_off + qpart), w, lam)
                    if st in QB_STATS and qlist:
                        for x in qlist:
                            xn = {"sack": x.sack, "scr": x.scr, "comp": x.comp, "int": x.int, "ypcomp": x.comp_yds}[st]
                            xw = {"sack": x.db, "scr": x.db, "comp": x.att, "int": x.att, "ypcomp": x.comp}[st]
                            if xw > 0:
                                qb.add((x.qb, st), xn - xw * (b + opp_def + team_off), xw, lam)
                    base_num[st] = base_num[st] * lam_b + n
                    base_den[st] = base_den[st] * lam_b + w
                for st, (nc, dc, _k) in OFF_ONLY.items():
                    n, w = getattr(o, nc), getattr(o, dc)
                    if w > 0:
                        off.add((team, st), n - w * base_of(st), w, lam)
                        base_num[st] = base_num[st] * lam_b + n
                        base_den[st] = base_den[st] * lam_b + w
                n, w = o.go_resid, o.go_n
                if w > 0 and cname:
                    coach.add((cname, "go"), n, w, lam)
    book.base = {s: base_of(s) for s in list(STATS) + list(OFF_ONLY)}
    book.state = {"off": off, "dfn": dfn, "qb": qb, "coach": coach}
    return book

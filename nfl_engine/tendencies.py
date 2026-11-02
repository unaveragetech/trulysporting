"""Situational tendencies: what each team (and defense) does in each situation and in response to what just happened.

Every tendency is a *residual against the league model* (observed pass-call minus what an average team does in the
same spot), tracked chronologically with exponential forgetting and shrinkage, so the value used for a game only
uses games played before it.  ``TendBook`` stores the running state per (team, offense/defense, situation family,
situation) plus the pre-game estimates for recent games; ``TendBook.shifts`` turns them into the logit shifts the
simulator adds to its play-call probability.  ``update`` folds in newly played games incrementally.
"""

from __future__ import annotations

import numpy as np
import pandas as pd

from nfl_engine.league import (PC_GSR_IDX, PC_YTG, RESP_LABELS, SD_IDX, YL_IDX, League, resp_codes, weather_cols)

FAMS = ("all", "dd", "sc", "zone", "resp")
SIDES = ("off", "def")
KEYS = {
    "all": ("all",),
    "dd": ("1", "2s", "2m", "2l", "3s", "3m", "3l", "4s", "4m", "4l"),
    "sc": tuple(a + b for a in ("L2", "L1", "T0", "T1", "T2") for b in ("h1", "q3", "q4")),
    "zone": ("own", "mid", "opp", "rz", "gl"),
    "resp": RESP_LABELS,
}


ALL_KEYS = [(side, fam, key) for side in SIDES for fam in FAMS for key in KEYS[fam]]
KEY_IDX = {k: i for i, k in enumerate(ALL_KEYS)}


def base_pass_p(L: League, df: pd.DataFrame, resp: np.ndarray) -> np.ndarray:
    """League-model pass probability for every row of ``df`` from the tabulated play-call grid."""
    down = np.clip(df["down"].fillna(1).to_numpy(int), 1, 4) - 1
    ytg = np.clip(df["ydstogo"].fillna(10).to_numpy(int), 1, PC_YTG) - 1
    yl = YL_IDX[np.clip(df["yardline_100"].fillna(50).to_numpy(int), 0, 100)]
    sd = SD_IDX[np.clip(df["score_differential"].fillna(0).to_numpy(int), -30, 30) + 30]
    gs = PC_GSR_IDX[(np.clip(df["game_seconds_remaining"].fillna(1800).to_numpy(), 0, 3600) // 10).astype(int)]
    p = np.clip(L.pass_grid[down, ytg, yl, sd, gs, resp].astype(float), 1e-4, 1 - 1e-4)
    z = np.log(p / (1 - p))
    for w, c, m in zip(L.pass_wx, ("wind_ex", "cold", "dome"), L.wx_mean):
        z = z + w * (df[c].to_numpy() - m)
    return 1 / (1 + np.exp(-z))


def add_context(df: pd.DataFrame, L: League) -> pd.DataFrame:
    """Scrimmage plays with the situation classes, previous-play response and league-model residual."""
    df = weather_cols(df[df["season_type"].isin(["REG", "POST"])].copy())
    df = df.sort_values(["game_id", "play_id"]).reset_index(drop=True)
    scrim = df["play_type"].isin(["pass", "run"]) & df["down"].notna() & (df["qb_kneel"] != 1) & (df["qb_spike"] != 1) \
        & df["score_differential"].notna() & df["yardline_100"].notna() & df["qtr"].between(1, 4)
    resp = resp_codes(df)
    df["resp"] = np.array(RESP_LABELS)[resp]
    df["is_pass"] = ((df["qb_dropback"] == 1) | (df["qb_scramble"] == 1)).astype(float)
    ytg, down, sd = df["ydstogo"], df["down"], df["score_differential"].fillna(0)
    size = np.where(ytg <= 3, "s", np.where(ytg <= 7, "m", "l"))
    df["dd"] = np.where(down == 1, "1", down.fillna(0).astype(int).astype(str) + pd.Series(size, index=df.index))
    sc = np.select([sd >= 9, sd >= 1, sd == 0, sd >= -8], ["L2", "L1", "T0", "T1"], default="T2")
    df["sc"] = sc + np.where(df["qtr"] >= 4, "q4", np.where(df["qtr"] >= 3, "q3", "h1"))
    yl = df["yardline_100"]
    df["zone"] = np.select([yl >= 80, yl >= 50, yl >= 21, yl >= 11], ["own", "mid", "opp", "rz"], default="gl")
    df["all"] = "all"
    df["scrim"] = scrim
    df["p0"] = np.nan
    df.loc[scrim, "p0"] = base_pass_p(L, df[scrim], resp[scrim.to_numpy()])
    df["resid"] = df["is_pass"] - df["p0"]
    for c in ("posteam", "defteam", "dd", "sc", "zone", "resp"):
        df[c] = df[c].astype(str)
    return df


SLIM = ["game_id", "season", "posteam", "defteam", "resid", "p0", "is_pass", "dd", "sc", "zone", "resp", "all"]


def context_frame(L: League, seasons, refresh: bool = False) -> pd.DataFrame:
    """add_context over several seasons (one at a time, keeping only the columns the trackers need)."""
    from nfl_engine.tracking import load_rich

    parts = []
    for s in seasons:
        d = add_context(load_rich(s, refresh=refresh), L)
        parts.append(d.loc[d["scrim"], SLIM])
    return pd.concat(parts, ignore_index=True)


def _agg(plays: pd.DataFrame, games: pd.DataFrame, side: str, fam: str) -> pd.DataFrame:
    team = "posteam" if side == "off" else "defteam"
    p = plays[plays["resid"].notna()]
    a = p.groupby([team, fam, "game_id"], observed=True)["resid"].agg(["sum", "count"]).reset_index()
    a.columns = ["team", "key", "game_id", "sum", "count"]
    a["day"] = a["game_id"].map(games.set_index("game_id")["gameday"])
    return a.dropna(subset=["day"]).sort_values(["team", "key", "day"]).reset_index(drop=True)


class TendBook:
    def __init__(self, half_life: float = 10.0, prior: float = 40.0, hist_from: int = 2021):
        self.hl, self.prior, self.hist_from = half_life, prior, hist_from
        self.state: dict = {}  # (team, side, fam, key) -> [S, N, last_day(ns)]
        self.hist: dict = {}  # (team, game_id) -> float32 vector over ALL_KEYS (pre-game estimates)
        self.coef: dict = {}  # (side, fam) -> logit weight on the estimate
        self.last_day = None

    def _h(self, team: str, gid: str) -> np.ndarray:
        v = self.hist.get((team, gid))
        if v is None:
            v = self.hist[(team, gid)] = np.zeros(len(ALL_KEYS), np.float32)
        return v

    # ---- core recurrence --------------------------------------------------------------
    def _decay(self, days: float) -> float:
        return 0.5 ** (max(days, 0.0) / (7.0 * self.hl))

    def _run(self, a: pd.DataFrame, side: str, fam: str, seasons: dict, keep_hist: bool) -> list:
        """Walk a sorted (team, key, game) table updating ``state``; returns [(team, key, game_id, est)]."""
        out = []
        ns_day = 86400e9
        for (team, key), g in a.groupby(["team", "key"], sort=False):
            st = self.state.get((team, side, fam, key), [0.0, 0.0, None])
            S, N, last = st
            for gid, s, c, day in zip(g["game_id"], g["sum"], g["count"], g["day"]):
                d = day.value
                if last is not None:
                    f = self._decay((d - last) / ns_day)
                    S, N = S * f, N * f
                out.append((team, key, gid, S / (N + self.prior)))
                S, N, last = S + s, N + c, d
            self.state[(team, side, fam, key)] = [S, N, last]
        return out

    def _est(self, team: str, side: str, fam: str, key: str, day) -> float:
        st = self.state.get((team, side, fam, key))
        if not st or st[2] is None:
            return 0.0
        f = self._decay((pd.Timestamp(day).value - st[2]) / 86400e9)
        return st[0] * f / (st[1] * f + self.prior)

    # ---- build / update ----------------------------------------------------------------
    def build(self, plays: pd.DataFrame, games: pd.DataFrame, fit_seasons: tuple[int, int] = (2018, 2023)):
        """Chronological pass over ``plays`` (from add_context); also fits the logit weight of each family."""
        feats = {}
        season_of = games.set_index("game_id")["season"].to_dict()
        for side in SIDES:
            for fam in FAMS:
                a = _agg(plays, games, side, fam)
                est = self._run(a, side, fam, season_of, True)
                e = pd.DataFrame(est, columns=["team", "key", "game_id", "est"])
                for t, k, gid, v in zip(e["team"], e["key"], e["game_id"], e["est"]):
                    if season_of.get(gid, 0) >= self.hist_from:
                        self._h(t, gid)[KEY_IDX[(side, fam, k)]] = v
                tm = "posteam" if side == "off" else "defteam"
                m = plays[[tm, fam, "game_id"]].merge(e.rename(columns={"team": tm, "key": fam}), on=[tm, fam, "game_id"], how="left")
                feats[f"{side}_{fam}"] = m["est"].fillna(0.0).to_numpy()
        F = pd.DataFrame(feats, index=plays.index)
        self.last_day = max(games.loc[games["game_id"].isin(set(plays["game_id"])), "gameday"])
        self._fit(plays, F, fit_seasons, games)
        return F

    def _fit(self, plays: pd.DataFrame, F: pd.DataFrame, fit_seasons, games) -> None:
        from sklearn.linear_model import LogisticRegression

        ok = plays["p0"].notna() & plays["season"].between(*fit_seasons)
        p0 = np.clip(plays.loc[ok, "p0"].to_numpy(), 1e-4, 1 - 1e-4)
        X = np.c_[np.log(p0 / (1 - p0)), F.loc[ok].to_numpy()]
        m = LogisticRegression(C=5.0, max_iter=500).fit(X, plays.loc[ok, "is_pass"].to_numpy())
        for name, w in zip(F.columns, m.coef_[0][1:]):
            side, fam = name.split("_", 1)
            self.coef[(side, fam)] = float(w)

    def update(self, plays_new: pd.DataFrame, games: pd.DataFrame) -> int:
        """Fold newly played games (add_context frame) into the running state; returns games added."""
        done = {gid for (_, gid) in self.hist}
        new = plays_new[~plays_new["game_id"].isin(done)]
        if self.last_day is not None:
            keep = set(games.loc[games["gameday"] > self.last_day, "game_id"])
            new = new[new["game_id"].isin(keep)]
        if new.empty:
            return 0
        season_of = games.set_index("game_id")["season"].to_dict()
        for side in SIDES:
            for fam in FAMS:
                e = pd.DataFrame(self._run(_agg(new, games, side, fam), side, fam, season_of, True),
                                 columns=["team", "key", "game_id", "est"])
                for t, k, gid, v in zip(e["team"], e["key"], e["game_id"], e["est"]):
                    self._h(t, gid)[KEY_IDX[(side, fam, k)]] = v
        self.last_day = max(games.loc[games["game_id"].isin(set(new["game_id"])), "gameday"])
        return int(new["game_id"].nunique())

    # ---- for the simulator -------------------------------------------------------------
    def shifts(self, off: str, dfn: str, game_id: str, day) -> dict:
        """Logit shifts per situation for ``off`` facing ``dfn`` in this game (pre-game information only)."""
        out = {"all": 0.0, "dd": {}, "sc": {}, "zone": {}, "resp": {}}
        for side, team in (("off", off), ("def", dfn)):
            h = self.hist.get((team, game_id))
            for fam in FAMS:
                w = self.coef.get((side, fam), 0.0)
                if not w:
                    continue
                for key in KEYS[fam]:
                    est = float(h[KEY_IDX[(side, fam, key)]]) if h is not None else self._est(team, side, fam, key, day)
                    if fam == "all":
                        out["all"] += w * est
                    else:
                        out[fam][key] = out[fam].get(key, 0.0) + w * est
        return out

    def team_profile(self, team: str, day=None, side: str = "off") -> pd.DataFrame:
        """Current shrunk tendency (percentage points vs league) of ``team`` per situation, for display."""
        day = day or self.last_day
        rows = []
        for fam in FAMS:
            for key in KEYS[fam]:
                st = self.state.get((team, side, fam, key))
                rows.append({"family": fam, "situation": key, "vs_league_pp": 100 * self._est(team, side, fam, key, day),
                             "plays": 0.0 if not st else st[1]})
        return pd.DataFrame(rows)

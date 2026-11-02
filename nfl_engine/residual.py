"""Second stage: learn what the play-level sim systematically misses about each team.

For every completed game we compare real points with the pre-game simulated expectation; the gap is
accumulated per team (offence and defence) with decay and shrinkage, then fed back as an additive
points adjustment on future games.  Captures persistent traits the play model has no direct term for
(special teams, explosiveness, finishing drives, scheme).
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass

import numpy as np
import pandas as pd


@dataclass
class ResidualParams:
    half_life: float = 30.0  # games
    k: float = 50.0  # prior strength in games
    carry: float = 0.7
    gain: float = 1.0


class ResidualBook:
    def __init__(self, p: ResidualParams):
        self.p = p
        self.lam = 0.5 ** (1.0 / p.half_life)
        self.on, self.od = defaultdict(float), defaultdict(float)  # offence num/den
        self.dn, self.dd = defaultdict(float), defaultdict(float)  # defence num/den
        self.season = None
        self.done: set[str] = set()

    def _off(self, t):
        return self.on[t] / (self.od[t] + self.p.k) if self.od[t] else 0.0

    def _def(self, t):
        return self.dn[t] / (self.dd[t] + self.p.k) if self.dd[t] else 0.0

    def adj(self, home: str, away: str) -> tuple[float, float]:
        g = self.p.gain
        return g * (self._off(home) + self._def(away)), g * (self._off(away) + self._def(home))

    def new_season(self, season: int) -> None:
        if self.season is not None and season != self.season:
            for d in (self.on, self.od, self.dn, self.dd):
                for t in list(d):
                    d[t] *= self.p.carry
        self.season = season

    def update(self, gid, home, away, sim_h, sim_a, act_h, act_a) -> None:
        rh, ra = act_h - sim_h, act_a - sim_a
        oh, oa, dh, da = self._off(home), self._off(away), self._def(home), self._def(away)
        lam = self.lam
        for store_n, store_d, t, n in ((self.on, self.od, home, rh - da), (self.on, self.od, away, ra - dh),
                                       (self.dn, self.dd, away, rh - oh), (self.dn, self.dd, home, ra - oa)):
            store_n[t] = store_n[t] * lam + n
            store_d[t] = store_d[t] * lam + 1.0
        self.done.add(gid)


def run_residuals(df: pd.DataFrame, p: ResidualParams, book: ResidualBook | None = None):
    """Walk ``df`` (needs gameday/home/away/sim_home/sim_away/act_*) chronologically.

    Returns (adj_home, adj_away) aligned to ``df.index`` using only information from earlier days, and the
    updated book.  Rows without a result get an adjustment but do not update the book.
    """
    book = book or ResidualBook(p)
    adj_h = pd.Series(0.0, index=df.index)
    adj_a = pd.Series(0.0, index=df.index)
    for _day, grp in df.sort_values(["gameday", "game_id"]).groupby("gameday", sort=True):
        book.new_season(int(grp["season"].iat[0]))
        for i, r in grp.iterrows():
            adj_h[i], adj_a[i] = book.adj(r["home"], r["away"])
        for i, r in grp.iterrows():
            if r["act_home"] == r["act_home"] and r["game_id"] not in book.done:
                book.update(r["game_id"], r["home"], r["away"], r["sim_home"], r["sim_away"], r["act_home"], r["act_away"])
    return adj_h, adj_a, book


def apply_adjustment(df: pd.DataFrame, adj_h, adj_a) -> pd.DataFrame:
    d = df.copy()
    d["adj_home"], d["adj_away"] = d["sim_home"] + adj_h, d["sim_away"] + adj_a
    d["adj_margin"] = d["adj_home"] - d["adj_away"]
    d["adj_total"] = d["adj_home"] + d["adj_away"]
    return d


def fit_gain(df: pd.DataFrame, adj_h, adj_a) -> float:
    """Least-squares gain on the residual adjustment for margin and total (shared)."""
    y = np.r_[df["act_home"] - df["sim_home"], df["act_away"] - df["sim_away"]]
    x = np.r_[adj_h, adj_a]
    m = np.isfinite(y) & np.isfinite(x)
    denom = float((x[m] ** 2).sum())
    return float((x[m] * y[m]).sum() / denom) if denom > 0 else 1.0

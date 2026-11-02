"""Parallel simulation runner, calibration against completed games, and walk-forward backtesting."""

from __future__ import annotations

import os
import zlib
from concurrent.futures import ProcessPoolExecutor
from dataclasses import asdict, dataclass, field

import numpy as np
import pandas as pd

from nfl_engine.league import League
from nfl_engine.matchup import Tuning, make_spec
from nfl_engine.ratings import Book
from nfl_engine.sim import simulate

_L: League | None = None


def _init(L: League) -> None:
    global _L
    _L = L


def _task(args):
    key, spec, n, seed = args
    r = simulate(_L, spec, n=n, seed=seed)
    return key, {
        "margin": r["margin"].astype(np.int16), "home": r["home_pts"].astype(np.int16),
        "away": r["away_pts"].astype(np.int16), "box": r["box"], "ot": r["ot_rate"],
    }


def seed_of(game_id: str) -> int:
    return zlib.crc32(game_id.encode()) & 0x7FFFFFFF


def run_games(L: League, book: Book, games: pd.DataFrame, tune: Tuning, n: int = 300,
              workers: int | None = None) -> dict:
    """Simulate each game ``n`` times (common random numbers per game id).  Returns {game_id: result}."""
    jobs = [(r.game_id, make_spec(r, book, L, tune), n, seed_of(r.game_id)) for r in games.itertuples(index=False)]
    workers = workers or max(1, (os.cpu_count() or 2) - 2)
    if workers == 1 or len(jobs) < 8:
        _init(L)
        return dict(_task(j) for j in jobs)
    with ProcessPoolExecutor(workers, initializer=_init, initargs=(L,)) as ex:
        return dict(ex.map(_task, jobs, chunksize=max(1, len(jobs) // (workers * 6))))


# ---------------------------------------------------------------- summaries & metrics


def summarize(res: dict, games: pd.DataFrame) -> pd.DataFrame:
    rows = []
    for r in games.itertuples(index=False):
        x = res[r.game_id]
        m, h, a = x["margin"].astype(float), x["home"].astype(float), x["away"].astype(float)
        rows.append({
            "game_id": r.game_id, "season": r.season, "week": r.week, "gameday": r.gameday,
            "home": r.home_team, "away": r.away_team,
            "sim_margin": m.mean(), "sim_total": (h + a).mean(), "sim_home": h.mean(), "sim_away": a.mean(),
            "sim_pwin": float(((m > 0) + 0.5 * (m == 0)).mean()), "sim_sd": m.std(),
            "sim_sd_total": (h + a).std(),
            "spread": getattr(r, "spread_line", np.nan), "total_line": getattr(r, "total_line", np.nan),
            "act_margin": getattr(r, "result", np.nan), "act_total": getattr(r, "total", np.nan),
            "act_home": r.home_score, "act_away": r.away_score,
        })
    return pd.DataFrame(rows)


def _logit(p):
    p = np.clip(p, 1e-4, 1 - 1e-4)
    return np.log(p / (1 - p))


@dataclass
class Calibrator:
    """Maps raw sim outputs to calibrated predictions using completed games (fit out-of-sample pre-game)."""
    a_m: float = 0.0
    b_m: float = 1.0
    a_t: float = 0.0
    b_t: float = 1.0
    w_a: float = 0.0
    w_b: float = 1.0 / 7.5  # logistic slope per margin point

    def margin(self, m):
        return self.a_m + self.b_m * np.asarray(m, float)

    def total(self, t):
        return self.a_t + self.b_t * np.asarray(t, float)

    def pwin(self, m):
        return 1 / (1 + np.exp(-(self.w_a + self.w_b * self.margin(m))))


def fit_calibrator(df: pd.DataFrame, cm: str = "sim_margin", ct: str = "sim_total") -> Calibrator:
    from sklearn.linear_model import LogisticRegression

    d = df.dropna(subset=["act_margin", "act_total"])
    c = Calibrator()
    bm, am = np.polyfit(d[cm], d["act_margin"], 1)
    bt, at = np.polyfit(d[ct], d["act_total"], 1)
    c.a_m, c.b_m, c.a_t, c.b_t = float(am), float(bm), float(at), float(bt)
    y = (d["act_margin"] > 0).astype(int)
    keep = d["act_margin"] != 0
    lr = LogisticRegression(C=100.0).fit(c.margin(d.loc[keep, cm]).reshape(-1, 1), y[keep])
    c.w_b, c.w_a = float(lr.coef_[0][0]), float(lr.intercept_[0])
    return c


def metrics(df: pd.DataFrame, cal: Calibrator | None = None, cal_raw: Calibrator | None = None) -> dict:
    d = df.dropna(subset=["act_margin"]).copy()
    d = d[d["act_margin"] != 0]
    y = (d["act_margin"] > 0).astype(float).to_numpy()
    out = {"games": len(d)}

    def block(name, pm, pt, pw):
        eps = 1e-4
        pw = np.clip(pw, eps, 1 - eps)
        out[name] = {
            "win_acc": float(((pw > 0.5) == (y > 0.5)).mean()),
            "brier": float(((pw - y) ** 2).mean()),
            "logloss": float(-(y * np.log(pw) + (1 - y) * np.log(1 - pw)).mean()),
            "margin_mae": float(np.abs(pm - d["act_margin"]).mean()),
            "margin_rmse": float(np.sqrt(((pm - d["act_margin"]) ** 2).mean())),
            "margin_bias": float((pm - d["act_margin"]).mean()),
            "total_mae": float(np.abs(pt - d["act_total"]).mean()),
            "total_bias": float((pt - d["act_total"]).mean()),
            "margin_corr": float(np.corrcoef(pm, d["act_margin"])[0, 1]),
            "total_corr": float(np.corrcoef(pt, d["act_total"])[0, 1]),
        }

    block("sim_raw", d["sim_margin"].to_numpy(), d["sim_total"].to_numpy(), d["sim_pwin"].to_numpy())
    cm, ct = ("adj_margin", "adj_total") if "adj_margin" in d else ("sim_margin", "sim_total")
    if cal_raw is not None:
        block("sim_calibrated_play_level_only", cal_raw.margin(d["sim_margin"]), cal_raw.total(d["sim_total"]),
              cal_raw.pwin(d["sim_margin"]))
    if cal is not None:
        pm = cal.margin(d[cm])
        block("sim_calibrated", pm, cal.total(d[ct]), cal.pwin(d[cm]))
    mk = d.dropna(subset=["spread", "total_line"])
    if len(mk):
        ym = (mk["act_margin"] > 0).astype(float).to_numpy()
        pw = 1 / (1 + np.exp(-mk["spread"].to_numpy() / 6.5))
        pw = np.clip(pw, 1e-4, 1 - 1e-4)
        out["market"] = {
            "games": len(mk),
            "win_acc": float(((mk["spread"] > 0) == (mk["act_margin"] > 0)).mean()),
            "brier": float(((pw - ym) ** 2).mean()),
            "logloss": float(-(ym * np.log(pw) + (1 - ym) * np.log(1 - pw)).mean()),
            "margin_mae": float(np.abs(mk["spread"] - mk["act_margin"]).mean()),
            "margin_rmse": float(np.sqrt(((mk["spread"] - mk["act_margin"]) ** 2).mean())),
            "total_mae": float(np.abs(mk["total_line"] - mk["act_total"]).mean()),
        }
        if cal is not None:
            pm = cal.margin(mk[cm])
            out["sim_calibrated_on_market_games"] = {
                "margin_mae": float(np.abs(pm - mk["act_margin"]).mean()),
                "total_mae": float(np.abs(cal.total(mk[ct]) - mk["act_total"]).mean()),
                "win_acc": float(((pm > 0) == (mk["act_margin"] > 0)).mean()),
            }
    return out


def ats_report(df: pd.DataFrame, cal: Calibrator, edge: float = 2.0) -> dict:
    """Would picking the side the sim likes against the closing line have won?  (Not betting advice.)"""
    d = df.dropna(subset=["spread", "act_margin"]).copy()
    d["pm"] = cal.margin(d["adj_margin"] if "adj_margin" in d else d["sim_margin"])
    d["edge"] = d["pm"] - d["spread"]
    res = {}
    for thr in (0.0, 1.0, edge, 3.0, 4.0):
        s = d[d["edge"].abs() >= thr]
        s = s[(s["act_margin"] - s["spread"]) != 0]
        if len(s):
            win = ((s["edge"] > 0) == (s["act_margin"] > s["spread"])).mean()
            res[f"edge>={thr}"] = {"bets": len(s), "ats_win_pct": float(win)}
    return res


def calibration_table(df: pd.DataFrame, cal: Calibrator, bins: int = 8) -> list[dict]:
    d = df.dropna(subset=["act_margin"]).copy()
    d = d[d["act_margin"] != 0]
    d["p"] = cal.pwin(d["adj_margin"] if "adj_margin" in d else d["sim_margin"])
    d["bin"] = pd.qcut(d["p"], bins, duplicates="drop")
    g = d.groupby("bin", observed=True)
    return [{"p_pred": float(v["p"].mean()), "p_actual": float((v["act_margin"] > 0).mean()), "n": len(v)}
            for _, v in g]


def box_realism(res: dict, games: pd.DataFrame, tg: pd.DataFrame) -> list[dict]:
    """Compare simulated team stat lines with real box-score aggregates for the same games."""
    t = tg.set_index(["game_id", "team"])
    rows = []
    keys = {"plays": lambda r: r.n_scrim, "db": lambda r: r.db, "pass_yds": None, "rush_yds": lambda r: r.ru_yds,
            "to": lambda r: r.int + r.fum, "td": None, "punts": None, "fga": None, "pen": lambda r: r.offpen + r.defpen}
    sim_means = {k: [] for k in ("plays", "db", "to", "pen")}
    real = {k: [] for k in sim_means}
    for g in games.itertuples(index=False):
        x = res[g.game_id]["box"]
        for side, team in ((0, g.home_team), (1, g.away_team)):
            if (g.game_id, team) not in t.index:
                continue
            o = t.loc[(g.game_id, team)]
            for k in sim_means:
                sim_means[k].append(x[k][side])
            real["plays"].append(o["n_scrim"])
            real["db"].append(o["db"])
            real["to"].append(o["int"] + o["fum"])
            real["pen"].append(o["offpen"] + o["defpen"])
    for k in sim_means:
        rows.append({"stat": k, "sim": float(np.mean(sim_means[k])), "real": float(np.mean(real[k])),
                     "corr": float(np.corrcoef(sim_means[k], real[k])[0, 1])})
    return rows

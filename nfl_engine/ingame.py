"""In-game accuracy: how good is the engine's live win probability, and how do we correct it when it is wrong.

``backtest`` replays completed games from mid-game states (a fixed set of clock checkpoints), asks the engine for
the home win probability from each state and scores it against what really happened and against the nflfastR
live win-probability model.  The result also fits a per-clock-bucket Platt calibrator (``IngameCal``) that
``live_win_prob`` applies, and that the nightly job refits from graded live games (``ledger``).
"""

from __future__ import annotations

import json
import math
import random
import zlib
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass, field

import numpy as np
import pandas as pd

from nfl_engine.data import CANON, SPORTS_DIR
from nfl_engine.sim import Engine

CHECKPOINTS = (3300, 2700, 1800, 900, 300)  # game seconds remaining
CAL_PATH = SPORTS_DIR / "ingame_cal.json"
STATES_PATH = SPORTS_DIR / "ingame_states.csv"
LEDGER_DIR = SPORTS_DIR / "live"


def _logit(p):
    p = np.clip(np.asarray(p, float), 0.005, 0.995)
    return np.log(p / (1 - p))


@dataclass
class IngameCal:
    """logit(p_cal) = a_t + b_t * logit(p_raw), linearly interpolated across the checkpoint clock."""

    ts: list = field(default_factory=lambda: list(CHECKPOINTS))
    a: list = field(default_factory=lambda: [0.0] * len(CHECKPOINTS))
    b: list = field(default_factory=lambda: [1.0] * len(CHECKPOINTS))
    c: list = field(default_factory=lambda: [0.0] * len(CHECKPOINTS))  # weight on the pre-game market prior

    def apply(self, p: float, gsr: float, p_mkt: float | None = None) -> float:
        ts = np.array(self.ts, float)
        order = np.argsort(ts)
        a = np.interp(gsr, ts[order], np.array(self.a)[order])
        b = np.interp(gsr, ts[order], np.array(self.b)[order])
        z = a + b * float(_logit(p))
        if p_mkt is not None and p_mkt == p_mkt:
            c = float(np.interp(gsr, ts[order], np.array(self.c)[order]))
            z += c * float(_logit(p_mkt)) * np.sqrt(max(gsr, 0) / 3600)
        return float(1 / (1 + np.exp(-z)))

    def to_json(self) -> dict:
        return {"ts": self.ts, "a": self.a, "b": self.b, "c": self.c}

    def save(self) -> None:
        CAL_PATH.parent.mkdir(parents=True, exist_ok=True)
        CAL_PATH.write_text(json.dumps(self.to_json()))

    @classmethod
    def load(cls) -> "IngameCal":
        try:
            return cls(**json.loads(CAL_PATH.read_text()))
        except Exception:  # noqa: BLE001
            return cls()


def mkt_prob(spread: float | None) -> float | None:
    """Pre-game home win probability implied by the point spread (positive = home favoured)."""
    if spread is None or spread != spread:
        return None
    return float(0.5 * (1 + math.erf(spread / 13.86 / math.sqrt(2))))


def fit_cal(df: pd.DataFrame) -> IngameCal:
    """Fit per-checkpoint scaling from rows with ``t``, ``p_raw``, ``y`` and (optionally) ``p_mkt``."""
    from sklearn.linear_model import LogisticRegression

    cal = IngameCal()
    for i, t in enumerate(cal.ts):
        d = df[df["t"] == t]
        if "p_mkt" in d:
            d = d[d["p_mkt"].notna()]
        if len(d) < 40 or (d["y"] > 0.5).nunique() < 2:
            continue
        x = _logit(d["p_raw"]).reshape(-1, 1)
        if "p_mkt" in d:
            x = np.c_[x, _logit(d["p_mkt"]) * np.sqrt(d["gsr"].to_numpy() / 3600)]
        m = LogisticRegression(C=10.0).fit(x, (d["y"] > 0.5).astype(int))
        cal.a[i], cal.b[i] = float(m.intercept_[0]), float(m.coef_[0, 0])
        if x.shape[1] == 2:
            cal.c[i] = float(m.coef_[0, 1])
    return cal


# ---------------------------------------------------------------- historical states


def sample_states(pbp: pd.DataFrame, games: pd.DataFrame) -> pd.DataFrame:
    """First scrimmage play at/after each clock checkpoint, per completed game."""
    pbp = pbp.copy()
    for old, new in CANON.items():
        pbp["game_id"] = pbp["game_id"].str.replace(f"_{old}", f"_{new}", regex=False)
        for c in ("posteam", "home_team"):
            pbp[c] = pbp[c].replace(old, new)
    ok = set(games[games["home_score"].notna()]["game_id"])
    s = pbp[pbp["game_id"].isin(ok) & pbp["down"].notna() & pbp["posteam"].notna() & pbp["play_type"].isin(["pass", "run"])
            & (pbp["qtr"] <= 4) & pbp["home_wp"].notna()].sort_values(["game_id", "play_id"])
    rows = []
    for gid, g in s.groupby("game_id", sort=False):
        home = g["home_team"].iat[0]
        fr = 0 if g["posteam"].iat[0] == home else 1
        for t in CHECKPOINTS:
            c = g[g["game_seconds_remaining"] <= t]
            if c.empty:
                continue
            r = c.iloc[0]
            if r["game_seconds_remaining"] < t - 240:  # no snap near the checkpoint
                continue
            rows.append({"game_id": gid, "t": t, "gsr": float(r["game_seconds_remaining"]),
                         "hs": int(r["total_home_score"]), "as_": int(r["total_away_score"]),
                         "poss": 0 if r["posteam"] == home else 1, "yl": int(r["yardline_100"]),
                         "down": int(r["down"]), "ytg": int(r["ydstogo"]), "fr": fr, "nflfastr": float(r["home_wp"])})
    return pd.DataFrame(rows)


_L = None


def _init(L):
    global _L
    _L = L


def _task(args):
    key, spec, states, n = args
    eng = Engine(_L, spec)
    out = []
    for st in states:
        rnd = random.Random(zlib.crc32(f"{key}{st['t']}".encode()))
        w = 0.0
        for _ in range(n):
            r = eng.run_from(rnd, (st["hs"], st["as_"]), max(st["gsr"], 1), st["poss"], st["yl"], st["down"], st["ytg"], st["fr"])
            w += 1.0 if r["home"] > r["away"] else 0.5 if r["home"] == r["away"] else 0.0
        out.append(w / n)
    return key, out


def run_states(L, book, games: pd.DataFrame, tune, states: pd.DataFrame, n: int = 250, workers: int = 4) -> pd.DataFrame:
    from nfl_engine.matchup import make_spec

    by = {r.game_id: r for r in games.itertuples(index=False)}
    states = states.sort_values(["game_id", "t"], ascending=[True, False]).reset_index(drop=True)
    groups = list(states.groupby("game_id", sort=True))
    jobs = [(gid, make_spec(by[gid], book, L, tune), g.to_dict("records"), n) for gid, g in groups]
    with ProcessPoolExecutor(workers, initializer=_init, initargs=(L,)) as ex:
        res = dict(ex.map(_task, jobs, chunksize=max(1, len(jobs) // (workers * 6))))
    out = states.copy()
    out["p_raw"] = np.concatenate([res[gid] for gid, _ in groups])
    d = games.set_index("game_id").loc[out["game_id"]]
    hs, as_ = d["home_score"].to_numpy(), d["away_score"].to_numpy()
    out["y"] = np.where(hs > as_, 1.0, np.where(hs == as_, 0.5, 0.0))
    out["season"] = d["season"].to_numpy()
    out["p_mkt"] = [mkt_prob(x) for x in d["spread_line"]]
    return out


# ---------------------------------------------------------------- scoring


def score(df: pd.DataFrame, col: str) -> dict:
    p, y = np.clip(df[col].to_numpy(float), 0.005, 0.995), df["y"].to_numpy(float)
    keep = y != 0.5
    return {"brier": float(np.mean((p - y) ** 2)),
            "logloss": float(-np.mean(y * np.log(p) + (1 - y) * np.log(1 - p))),
            "acc": float(np.mean(((p > 0.5) == (y > 0.5))[keep]))}


def report(df: pd.DataFrame) -> pd.DataFrame:
    rows = []
    for t, d in list(df.groupby("t")) + [("all", df)]:
        r = {"checkpoint": t, "states": len(d)}
        for k, c in (("engine", "p_raw"), ("engine+cal", "p_cal"), ("nflfastR", "nflfastr")):
            if c in d:
                s = score(d, c)
                r[f"{k} brier"], r[f"{k} acc"] = round(s["brier"], 4), round(s["acc"], 3)
        rows.append(r)
    return pd.DataFrame(rows)


def backtest(bundle, games, book, pbp, train_end: int = 2023, per_season: int = 120, n: int = 250,
             workers: int = 4, seed: int = 3):
    """Sample games per season, simulate from checkpoint states, fit the calibrator on <=train_end, test after."""
    states = sample_states(pbp, games)
    states["season"] = games.set_index("game_id")["season"].reindex(states["game_id"]).to_numpy()
    rng = np.random.RandomState(seed)
    keep = []
    for _, g in states[states["season"] >= 2016].groupby("season"):
        ids = g["game_id"].unique()
        keep += list(rng.choice(ids, min(per_season, len(ids)), replace=False))
    states = states[states["game_id"].isin(keep)].reset_index(drop=True)
    df = run_states(bundle.league, book, games, bundle.tuning, states, n=n, workers=workers)
    cal = fit_cal(df[df["season"] <= train_end])
    df["p_cal"] = [cal.apply(p, g, m) for p, g, m in zip(df["p_raw"], df["gsr"], df["p_mkt"])]
    df["split"] = np.where(df["season"] <= train_end, "train", "test")
    return df, cal


# ---------------------------------------------------------------- live ledger: grade what we predicted, refit on misses

_last_rec: dict = {}


def record(event: str, gsr: float, p_raw: float, p_cal: float, hs: int, as_: int, final: bool = False,
           p_mkt: float | None = None) -> None:
    """Append one live reading (at most one per 45 game-seconds) so finished games can be graded later."""
    last = _last_rec.get(event)
    if not final and last is not None and abs(last - gsr) < 45:
        return
    _last_rec[event] = gsr
    LEDGER_DIR.mkdir(parents=True, exist_ok=True)
    row = {"gsr": gsr, "p_raw": p_raw, "p_cal": p_cal, "hs": hs, "as": as_, "final": final, "p_mkt": p_mkt}
    with open(LEDGER_DIR / f"ledger_{event}.jsonl", "a", encoding="utf-8") as f:
        f.write(json.dumps(row) + "\n")


def ledger_rows() -> pd.DataFrame:
    """One row per (finished game, checkpoint): the reading closest to each checkpoint, with the real result."""
    out = []
    for path in sorted(LEDGER_DIR.glob("ledger_*.jsonl")):
        recs = [json.loads(x) for x in path.read_text(encoding="utf-8").splitlines() if x.strip()]
        fin = next((r for r in reversed(recs) if r.get("final")), None)
        pts = [r for r in recs if not r.get("final")]
        if fin is None or not pts:
            continue
        y = 1.0 if fin["hs"] > fin["as"] else 0.5 if fin["hs"] == fin["as"] else 0.0
        for t in CHECKPOINTS:
            r = min(pts, key=lambda x: abs(x["gsr"] - t))
            if abs(r["gsr"] - t) <= 240:
                out.append({"event": path.stem[7:], "t": t, "gsr": r["gsr"], "p_raw": r["p_raw"], "p_cal": r["p_cal"], "p_mkt": r.get("p_mkt"), "y": y})
    return pd.DataFrame(out)


def live_report() -> dict:
    """Accuracy of the live readings on finished games plus the games the engine was confidently wrong about."""
    df = ledger_rows()
    misses = []
    for path in sorted(LEDGER_DIR.glob("ledger_*.jsonl")):
        recs = [json.loads(x) for x in path.read_text(encoding="utf-8").splitlines() if x.strip()]
        fin = next((r for r in reversed(recs) if r.get("final")), None)
        if fin is None or fin["hs"] == fin["as"]:
            continue
        home_won = fin["hs"] > fin["as"]
        wrong = [r for r in recs if not r.get("final") and ((r["p_cal"] > 0.8 and not home_won) or (r["p_cal"] < 0.2 and home_won))]
        if wrong:
            w = max(wrong, key=lambda r: abs(r["p_cal"] - 0.5))
            misses.append({"event": path.stem[7:], "peak_confidence": round(max(w["p_cal"], 1 - w["p_cal"]), 3),
                           "game_seconds_left": int(w["gsr"]), "final": f"{fin['hs']}-{fin['as']}"})
    if df.empty:
        return {"games": 0, "misses": misses}
    return {"games": int(df["event"].nunique()), "states": len(df), "raw": score(df, "p_raw"), "cal": score(df, "p_cal"),
            "misses": misses}


def refit_from_ledger(weight: int = 5) -> dict:
    """Nightly: refit the calibrator on historical backtest states plus every graded live reading (live counts more)."""
    live = ledger_rows()
    if len(live) < 20 or not STATES_PATH.exists():
        return {"skipped": "need graded live games", "live_states": len(live)}
    cols = ["t", "gsr", "p_raw", "p_mkt", "y"]
    hist = pd.read_csv(STATES_PATH)[cols]
    both = pd.concat([hist] + [live[cols]] * weight, ignore_index=True)
    cal = fit_cal(both)
    cal.save()
    return {"live_states": len(live), "a": [round(x, 3) for x in cal.a], "b": [round(x, 3) for x in cal.b],
            "c": [round(x, 3) for x in cal.c]}

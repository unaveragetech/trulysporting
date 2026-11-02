"""Train -> calibrate -> backtest -> save, plus prediction for upcoming games."""

from __future__ import annotations

import json
import pickle
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path

import numpy as np
import pandas as pd

from nfl_engine.backtest import (
    Calibrator, ats_report, box_realism, calibration_table, fit_calibrator, metrics, run_games, summarize)
from nfl_engine.data import SPORTS_DIR, load_games, load_pbp
from nfl_engine.league import League, fit_league
from nfl_engine.matchup import Tuning, played
from nfl_engine.ratings import Book, RatingParams, build_book, build_observations
from nfl_engine.residual import (
    ResidualBook, ResidualParams, apply_adjustment, fit_gain, run_residuals)

MODEL_PATH = SPORTS_DIR / "model.pkl"
FIRST_SEASON = 2015


@dataclass
class Bundle:
    league: League
    rating_params: RatingParams
    tuning: Tuning
    calibrator: Calibrator
    cal_raw: Calibrator
    resbook: ResidualBook
    train_end: int
    trained_at: str = ""
    report: dict = field(default_factory=dict)


def _log(msg: str) -> None:
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


def prepare(train_end: int, refresh: bool = False):
    games = load_games(refresh=refresh)
    games = games[games["season"] >= FIRST_SEASON].reset_index(drop=True)
    last = int(games["season"].max())
    pbp = load_pbp(list(range(FIRST_SEASON, last + 1)), refresh=refresh)
    L = fit_league(pbp[pbp["season"] <= train_end], rules_pbp=pbp)
    tg, qbg, _ = build_observations(pbp, L)
    return games, pbp, L, tg, qbg


def _score(df: pd.DataFrame) -> float:
    """Rating-quality objective: correlation of simulated and real margins (scale free)."""
    d = df.dropna(subset=["act_margin"])
    return float(np.corrcoef(d["sim_margin"], d["act_margin"])[0, 1])


def train(train_end: int = 2023, cal_years: int = 3, n_search: int = 60, n_cal: int = 200, n_test: int = 400, n_hist: int = 60,
          search: bool = True, refresh: bool = False, out_md: Path | None = None) -> Bundle:
    t0 = time.time()
    games, pbp, L, tg, qbg = prepare(train_end, refresh)
    pl = played(games)
    cal_games = pl[pl["season"].between(train_end - cal_years + 1, train_end)]
    test_games = pl[pl["season"] > train_end]
    _log(f"data ready: {len(pl)} completed games; calibrate on {len(cal_games)}, test on {len(test_games)}")

    P = RatingParams()
    tune = Tuning(hfa=1.2, eff=0.6)

    def corr_for(params: RatingParams, tn: Tuning) -> float:
        bk = build_book(games, tg, qbg, params)
        return _score(summarize(run_games(L, bk, cal_games, tn, n=n_search), cal_games))

    if search:
        best = corr_for(P, tune)
        _log(f"rating search baseline corr={best:.4f}")
        for sweep in range(2):
            moved = False
            for name in ("half_life", "carry", "k_scale", "qb_k_scale", "qb_carry"):
                cur = getattr(P, name)
                if name in ("carry", "qb_carry"):
                    values = (max(0.2, cur - 0.2), min(1.0, cur + 0.2))
                else:
                    values = (cur * 0.5, cur * 2.0)
                for v in values:
                    if abs(v - cur) < 1e-9:
                        continue
                    cand = RatingParams(**{**asdict(P), name: float(v)})
                    c = corr_for(cand, tune)
                    _log(f"  sweep {sweep} {name}={v:.2f}: corr={c:.4f}")
                    if c > best + 0.003:  # only move on a clear gain
                        best, P, moved = c, cand, True
                        break
            if not moved:
                break
        _log(f"chosen rating params {asdict(P)} corr={best:.4f}")
    book = build_book(games, tg, qbg, P)

    # --- solve home-field and efficiency levers so league margin/total match reality
    def means(tn: Tuning, n: int):
        s = summarize(run_games(L, book, cal_games, tn, n=n), cal_games)
        return s["sim_margin"].mean(), s["sim_total"].mean(), s

    act_m, act_t = cal_games["result"].mean(), cal_games["total"].mean()
    m00, t00, _ = means(Tuning(hfa=0, eff=0), n_search + 40)
    m10, _, _ = means(Tuning(hfa=1, eff=0), n_search + 40)
    _, t01, _ = means(Tuning(hfa=0, eff=1), n_search + 40)
    hfa = (act_m - m00) / max(m10 - m00, 1e-6)
    eff = (act_t - t00) / (t01 - t00)
    tune = Tuning(hfa=float(np.clip(hfa, 0, 3)), eff=float(np.clip(eff, -1, 3)))
    _log(f"levers: hfa={tune.hfa:.2f} eff={tune.eff:.2f} (actual margin {act_m:.2f}, total {act_t:.2f})")

    # --- how much of the rated deviation to trust: slope of real vs simulated margin
    for _ in range(2):
        s = summarize(run_games(L, book, cal_games, tune, n=n_cal), cal_games)
        slope = float(np.polyfit(s["sim_margin"], s["act_margin"], 1)[0])
        _log(f"dev_scale={tune.dev_scale:.2f}: slope real/sim margin = {slope:.2f}")
        if 0.93 < slope < 1.07:
            break
        tune.dev_scale = float(np.clip(tune.dev_scale * slope, 0.3, 2.5))
        m_, t_, _ = means(tune, n_search + 40)
        tune.hfa = float(np.clip(tune.hfa * (act_m / m_ if abs(m_) > 0.3 else 1.0), 0, 3))
    cal_df = summarize(run_games(L, book, cal_games, tune, n=n_cal), cal_games)
    cal_raw = fit_calibrator(cal_df)
    _log(f"play-level calibrator {asdict(cal_raw)}")

    # --- stage 2: per-team residual learning from every completed game before the test window
    hist_games = pl[(pl["season"] <= train_end) & (pl["season"] > FIRST_SEASON)
                    & ~pl["game_id"].isin(cal_games["game_id"])]
    _log(f"simulating {len(hist_games)} earlier games for residual learning")
    hist_df = summarize(run_games(L, book, hist_games, tune, n=n_hist), hist_games)
    train_df = pd.concat([hist_df, cal_df], ignore_index=True).sort_values(["gameday", "game_id"]).reset_index(drop=True)
    is_cal = train_df["game_id"].isin(cal_games["game_id"])
    best_rp, best_loss = ResidualParams(gain=0.0), None
    for hl in (15.0, 40.0):
        for k in (25.0, 60.0, 120.0):
            rp = ResidualParams(half_life=hl, k=k)
            ah, aa, _ = run_residuals(train_df, rp)
            g = float(np.clip(fit_gain(train_df[is_cal], ah[is_cal], aa[is_cal]), 0.0, 3.0))
            adj = apply_adjustment(train_df[is_cal], g * ah[is_cal], g * aa[is_cal])
            c = fit_calibrator(adj, "adj_margin", "adj_total")
            loss = float(np.abs(c.margin(adj["adj_margin"]) - adj["act_margin"]).mean()
                         + 0.5 * np.abs(c.total(adj["adj_total"]) - adj["act_total"]).mean())
            _log(f"  residual hl={hl} k={k} gain={g:.2f}: loss={loss:.3f}")
            if best_loss is None or loss < best_loss:
                best_loss, best_rp = loss, ResidualParams(half_life=hl, k=k, gain=g)
    ah, aa, resbook = run_residuals(train_df, best_rp)
    cal_adj = apply_adjustment(train_df[is_cal], ah[is_cal], aa[is_cal])
    cal = fit_calibrator(cal_adj, "adj_margin", "adj_total")
    _log(f"residual params {asdict(best_rp)}; final calibrator {asdict(cal)}")

    report: dict = {"train_end": train_end, "tuning": asdict(tune), "rating_params": asdict(P),
                    "residual_params": asdict(best_rp), "calibrator": asdict(cal), "n_cal_games": len(cal_games),
                    "n_test_games": len(test_games), "sims_per_game_test": n_test}
    report["calibration_set"] = metrics(cal_adj, cal, cal_raw)
    if len(test_games):
        _log(f"backtest on {len(test_games)} unseen games x {n_test} sims")
        res = run_games(L, book, test_games, tune, n=n_test)
        test_df = summarize(res, test_games).sort_values(["gameday", "game_id"]).reset_index(drop=True)
        th, ta, resbook = run_residuals(test_df, best_rp, resbook)  # keeps learning game by game
        test_df = apply_adjustment(test_df, th, ta)
        report["test"] = metrics(test_df, cal, cal_raw)
        report["test_by_season"] = {int(k): metrics(v, cal, cal_raw) for k, v in test_df.groupby("season")}
        report["test_ats"] = ats_report(test_df, cal)
        report["test_calibration_table"] = calibration_table(test_df, cal)
        report["box_realism"] = box_realism(res, test_games, tg)
        test_df.to_csv(SPORTS_DIR / "backtest_games.csv", index=False)
    bundle = Bundle(L, P, tune, cal, cal_raw, resbook, train_end, time.strftime("%Y-%m-%d %H:%M"), report)
    with open(MODEL_PATH, "wb") as f:
        pickle.dump(bundle, f)
    (SPORTS_DIR / "report.json").write_text(json.dumps(report, indent=2, default=float), encoding="utf-8")
    if out_md:
        out_md.write_text(render_report(report), encoding="utf-8")
    _log(f"done in {time.time() - t0:.0f}s")
    return bundle


def load_bundle() -> Bundle:
    with open(MODEL_PATH, "rb") as f:
        return pickle.load(f)


# ---------------------------------------------------------------- report text


def _pct(x):
    return f"{100 * x:.1f}%"


def render_report(r: dict) -> str:
    t = r.get("test", {})
    lines = ["# Sports engine backtest", "",
             f"Trained on seasons through **{r['train_end']}**; every game below was **unseen** by the model "
             f"(ratings use only pre-kickoff information).", ""]
    if t:
        raw, cal, mk = t["sim_raw"], t["sim_calibrated"], t.get("market", {})
        pl_ = t.get("sim_calibrated_play_level_only", raw)
        lines += [f"## Held-out games ({t['games']} games, {r['sims_per_game_test']} simulations each)", "",
                  "| Metric | Sim (raw) | Sim (calibrated) | Sim + team-residual stage | Closing market |",
                  "|---|---|---|---|---|"]
        rows = [("Winner accuracy", "win_acc", _pct), ("Brier score", "brier", lambda v: f"{v:.4f}"),
                ("Log loss", "logloss", lambda v: f"{v:.4f}"), ("Margin MAE (pts)", "margin_mae", lambda v: f"{v:.2f}"),
                ("Margin RMSE (pts)", "margin_rmse", lambda v: f"{v:.2f}"), ("Total MAE (pts)", "total_mae", lambda v: f"{v:.2f}")]
        for name, key, f in rows:
            lines.append(f"| {name} | {f(raw[key])} | {f(pl_[key])} | {f(cal[key])} | {f(mk[key]) if key in mk else '-'} |")
        lines += ["", f"Margin correlation sim vs actual: {cal['margin_corr']:.3f}; total correlation: {cal['total_corr']:.3f}. "
                  f"Bias (pred − actual) margin {cal['margin_bias']:+.2f}, total {cal['total_bias']:+.2f}.", ""]
    if r.get("test_by_season"):
        lines += ["## By season", "", "| Season | Games | Win acc | Margin MAE | Total MAE | Market win acc | Market MAE |", "|---|---|---|---|---|---|---|"]
        for s, m in r["test_by_season"].items():
            c, mk = m["sim_calibrated"], m.get("market", {})
            lines.append(f"| {s} | {m['games']} | {_pct(c['win_acc'])} | {c['margin_mae']:.2f} | {c['total_mae']:.2f} | "
                         f"{_pct(mk['win_acc']) if mk else '-'} | {mk['margin_mae']:.2f} |" if mk else
                         f"| {s} | {m['games']} | {_pct(c['win_acc'])} | {c['margin_mae']:.2f} | {c['total_mae']:.2f} | - | - |")
        lines.append("")
    if r.get("test_calibration_table"):
        lines += ["## Win-probability calibration (held-out)", "", "| Predicted | Actual | Games |", "|---|---|---|"]
        lines += [f"| {_pct(x['p_pred'])} | {_pct(x['p_actual'])} | {x['n']} |" for x in r["test_calibration_table"]]
        lines.append("")
    if r.get("box_realism"):
        lines += ["## Box-score realism (simulated vs real team stat lines, held-out)", "",
                  "| Stat | Sim avg | Real avg | Per-game correlation |", "|---|---|---|---|"]
        lines += [f"| {x['stat']} | {x['sim']:.2f} | {x['real']:.2f} | {x['corr']:.2f} |" for x in r["box_realism"]]
        lines.append("")
    if r.get("test_ats"):
        lines += ["## Sim vs the closing spread (held-out)", "",
                  "Share of games where the side the sim preferred covered. 50% is break-even before vig; "
                  "~52.4% is break-even at −110.", "", "| Edge threshold | Games | Sim side covered |", "|---|---|---|"]
        lines += [f"| {k} | {v['bets']} | {_pct(v['ats_win_pct'])} |" for k, v in r["test_ats"].items()]
        lines.append("")
    lines += ["## Fitted levers", "", "```json", json.dumps({"tuning": r["tuning"], "ratings": r["rating_params"], "residual": r.get("residual_params")}, indent=2), "```", ""]
    return "\n".join(lines)

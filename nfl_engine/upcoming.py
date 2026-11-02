"""Simulate unplayed games and surface the ones worth a closer look."""

from __future__ import annotations

import copy
from pathlib import Path

import numpy as np
import pandas as pd

from nfl_engine.backtest import run_games, summarize
from nfl_engine.residual import run_residuals
from nfl_engine.data import SPORTS_DIR, load_games, load_pbp
from nfl_engine.matchup import Tuning, weather_of
from nfl_engine.pipeline import FIRST_SEASON, Bundle, load_bundle
from nfl_engine.ratings import STATS, QB_STATS, build_book, build_observations


def _ml_prob(ml: float) -> float:
    if ml != ml:
        return float("nan")
    return 100 / (ml + 100) if ml > 0 else -ml / (-ml + 100)


def qb_override(book, bundle: Bundle, team_snap, qb_id: str):
    """Swap the starting quarterback of a snapshot for another player using current QB ratings."""
    qb = book.state["qb"]
    snap = copy.copy(team_snap)
    snap.qb = {st: qb.dev((qb_id, st), STATS[st][2] * bundle.rating_params.qb_k_scale) for st in QB_STATS}
    snap.qb_id = qb_id
    return snap


def fresh_book(bundle: Bundle, refresh: bool = False):
    games = load_games(refresh=refresh)
    games = games[games["season"] >= FIRST_SEASON].reset_index(drop=True)
    pbp = load_pbp(list(range(FIRST_SEASON, int(games["season"].max()) + 1)), refresh=refresh)
    tg, qbg, _ = build_observations(pbp, bundle.league)
    return games, build_book(games, tg, qbg, bundle.rating_params)


def catch_up(bundle: Bundle, games: pd.DataFrame, book, n: int = 60) -> None:
    """Fold games completed since training into the team-residual book (simulating each pre-game)."""
    from nfl_engine.matchup import played

    rb = bundle.resbook
    new = played(games)
    new = new[~new["game_id"].isin(rb.done) & (new["season"] > 2015)]
    if new.empty:
        return
    df = summarize(run_games(bundle.league, book, new, bundle.tuning, n=n), new)
    run_residuals(df.sort_values(["gameday", "game_id"]).reset_index(drop=True), rb.p, rb)


def simulate_upcoming(bundle: Bundle, games: pd.DataFrame, book, n: int = 3000, week: int | None = None,
                      qb_overrides: dict | None = None, workers: int | None = None) -> pd.DataFrame:
    today = pd.Timestamp.today().normalize()
    todo = games[games["home_score"].isna() & (games["gameday"] >= today - pd.Timedelta(days=1))]
    if week is not None:
        todo = todo[todo["week"] == week]
    else:  # default: the next slate that has market lines or is within ~a week
        horizon = todo["gameday"].min() + pd.Timedelta(days=7) if len(todo) else today
        todo = todo[todo["gameday"] <= horizon]
    if todo.empty:
        return pd.DataFrame()
    if qb_overrides:
        for r in todo.itertuples(index=False):
            snaps = book.snaps[r.game_id]
            for side, team in (("home", r.home_team), ("away", r.away_team)):
                if team in qb_overrides:
                    snaps[side] = qb_override(book, bundle, snaps[side], qb_overrides[team])
    res = run_games(bundle.league, book, todo, bundle.tuning, n=n, workers=workers)
    cal = bundle.calibrator
    rb = bundle.resbook
    rows = []
    for r in todo.itertuples(index=False):
        x = res[r.game_id]
        ah, aa = rb.adj(r.home_team, r.away_team)
        raw_m = x["margin"].astype(float) + (ah - aa)
        raw_t = (x["home"] + x["away"]).astype(float) + (ah + aa)
        m, t = cal.margin(raw_m), cal.total(raw_t)
        pm, pt = float(m.mean()), float(t.mean())
        pw = float(cal.pwin(raw_m.mean()))
        spread, tl = r.spread_line, r.total_line
        snaps = book.snaps[r.game_id]
        wx = weather_of(r)
        row = {
            "game_id": r.game_id, "week": r.week, "day": r.gameday.date(), "away": r.away_team, "home": r.home_team,
            "away_qb": getattr(r, "away_qb_name", None), "home_qb": getattr(r, "home_qb_name", None),
            "proj_away": pt / 2 - pm / 2, "proj_home": pt / 2 + pm / 2, "model_spread": pm, "model_total": pt,
            "p_home": pw, "market_spread": spread, "market_total": tl,
            "edge_spread": pm - spread if spread == spread else np.nan,
            "edge_total": pt - tl if tl == tl else np.nan,
            "p_cover_home": float((m > spread).mean()) if spread == spread else np.nan,
            "p_over": float((t > tl).mean()) if tl == tl else np.nan,
            "p_home_market": _ml_prob(r.home_moneyline) / (_ml_prob(r.home_moneyline) + _ml_prob(r.away_moneyline))
            if r.home_moneyline == r.home_moneyline else np.nan,
            "p_home_margin_ge_7": float((m >= 7).mean()), "p_away_margin_ge_7": float((m <= -7).mean()),
            "weather": ("dome" if wx[2] else f"{getattr(r, 'temp', np.nan):.0f}F wind {getattr(r, 'wind', np.nan):.0f}")
            if (wx[2] or getattr(r, 'temp', np.nan) == getattr(r, 'temp', np.nan)) else "n/a",
            "box_pass_home": x["box"]["pass_yds"][0], "box_pass_away": x["box"]["pass_yds"][1],
            "box_rush_home": x["box"]["rush_yds"][0], "box_rush_away": x["box"]["rush_yds"][1],
            "to_home": x["box"]["to"][0], "to_away": x["box"]["to"][1],
            "qb_games_home": snaps["home"].qb_games, "qb_games_away": snaps["away"].qb_games,
        }
        row["flags"] = flags(row)
        row["interest"] = interest(row)
        rows.append(row)
    return pd.DataFrame(rows).sort_values(["day", "interest"], ascending=[True, False]).reset_index(drop=True)


def flags(r: dict) -> list[str]:
    f = []
    es, et = r["edge_spread"], r["edge_total"]
    if es == es and abs(es) >= 2.0:
        side = r["home"] if es > 0 else r["away"]
        f.append(f"SPREAD lean {side} ({es:+.1f} vs line)")
    if et == et and abs(et) >= 3.0:
        f.append(f"TOTAL lean {'OVER' if et > 0 else 'UNDER'} ({et:+.1f} vs line)")
    ph, pm = r["p_home"], r["p_home_market"]
    if pm == pm:
        if ph - pm >= 0.06 and pm < 0.5:
            f.append(f"UPSET watch {r['home']} ({ph:.0%} vs mkt {pm:.0%})")
        if (1 - ph) - (1 - pm) >= 0.06 and (1 - pm) < 0.5:
            f.append(f"UPSET watch {r['away']} ({1 - ph:.0%} vs mkt {1 - pm:.0%})")
    if abs(r["model_spread"]) < 2.5:
        f.append("coin-flip")
    if r["model_total"] >= 51:
        f.append("shootout")
    elif r["model_total"] <= 38:
        f.append("grinder")
    if r["qb_games_home"] < 150 or r["qb_games_away"] < 150:
        f.append("thin QB sample")
    return f


def interest(r: dict) -> float:
    s = 0.0
    if r["edge_spread"] == r["edge_spread"]:
        s += abs(r["edge_spread"])
    if r["edge_total"] == r["edge_total"]:
        s += 0.6 * abs(r["edge_total"])
    s += 6 * (1 - abs(2 * r["p_home"] - 1))  # closer games are more interesting
    return float(s)


def to_markdown(df: pd.DataFrame, bundle: Bundle) -> str:
    out = [f"# Sim slate ({bundle.trained_at} model, trained through {bundle.train_end})", "",
           "Calibrated Monte-Carlo projections; edges are model minus closing/current market line "
           "(spread positive = home favoured). Exploratory analytics, not betting advice.", "",
           "| Day | Matchup (QBs) | Proj | Win% (home) | Mkt spread | Model spread | Edge | Mkt total | Model total | Wx | Flags |",
           "|---|---|---|---|---|---|---|---|---|---|---|"]
    for r in df.itertuples(index=False):
        mk = f"{r.market_spread:+.1f}" if r.market_spread == r.market_spread else "-"
        mt = f"{r.market_total:.1f}" if r.market_total == r.market_total else "-"
        ed = f"{r.edge_spread:+.1f}" if r.edge_spread == r.edge_spread else "-"
        out.append(f"| {r.day} | {r.away} @ {r.home} ({r.away_qb} / {r.home_qb}) | {r.proj_away:.0f}-{r.proj_home:.0f} | "
                   f"{r.p_home:.0%} | {mk} | {r.model_spread:+.1f} | {ed} | {mt} | {r.model_total:.1f} | {r.weather} | "
                   f"{'; '.join(r.flags)} |")
    return "\n".join(out)


def run_cli(a) -> None:
    bundle = load_bundle()
    games, book = fresh_book(bundle)
    catch_up(bundle, games, book)
    if a.cmd == "upcoming":
        df = simulate_upcoming(bundle, games, book, n=a.sims, week=a.week)
    else:
        sel = games[games["home_score"].isna() & (games["home_team"] == a.home.upper()) &
                    (games["away_team"] == a.away.upper())]
        if sel.empty:
            raise SystemExit(f"no unplayed {a.away.upper()} @ {a.home.upper()} game on the schedule")
        week = int(sel.iloc[0]["week"])
        df = simulate_upcoming(bundle, games, book, n=a.sims, week=week)
        df = df[(df["home"] == a.home.upper()) & (df["away"] == a.away.upper())]
    if df.empty:
        print("nothing to simulate")
        return
    md = to_markdown(df, bundle)
    print(md)
    if getattr(a, "out", None):
        Path(a.out).write_text(md, encoding="utf-8")
    df.to_csv(SPORTS_DIR / "upcoming.csv", index=False)

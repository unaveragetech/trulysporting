from __future__ import annotations

import argparse
from pathlib import Path


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(prog="python -m nfl_engine", description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    t = sub.add_parser("train", help="fit league model + ratings, calibrate on completed games, backtest on later ones")
    t.add_argument("--train-end", type=int, default=2023)
    t.add_argument("--cal-years", type=int, default=3)
    t.add_argument("--sims", type=int, default=400, help="simulations per held-out game")
    t.add_argument("--no-search", action="store_true", help="skip the rating hyper-parameter search")
    t.add_argument("--refresh", action="store_true", help="re-download data")
    t.add_argument("--report", default="docs/NFL_ENGINE_BACKTEST.md")
    u = sub.add_parser("upcoming", help="simulate every unplayed game with a posted schedule")
    u.add_argument("--sims", type=int, default=3000)
    u.add_argument("--week", type=int, default=None)
    u.add_argument("--out", default=None, help="write markdown here")
    p = sub.add_parser("predict", help="simulate one matchup")
    p.add_argument("home")
    p.add_argument("away")
    p.add_argument("--sims", type=int, default=5000)
    g = sub.add_parser("ingame", help="backtest the live win probability from mid-game states and fit its calibrator")
    g.add_argument("--per-season", type=int, default=120)
    g.add_argument("--sims", type=int, default=250)
    g.add_argument("--workers", type=int, default=4)
    g.add_argument("--refit", action="store_true", help="refit the calibrator from saved states only")
    a = ap.parse_args(argv)
    if a.cmd == "ingame":
        from nfl_engine.ingame_cli import run
        run(a)
    elif a.cmd == "train":
        from nfl_engine.pipeline import train
        train(train_end=a.train_end, cal_years=a.cal_years, n_test=a.sims, search=not a.no_search,
              refresh=a.refresh, out_md=Path(a.report))
    else:
        from nfl_engine.upcoming import run_cli
        run_cli(a)

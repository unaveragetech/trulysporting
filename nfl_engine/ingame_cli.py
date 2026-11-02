"""CLI driver for the in-game backtest (kept out of ingame.py so importing that stays light)."""

from __future__ import annotations

from pathlib import Path

from nfl_engine import ingame
from nfl_engine.data import SPORTS_DIR, load_pbp
from nfl_engine.pipeline import FIRST_SEASON, load_bundle
from nfl_engine.upcoming import fresh_book


def run(a) -> None:
    if getattr(a, "refit", False):  # refit the calibrator from the saved backtest states without re-simulating
        import pandas as pd

        from nfl_engine.data import load_games

        df = pd.read_csv(ingame.STATES_PATH)
        g = load_games().set_index("game_id")
        df["p_mkt"] = [ingame.mkt_prob(x) for x in g.loc[df["game_id"], "spread_line"]]
        cal = ingame.fit_cal(df[df["season"] <= 2023])
        df["p_cal"] = [cal.apply(p, t, m) for p, t, m in zip(df["p_raw"], df["gsr"], df["p_mkt"])]
        df["split"] = ["train" if s <= 2023 else "test" for s in df["season"]]
        return _finish(df, cal)
    bundle = load_bundle()
    games, book = fresh_book(bundle)
    seasons = list(range(max(FIRST_SEASON, 2016), int(games["season"].max()) + 1))
    import pandas as pd

    pbp = pd.concat([load_pbp([s]) for s in seasons], ignore_index=True)
    df, cal = ingame.backtest(bundle, games, book, pbp, per_season=a.per_season, n=a.sims, workers=a.workers)
    del pbp
    _finish(df, cal)


def _finish(df, cal) -> None:
    df.to_csv(ingame.STATES_PATH, index=False)
    cal.save()
    test = df[df["split"] == "test"]
    rep = ingame.report(test)
    print(rep.to_string(index=False))
    md = ["# In-game win probability backtest", "",
          f"Held-out seasons after the calibrator's training window: {len(test)} checkpoint states from "
          f"{test['game_id'].nunique()} games. Brier: lower is better; acc = share of states whose leader went on to win.", "",
          rep.to_markdown(index=False), "",
          f"Calibrator (per clock checkpoint): a={['%.2f' % x for x in cal.a]}, b={['%.2f' % x for x in cal.b]}, market weight c={['%.2f' % x for x in cal.c]}"]
    Path("docs/NFL_ENGINE_INGAME.md").write_text("\n".join(md), encoding="utf-8")

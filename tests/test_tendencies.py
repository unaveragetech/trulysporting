import numpy as np
import pandas as pd

from nfl_engine.tendencies import KEY_IDX, TendBook


def _plays(n_games=6, pass_boost=0.3):
    """Team A passes `pass_boost` more than the model expects on 3rd & medium; everything else neutral."""
    rng = np.random.RandomState(0)
    rows = []
    for g in range(n_games):
        for i in range(60):
            rows.append({"game_id": f"g{g}", "season": 2024, "posteam": "A", "defteam": "B", "dd": "3m", "sc": "T0h1",
                         "zone": "mid", "resp": "open", "all": "all", "p0": 0.5,
                         "is_pass": float(rng.rand() < 0.5 + pass_boost)})
            rows.append({"game_id": f"g{g}", "season": 2024, "posteam": "B", "defteam": "A", "dd": "3m", "sc": "T0h1",
                         "zone": "mid", "resp": "open", "all": "all", "p0": 0.5, "is_pass": float(rng.rand() < 0.5)})
    d = pd.DataFrame(rows)
    d["resid"] = d["is_pass"] - d["p0"]
    return d


def _games(n=6):
    return pd.DataFrame({"game_id": [f"g{i}" for i in range(n)], "season": 2024,
                         "gameday": pd.date_range("2024-09-08", periods=n, freq="7D")})


def test_estimates_use_only_earlier_games_and_learn_the_tendency():
    tb = TendBook(half_life=10, prior=40, hist_from=2024)
    tb.build(_plays(), _games(), fit_seasons=(2024, 2024))
    k = KEY_IDX[("off", "dd", "3m")]
    assert tb.hist[("A", "g0")][k] == 0.0  # nothing known before the first game
    assert tb.hist[("A", "g5")][k] > tb.hist[("A", "g1")][k] > 0  # grows as evidence accumulates
    assert tb.hist[("B", "g5")][k] < tb.hist[("A", "g5")][k]
    sh = tb.shifts("A", "B", "future", "2024-12-01")
    assert sh["dd"]["3m"] > 0 and "T0h1" in sh["sc"]


def test_update_adds_new_games_once():
    tb = TendBook(hist_from=2024)
    plays, games = _plays(), _games()
    tb.build(plays[plays["game_id"] != "g5"], games[games["game_id"] != "g5"], fit_seasons=(2024, 2024))
    before = tb.state[("A", "off", "dd", "3m")][1]
    assert tb.update(plays, games) == 1
    assert tb.state[("A", "off", "dd", "3m")][1] > before * 0.9
    assert tb.update(plays, games) == 0  # already folded in

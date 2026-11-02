import numpy as np
import pandas as pd

from nfl_engine import ingame


def test_cal_identity_by_default_and_monotone():
    cal = ingame.IngameCal()
    assert abs(cal.apply(0.7, 1800) - 0.7) < 1e-6
    ps = [cal.apply(p, 900) for p in (0.1, 0.4, 0.6, 0.9)]
    assert ps == sorted(ps)


def test_fit_cal_shrinks_overconfident_probabilities():
    rng = np.random.RandomState(0)
    p_true = rng.uniform(0.2, 0.8, 4000)
    y = (rng.uniform(size=4000) < p_true).astype(float)
    raw = 1 / (1 + np.exp(-2.5 * np.log(p_true / (1 - p_true))))  # engine is too confident
    df = pd.DataFrame({"t": 1800, "p_raw": raw, "y": y})
    cal = ingame.fit_cal(df)
    assert cal.b[2] < 0.7
    assert abs(cal.apply(0.5, 1800) - 0.5) < 0.05


def test_ledger_grades_finished_game_and_flags_misses(tmp_path, monkeypatch):
    monkeypatch.setattr(ingame, "LEDGER_DIR", tmp_path)
    monkeypatch.setattr(ingame, "_last_rec", {})
    for gsr, p in ((3290, 0.55), (2700, 0.6), (1800, 0.85), (900, 0.9), (300, 0.8)):
        ingame.record("e1", gsr, p, p, 10, 7)
    ingame.record("e1", 0, 0.5, 0.5, 14, 20, final=True)  # the 85-90% favourite lost
    df = ingame.ledger_rows()
    assert len(df) == 5 and set(df["y"]) == {0.0}
    rep = ingame.live_report()
    assert rep["games"] == 1 and rep["misses"][0]["peak_confidence"] == 0.9

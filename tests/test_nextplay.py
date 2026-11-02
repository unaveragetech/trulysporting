import random

import pytest

from nfl_engine import nextplay
from nfl_engine.pipeline import MODEL_PATH, load_bundle
from nfl_engine.sim import GameSpec, SideParams


@pytest.fixture(scope="module")
def league():
    if not MODEL_PATH.exists():
        pytest.skip("no trained model")
    return load_bundle().league


def test_projection_probabilities_are_sane(league):
    spec = GameSpec(home="KC", away="BUF", sides=(SideParams(), SideParams()))
    st = {"down": 3, "ytg": 8, "yl": 40, "poss": 0, "hs": 7, "as": 10, "gsr": 1200.0, "first_recv": 1}
    r = nextplay.project(league, spec, st, n_plays=5, sims=200)
    s1 = r["steps"][0]
    assert s1["p_pass"] > 0.8  # 3rd and long
    for s in r["steps"]:
        assert 0.99 <= s["p_pass"] + s["p_run"] + s["p_punt"] + s["p_fg"] + s["p_game_over"] <= 1.01
    assert abs(sum(q["prob"] for q in r["sequences"]) - 1) < 0.9 and len(r["sequences"]) >= 1


def test_ig_shift_moves_pass_probability_up(league):
    spec = GameSpec(home="KC", away="BUF", sides=(SideParams(tshift={"all": 0.0, "dd": {}, "sc": {}, "zone": {}, "resp": {}}), SideParams()))
    from nfl_engine.sim import Engine
    base = Engine(league, spec)._pass_prob(spec.sides[0], 1, 10, 60, 0, 2, 600, 1500, 0, 0)
    hot = nextplay._with_ig(spec, 0, 0.2)
    up = Engine(league, hot)._pass_prob(hot.sides[0], 1, 10, 60, 0, 2, 600, 1500, 0, 0)
    assert up > base

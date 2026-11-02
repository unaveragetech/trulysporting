"""Offline checks for the live-play parsing and tuning bounds (no network)."""

from nfl_engine import livetune
from nfl_engine.liveplay import abbr, classify, clock_secs


def _p(typ, text="", scoring=False, penalty=False):
    return {"type": {"text": typ}, "text": text, "scoringPlay": scoring, "isPenalty": penalty}


def test_classify_scrimmage_plays():
    assert classify(_p("Pass Reception", "J.Doe pass short left to X for 5 yards"))[0] == "comp"
    assert classify(_p("Pass Incompletion"))[0] == "inc"
    assert classify(_p("Rush", "A.Back up the middle"))[0] == "run"
    assert classify(_p("Sack"))[0] == "sack"
    assert classify(_p("Passing Touchdown", "pass to X for 20 yards, TOUCHDOWN", scoring=True)) == ("comp", True)
    assert classify(_p("Punt"))[0] == "punt"
    assert classify(_p("Kickoff"))[0] == "other"
    assert classify(_p("Penalty"))[0] == "penalty"


def test_clock_and_abbreviations():
    assert clock_secs("13:02") == 782
    assert clock_secs("") == 0
    assert abbr("LAR") == "LA" and abbr("WSH") == "WAS" and abbr("KC") == "KC"


def test_live_adjustment_bounds():
    for k, (_n0, _eta, bound) in livetune.SPEC.items():
        assert bound > 0

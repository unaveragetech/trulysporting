import math

import pandas as pd

import parlay_pricing as PP
import parlay_rel as R
import parlays as P

START = (pd.Timestamp.now(tz="UTC") + pd.Timedelta(hours=5)).isoformat()


def mk(i, p, kind="ml", market=True, model=True, quotes=(), info=None, gid=None, start=START):
    srcs = []
    if market:
        srcs.append(P.Source("DraftKings", "market", p, "x"))
    if model:
        srcs.append(P.Source("Team-form model", "model", p, "x"))
    return P.Leg(f"L{i}", gid or f"g{i}", "basketball/nba", "NBA", f"A{i} @ B{i}", start, "pre", kind, f"Pick {i}", p,
                 sources=srcs, quotes=list(quotes), info=info or {}, meta={"kind": kind, "side": "home"})


def pool(ps):
    return [mk(i, p) for i, p in enumerate(ps)]


def test_reliability_rewards_market_agreement_and_punishes_thin_evidence():
    solid = mk(1, 0.8, quotes=[PP.quote(b, "sportsbook", -200, 170, None, "Unabated", ts="t") for b in ("DraftKings", "FanDuel", "BetMGM")])
    model_only = mk(2, 0.8, market=False)
    q_player = mk(3, 0.8, kind="player", market=False, model=False, info={"games_used": 7, "hits": 4, "listed_questionable": True})
    a, b, c = (R.reliability(x) for x in (solid, model_only, q_player))
    assert a["score"] > b["score"] > c["score"] and a["label"] == "High" and c["label"] == "Low"
    assert any("questionable" in t for _, t in c["reasons"]) and 5 <= c["score"] <= 95


def test_disagreeing_model_and_market_lowers_reliability():
    l = mk(1, 0.7)
    l.sources = [P.Source("DK", "market", 0.80, ""), P.Source("Team-form model", "model", 0.55, "")]
    assert any("disagree" in t for _, t in R.reliability(l)["reasons"])


def test_parlay_reliability_is_dragged_down_by_the_weakest_leg():
    good = [mk(i, 0.8) for i in range(3)]
    weak = mk(9, 0.8, market=False)
    assert R.parlay_reliability(good + [weak]) < R.parlay_reliability(good)


def test_stacking_likely_legs_goes_up_to_many_legs():
    legs = pool([0.95, 0.93, 0.92, 0.91, 0.9, 0.9, 0.89, 0.88, 0.87, 0.86, 0.85])
    out = P.build_parlays(legs, 8, 10, 5, 0.8)
    assert out and all(8 <= x.k <= 10 for x in out)
    assert abs(out[0].p - math.prod(l.p for l in out[0].legs)) < 1e-9


def test_chance_band_returns_only_parlays_inside_it():
    legs = pool([0.9, 0.85, 0.8, 0.78, 0.75, 0.72, 0.7, 0.68, 0.66, 0.64, 0.62, 0.6])
    out = P.build_parlays(legs, 4, 8, 6, 0.55, min_parlay_p=0.08, max_parlay_p=0.35, rank="balanced")
    assert out and all(0.08 <= x.p <= 0.35 for x in out)  # the strongest combos are well above 35%, the band still finds its own


def test_must_include_forces_a_leg_and_drops_rivals_from_its_game():
    legs = pool([0.95, 0.93, 0.9, 0.88, 0.86, 0.84]) + [mk(20, 0.6, gid="g0")]
    out = P.build_parlays(legs, 3, 4, 5, 0.5, must_include=("L20",))
    assert out and all(any(l.key == "L20" for l in x.legs) for x in out)
    assert all(sum(l.game_id == "g0" for l in x.legs) == 1 for x in out)  # the other g0 leg is not used alongside it


def test_require_priced_and_min_reliability_filter_legs():
    q = PP.quote("DraftKings", "sportsbook", -200, 170, None, "Unabated", ts="t")
    legs = [mk(i, 0.8, quotes=[q] if i < 4 else []) for i in range(8)]
    out = P.build_parlays(legs, 3, 4, 10, 0.5, require_priced=True)
    assert out and all(l.key in {"L0", "L1", "L2", "L3"} for x in out for l in x.legs)
    weak = [mk(i, 0.8, market=False) for i in range(6)]
    assert P.build_parlays(weak, 3, 4, 5, 0.5, min_rel=70) == []


def test_rank_modes_order_differently():
    strong = [mk(i, 0.72) for i in range(4)]
    flimsy = [mk(10 + i, 0.78, market=False) for i in range(4)]
    legs = strong + flimsy
    likely = P.build_parlays(legs, 4, 4, 1, 0.5, rank="likely")[0]
    reliable = P.build_parlays(legs, 4, 4, 1, 0.5, rank="reliable")[0]
    assert all(l.key.startswith("L1") for l in likely.legs)      # higher chance, but model only
    assert all(int(l.key[1:]) < 4 for l in reliable.legs)        # market backed wins on reliability


def test_leg_odds_and_drop_one():
    q1 = PP.quote("DraftKings", "sportsbook", -150, 130, None, "Unabated", ts="t")
    q2 = PP.quote("FanDuel", "sportsbook", -140, 120, None, "Unabated", ts="t")
    l = mk(1, 0.65, quotes=[q1, q2])
    o = R.leg_odds(l)
    assert o["best_book"] == "FanDuel" and o["best_price"] == -140 and o["fair"] == -186 and o["n_books"] == 2
    legs = [mk(i, p) for i, p in enumerate([0.9, 0.8, 0.7])]
    rows = R.drop_one(legs)
    assert len(rows) == 3 and abs(rows[2]["chance"] - 0.72) < 1e-9 and rows[2]["gain"] > 0
    assert R.drop_one(legs[:2]) == []


def test_presets_define_every_generator_knob():
    keys = {"k", "min_p", "rank", "pmin", "pmax", "min_rel", "priced", "per_game", "max_pl"}
    for name, d in R.PRESETS.items():
        if "Custom" not in name:
            assert keys <= set(d), name
    assert R.DEFAULT_PRESET in R.PRESETS

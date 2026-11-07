import math

import parlays as P


def _game(i, ep="basketball/nba", state="pre", **kw):
    g = {"id": str(i), "ep": ep, "league": "NBA", "home": f"Home{i}", "away": f"Away{i}", "home_abbr": f"H{i}", "away_abbr": f"A{i}",
         "start": "2026-11-08T00:00Z", "state": state, "home_ml": -200, "away_ml": 170, "book": "ESPN BET", "kalshi_home": 0.66,
         "spread": -5.5, "total": 220.5, "home_score": 0, "away_score": 0, "period": 0, "clock": ""}
    g.update(kw)
    return g


def test_devig_and_odds_helpers():
    assert abs(P.devig_home(-200, 170) - 0.6429) < 0.002  # removes the book's margin
    assert P.prob_to_american(0.75) == -300 and P.prob_to_american(0.25) == 300
    assert abs(P.decimal_odds(-200) - 1.5) < 1e-9 and abs(P.decimal_odds(150) - 2.5) < 1e-9


def test_moneyline_leg_is_market_anchored_and_records_sources():
    pred = {"margin": 9.0, "p_home": 0.77, "home_pts": 115, "away_pts": 106}
    legs = P.ml_legs(_game(1), pred, 0.3, None, None)
    home = next(l for l in legs if l.key.endswith("home"))
    assert 0.62 < home.p < 0.77  # between market (~64%) and the model (77%), closer to the market
    names = {s.name for s in home.sources}
    assert {"Team-form model", "ESPN BET", "Kalshi"} <= names
    assert home.price == -200 and all(l.p > 0.5 for l in legs)


def test_live_legs_use_game_state_and_have_no_price():
    pred = {"margin": 2.0, "p_home": 0.57, "home_pts": 110, "away_pts": 108}
    lp = {"f": 0.25, "margin": 18.0, "p_home": 0.97, "p_draw": 0, "home_final": 121.0, "away_final": 103.0}
    g = _game(2, state="in", home_score=80, away_score=62, period=3, clock="4:00")
    legs = P.ml_legs(g, pred, 0.3, None, lp) + P.spread_total_legs(g, pred, 0.3, lp)
    ml = next(l for l in legs if l.kind == "ml" and l.key.endswith("home"))
    assert ml.live and ml.price is None and ml.p == P.MAX_LEG_P  # capped, never a lock
    sp = next(l for l in legs if l.kind == "spread")
    assert sp.live and "live" in sp.notes[0]


def test_spread_and_total_legs_hover_near_even_when_anchored_to_the_line():
    pred = {"margin": 8.0, "p_home": 0.72, "home_pts": 117, "away_pts": 109}
    legs = P.spread_total_legs(_game(3), pred, 0.3, None)
    assert legs and all(0.5 < l.p < 0.62 for l in legs)  # markets are efficient: no free lunch


def _legs(n_games=10):
    legs = []
    for i in range(n_games):
        legs.append(P.Leg(f"{i}:ml:home", str(i), "ep", "L", f"A{i} @ H{i}", "", "pre", "ml", f"Team{i} to win", 0.95 - 0.02 * i, -300,
                          [P.Source("Model", "model", 0.9, "x")]))
        legs.append(P.Leg(f"{i}:total:over", str(i), "ep", "L", f"A{i} @ H{i}", "", "pre", "total", f"Over {i}", 0.7 - 0.01 * i, None,
                          [P.Source("Model", "model", 0.7, "x")]))
        legs.append(P.Leg(f"{i}:pl:x", str(i), "ep", "L", f"A{i} @ H{i}", "", "pre", "player", f"Player{i} 20+ points", 0.9 - 0.02 * i, None,
                          [P.Source("Player history", "player", 0.9, "x")]))
    return legs


def test_build_parlays_respects_leg_counts_one_leg_per_game_and_player_cap():
    res = P.build_parlays(_legs(), kmin=4, kmax=7, top=10, min_p=0.6, max_player=2)
    assert len(res) == 10 and all(4 <= r.k <= 7 for r in res)
    assert {r.k for r in res} >= {4, 5, 6, 7}  # offers every leg count
    for r in res:
        games = [l.game_id for l in r.legs]
        assert len(games) == len(set(games))
        assert sum(l.kind == "player" for l in r.legs) <= 2
        assert abs(r.p - math.prod(l.p for l in r.legs)) < 1e-12
    # diverse: no two parlays are the same set, and none shares more than k-2 legs with another
    for i, a in enumerate(res):
        for b in res[i + 1:]:
            ka, kb = {l.key for l in a.legs}, {l.key for l in b.legs}
            assert ka != kb and len(ka & kb) <= max(1, min(a.k, b.k) - 2) + 2
    assert res == sorted(res, key=lambda r: -r.score)


def test_min_probability_filter_and_too_few_games():
    assert P.build_parlays(_legs(3), kmin=4) == []
    res = P.build_parlays(_legs(), kmin=4, kmax=4, min_p=0.9, top=3)
    assert all(l.p >= 0.9 for r in res for l in r.legs)


def test_value_ranking_prefers_priced_legs_and_reports_ev():
    legs = [l for l in _legs() if l.kind == "ml"]
    for l in legs:
        l.p = min(0.95, l.p + 0.03)  # our probability above the -300 price (75%)
    res = P.build_parlays(legs, kmin=4, kmax=5, top=3, rank="value")
    assert res[0].ev is not None and res[0].ev > 0 and res[0].market_decimal > 1


def test_explanations_show_formula_and_sources():
    res = P.build_parlays(_legs(), kmin=4, kmax=4, top=1)[0]
    ex = P.explain_parlay(res)
    assert "=" in ex["formula"] and ex["sources"] and any("independent" in a for a in ex["assumptions"])
    leg = P.explain_leg(res.legs[0])
    assert leg["sources"] and leg["probability"] == res.legs[0].p

import math

import parlay_pricing as PP
import parlays as P


def _leg(pick, p, quotes, kind="ml", meta=None, game="1"):
    return P.Leg(f"k{pick}", game, "basketball/nba", "NBA", "A @ B", "2026-11-09T00:00Z", "pre", kind, pick, p, quotes=quotes,
                 meta=meta or {"kind": kind, "side": "home"})


def _q(book, price, opp, via="Unabated", kind="sportsbook", line=None, exact=True):
    return PP.quote(book, kind, price, opp, line, via, exact=exact)


def test_price_maths_round_trips_and_removes_margin():
    assert abs(PP.to_decimal(-110) - 1.9091) < 1e-3 and abs(PP.to_decimal(150) - 2.5) < 1e-9
    assert PP.to_american(2.5) == 150 and PP.to_american(1.5) == -200 and PP.to_american(1.0) is None
    assert abs(PP.devig(-110, -110) - 0.5) < 1e-9
    assert 0.62 < PP.devig(-200, 170) < 0.65
    assert PP.payout(2.5, 10) == (25.0, 15.0)


def test_parlay_price_is_the_product_and_vig_compounds():
    legs = [_leg(f"L{i}", 0.5, [_q("DraftKings", -110, -110)], game=str(i)) for i in range(3)]
    r = PP.price_report(legs, p_ours=0.125)
    dk = r["best_book"]
    assert dk["book"] == "DraftKings" and abs(dk["decimal"] - 1.9091 ** 3) < 1e-3  # +596
    assert dk["american"] == 596
    assert abs(r["p_market"] - 0.125) < 1e-9 and abs(r["fair_decimal_market"] - 8.0) < 1e-6
    assert 0.12 < r["house_edge"] < 0.14  # three -110 legs: the book keeps about 13% on this ticket
    assert abs(r["vig_per_leg"] - 0.0454545) < 1e-4  # a -110/-110 leg keeps 4.55% of each dollar
    assert r["ev_ours"] < 0 and r["stakes"]["ten"][0] > 69


def test_single_book_must_quote_every_leg_and_shopping_is_a_ceiling():
    a = _leg("A", 0.6, [_q("DraftKings", -150, 130), _q("FanDuel", -140, 120)], game="1")
    b = _leg("B", 0.6, [_q("DraftKings", -150, 130), _q("FanDuel", -160, 140), _q("BetMGM", -130, 110)], game="2")
    r = PP.price_report([a, b])
    assert {x["book"] for x in r["books"]} == {"DraftKings", "FanDuel"}  # BetMGM does not quote leg A
    assert r["books"][0]["book"] == "FanDuel"  # -140 x -160 beats DraftKings -150 x -150
    assert abs(r["books"][0]["decimal"] - PP.to_decimal(-140) * PP.to_decimal(-160)) < 1e-9
    assert r["shopped"]["decimal"] > r["books"][0]["decimal"]  # best of each leg across books beats any single book
    assert abs(r["shopped"]["decimal"] - PP.to_decimal(-140) * PP.to_decimal(-130)) < 1e-9


def test_exchanges_and_different_lines_never_enter_the_parlay_price():
    ml = _leg("A", 0.6, [_q("Kalshi", -120, None, kind="exchange"), _q("DraftKings", -150, 130)], game="1")
    sp = _leg("B", 0.55, [_q("DraftKings", -110, -110, line=-3.5), _q("FanDuel", +100, -120, line=-3.0, exact=False)], kind="spread",
              meta={"kind": "spread", "side": "home", "line": -3.5}, game="2")
    r = PP.price_report([ml, sp])
    assert [b["book"] for b in r["books"]] == ["DraftKings"]
    assert r["legs"][1]["different_line"] and r["legs"][1]["different_line"][0]["source"] == "FanDuel"
    assert r["legs"][0]["exchanges"][0]["source"] == "Kalshi"
    assert all(q["source"] != "FanDuel" for q in r["legs"][1]["books"].values())


def test_unpriced_legs_are_estimated_and_labelled():
    priced = _leg("A", 0.7, [_q("DraftKings", -200, 170)], game="1")
    player = _leg("Player 20+ pts", 0.8, [], kind="player", meta={"kind": "player"}, game="2")
    r = PP.price_report([priced, player], p_ours=0.56)
    assert not r["all_priced"] and r["best_book"] is None and r["n_priced"] == 1
    est = r["estimate"]
    assert est["unpriced"] == ["Player 20+ pts"]
    assert abs(est["decimal"] - PP.to_decimal(-200) * (PP.STD_BOOK_FACTOR / 0.8)) < 1e-9
    assert r["stakes"]["estimated"] is True


def test_espn_quotes_map_sides_lines_and_prices():
    g = {"book": "DraftKings", "home_ml": -185, "away_ml": 155, "spread": -4.5, "home_spread_price": -110, "away_spread_price": -110,
         "total": 222.5, "over_price": -106, "under_price": -114}
    assert PP.espn_quotes(g, "ml", "away")[0]["price"] == 155 and PP.espn_quotes(g, "ml", "away")[0]["opp"] == -185
    away = PP.espn_quotes(g, "spread", "away")[0]
    assert away["line"] == 4.5 and PP.espn_quotes(g, "spread", "home")[0]["line"] == -4.5
    under = PP.espn_quotes(g, "total", "under")[0]
    assert under["price"] == -114 and under["opp"] == -106 and under["line"] == 222.5
    assert PP.espn_quotes({"book": "x"}, "total", "over") == []


def test_kalshi_quote_includes_the_fee():
    q = PP.kalshi_quote({"kalshi_home": 0.70}, "home")[0]
    cost = 0.70 + 0.07 * 0.70 * 0.30
    assert q["kind"] == "exchange" and abs(q["decimal"] - 1 / cost) < 0.01
    assert PP.kalshi_quote({"kalshi_home": None}, "home") == []


def _lines(price, points=None, **kw):
    d = {"price": price, "disabled": False, "statusId": 1}
    if points is not None:
        d["points"] = points
    d.update(kw)
    return d


def test_unabated_board_parsing_side_mapping_and_junk_filtering():
    data = {"lastUpdated": 1794100000000, "odds": {"nba": {"periodTypes": {"game": {"pregame": {
        "ml": {"eventId": 7, "eventName": "Spurs San Antonio SAS @ Knicks New York NYK", "eventStart": "2026-11-09T00:30:00Z", "betTypeId": 1,
               "sides": {"a": {"sideIndex": 0, "marketSourceLines": {"1": _lines(150, deepLink="https://g/1"), "86": _lines(10000)}},
                         "b": {"sideIndex": 1, "marketSourceLines": {"1": _lines(-180, deepLink="https://g/2"), "86": _lines(-10000)}}}},
        "tot": {"eventId": 7, "eventName": "Spurs San Antonio SAS @ Knicks New York NYK", "eventStart": "2026-11-09T00:30:00Z", "betTypeId": 3,
                "sides": {"a": {"sideIndex": 0, "marketSourceLines": {"1": _lines(-106, 222.5), "2": _lines(-110, 221.5)}},
                          "b": {"sideIndex": 1, "marketSourceLines": {"1": _lines(-114, 222.5), "2": _lines(-110, 221.5)}}}}}}}}}}
    b = PP.parse_board(data)
    ev = b["events"][0]
    assert ev["ml"][1] == {"away": 150, "home": -180, "link_away": "https://g/1", "link_home": "https://g/2"}
    assert 86 not in ev["ml"]  # placeholder prices (10000) are dropped
    assert ev["total"][1]["over"] == -106 and ev["total"][1]["under"] == -114  # side 0 is over, side 1 is under
    g = {"home": "New York Knicks", "away": "San Antonio Spurs", "start": "2026-11-09T00:30:00Z"}
    assert PP.find_event(b, g) is ev
    assert PP.find_event(b, dict(g, home="Boston Celtics")) is None
    assert PP.find_event(b, dict(g, start="2026-11-12T00:30:00Z")) is None

    meta = {"kind": "total", "side": "over", "line": 222.5}
    qs = PP.unabated_quotes(meta, ev, b["updated"])
    exact = {q["source"]: q for q in qs if q["exact"]}
    assert exact["DraftKings"]["price"] == -106 and exact["DraftKings"]["opp"] == -114
    assert any(q["source"] == "FanDuel" and not q["exact"] for q in qs)  # 221.5 is a different bet
    assert all(q["via"] == "Unabated" and q["ts"] for q in qs)

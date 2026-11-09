import pandas as pd

import parlay_pricing as PP
import parlay_venues as V
import parlays as P

NOW = pd.Timestamp("2026-11-09T12:00:00Z")
FRESH = "2026-11-09T11:58:00+00:00"
START = "2026-11-09T23:00:00Z"


def q(book, price, opp, kind="sportsbook", line=None, exact=True, ts=FRESH, via="Unabated"):
    return PP.quote(book, kind, price, opp, line, via, link=f"https://x/{book}", exact=exact, ts=ts)


def leg(pick, quotes, game="1", kind="ml", start=START, info=None, meta=None):
    return P.Leg(f"k{pick}", game, "basketball/nba", "NBA", "A @ B", start, "pre", kind, pick, 0.6, quotes=quotes,
                 meta=meta or {"kind": kind, "side": "home"}, info=info or {"live_state": "pre"})


def two(extra_a=(), extra_b=()):
    a = leg("A", [q("DraftKings", -150, 130), q("FanDuel", -140, 120)] + list(extra_a), game="1")
    b = leg("B", [q("DraftKings", -150, 130), q("FanDuel", -160, 140)] + list(extra_b), game="2")
    return [a, b]


def by(res, name):
    return next(v for v in res["venues"] if v["name"] == name)


def test_best_book_is_the_highest_paying_book_that_passes_every_check():
    r = V.evaluate(two(), NOW)
    assert r["best"]["name"] == "FanDuel" and r["best"]["status"] == "ok"  # -140 x -160 beats -150 x -150
    assert by(r, "DraftKings")["status"] == "ok" and r["verdict"] == "ok"


def test_book_missing_a_leg_or_on_a_different_line_is_not_placeable():
    a = leg("A", [q("DraftKings", -110, -110, line=-3.5), q("FanDuel", 100, -120, line=-3.0, exact=False)], kind="spread",
            meta={"kind": "spread", "side": "home", "line": -3.5})
    b = leg("B", [q("DraftKings", -150, 130)], game="2")
    r = V.evaluate([a, b], NOW)
    assert r["best"]["name"] == "DraftKings"
    fd = by(r, "FanDuel")
    assert fd["status"] == "no" and fd["decimal"] is None and any("different line" in t or "different" in t for _, t in fd["reasons"])


def test_stale_corrupt_and_placeholder_prices_are_rejected():
    old = "2026-11-09T10:00:00+00:00"
    assert any(s == "fail" for s, _ in V.check_quote(q("X", -150, 130, ts=old), NOW))
    assert any(s == "warn" for s, _ in V.check_quote(q("X", -150, 130, ts="2026-11-09T11:45:00+00:00"), NOW))
    assert any(s == "fail" for s, _ in V.check_quote(q("X", -150, -150), NOW))  # both sides favourites: 120%+ overround
    assert any(s == "fail" for s, _ in V.check_quote(q("X", 10000, -10000), NOW))
    real = V.check_quote(q("X", -10000, 3000), NOW)  # a genuine mismatch line is not a placeholder, but is flagged
    assert [s for s, _ in real] == ["warn"] and "extreme favourite" in real[0][1]
    assert V.check_quote(q("X", -110, -110), NOW) == []


def test_stale_quote_removes_a_book_from_the_ranking():
    a = leg("A", [q("DraftKings", -150, 130, ts="2026-11-09T09:00:00+00:00"), q("FanDuel", -140, 120)])
    r = V.evaluate([a], NOW)
    assert by(r, "DraftKings")["status"] == "no" and r["best"]["name"] == "FanDuel"


def test_started_game_closes_betting_everywhere():
    a = leg("A", [q("DraftKings", -150, 130)], info={"live_state": "in"})
    r = V.evaluate([a], NOW)
    assert r["best"] is None and r["verdict"] == "no" and r["closed"] == ["A"]
    soon = leg("A", [q("DraftKings", -150, 130)], start="2026-11-09T12:01:00Z")
    assert V.evaluate([soon], NOW)["best"] is None
    gone = leg("A", [q("DraftKings", -150, 130)], info={"gone": True})
    assert V.evaluate([gone], NOW)["best"] is None


def test_same_game_legs_and_player_legs_downgrade_to_verify_at_the_book():
    a = leg("A", [q("DraftKings", -150, 130)], game="1")
    b = leg("B", [q("DraftKings", -110, -110)], game="1", kind="total", meta={"kind": "total", "side": "over", "line": 220})
    r = V.evaluate([a, b], NOW)
    assert r["best"]["status"] == "caution" and any("same game" in t for _, t in r["general"])
    p = leg("Player 20+ pts", [], game="3", kind="player", meta={"kind": "player"})
    r2 = V.evaluate([leg("A", [q("DraftKings", -150, 130)], game="1"), p], NOW)
    assert r2["best"]["status"] == "caution" and r2["unpriced_legs"] == ["Player 20+ pts"] and r2["n_verified"] == 1
    assert abs(r2["best"]["decimal"] - PP.to_decimal(-150)) < 1e-9  # priced on the verifiable leg only


def test_exchanges_are_a_separate_bets_route_never_the_best_parlay_book():
    kal = lambda: q("Kalshi", -120, None, kind="exchange", via="Kalshi")
    a = leg("A", [q("DraftKings", -150, 130), kal()], game="1")
    b = leg("B", [q("DraftKings", -150, 130), kal()], game="2")
    r = V.evaluate([a, b], NOW)
    k = by(r, "Kalshi")
    assert k["type"] == "exchange" and k["status"] == "caution" and r["best"]["name"] == "DraftKings"
    only_k = V.evaluate([leg("A", [kal()], game="1")], NOW)
    assert only_k["best"] is None  # an exchange alone never counts as a sportsbook parlay


def test_outlier_price_against_other_books_is_flagged():
    a = leg("A", [q("DraftKings", -150, 130), q("FanDuel", -150, 130), q("BetMGM", -150, 130), q("Caesars", +150, -170)])
    r = V.evaluate([a], NOW)
    assert any("above the other books" in t for _, t in by(r, "Caesars")["reasons"])

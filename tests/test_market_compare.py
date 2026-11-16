import threading
import time

import pandas as pd
import pytest

import market_cache as MC
import parlay_compare as CMP
import parlay_pricing as PP
import parlay_venues as V
import parlays as P

NOW = pd.Timestamp("2026-11-09T12:00:00Z")
TS = "2026-11-09T11:59:00+00:00"
START = "2026-11-12T23:00:00Z"   # three days out: the old board (today + yesterday) never contained it


def leg(i, books):
    qs = [PP.quote(b, "sportsbook", -120, 100, None, "Unabated", ts=TS, link=f"https://x/{b}") for b in books]
    return P.Leg(f"k{i}", f"g{i}", "basketball/nba", "NBA", f"A{i} @ B{i}", START, "pre", "ml", f"Pick {i}", 0.7, quotes=qs,
                 meta={"kind": "ml", "side": "home"}, info={"live_state": "pre"})


def test_book_spellings_are_one_book():
    for n in ("Draft Kings", "DraftKings Sportsbook", "draftkings", "DRAFTKINGS"):
        assert PP.canon_book(n) == "DraftKings"
    assert PP.quote("Draft Kings", "espn", -110, -110, None, "ESPN")["source"] == "DraftKings"
    assert PP.canon_book("Some New Book") == "Some New Book"


def test_cache_is_single_flight_and_shared():
    MC.clear()
    calls = []

    def slow():
        calls.append(1)
        time.sleep(0.2)
        return {"v": 1}
    out = []
    ts = [threading.Thread(target=lambda: out.append(MC.get("k", 60, slow)[0])) for _ in range(8)]
    [t.start() for t in ts]
    [t.join() for t in ts]
    assert len(calls) == 1 and len(out) == 8


def test_cache_serves_stale_when_the_feed_fails_but_not_when_there_is_nothing():
    MC.clear()
    MC.get("a", 0, lambda: 5)
    time.sleep(0.01)

    def boom():
        raise RuntimeError("feed down")
    val, st_ = MC.get("a", 0, boom)
    assert val == 5 and st_["stale"] is True
    with pytest.raises(RuntimeError):
        MC.get("never-loaded", 10, boom)


def test_matrix_shows_every_book_and_who_can_take_the_whole_parlay():
    legs = [leg(1, ["DraftKings", "FanDuel"]), leg(2, ["DraftKings"]), leg(3, ["DraftKings", "FanDuel", "BetMGM"])]
    legs[0].quotes.append(PP.quote("BetMGM", "sportsbook", -120, 100, 3.5, "Unabated", ts=TS, exact=False))
    m = CMP.matrix(legs, V.evaluate(legs, NOW)["venues"])
    t = m["totals"]
    assert t["DraftKings"]["full"] and t["DraftKings"]["covered"] == 3 and t["DraftKings"]["american"]
    assert not t["FanDuel"]["full"] and t["FanDuel"]["covered"] == 2 and t["FanDuel"]["missing"] == ["Pick 2"]
    assert not t["BetMGM"]["full"] and "Pick 1" in t["BetMGM"]["missing"]      # other line does not count
    assert m["rows"][0]["cells"]["BetMGM"]["exact"] is False                   # but it is still shown
    assert m["books"][0] == "DraftKings"                                        # most coverage first


def test_a_game_days_away_is_priced_not_called_gone(monkeypatch):
    # the board for that day loads and has the game: quotes are live, the game is on the board
    row = {"id": "g1", "ep": "basketball/nba", "state": "pre", "detail": "", "book": "Draft Kings", "home_ml": -150.0, "away_ml": 130.0,
           "dk_home_ml": "0ML1_1", "home_logo": "h.png", "away_logo": "a.png"}
    seen = {}

    def fake_games_for(wanted):
        seen["w"] = wanted
        return {"g1": row}, {"stale": False, "failed": []}
    import live
    monkeypatch.setattr(live, "games_for", fake_games_for)
    monkeypatch.setattr(V, "_kalshi_by_ep", lambda *a, **k: None)
    monkeypatch.setattr(PP, "attach_unabated", lambda *a, **k: {})
    l = leg(1, [])
    l.game_id = "g1"
    V.refresh_legs([l], NOW)
    assert seen["w"] == [("basketball/nba", START)]                # asked for the game's own day
    assert l.info["gone"] is False and l.info["home_logo"] == "h.png"
    assert [q["source"] for q in l.quotes] == ["DraftKings"]       # "Draft Kings" folded into DraftKings


def test_failed_board_keeps_saved_prices_instead_of_saying_the_game_is_gone(monkeypatch):
    import live
    monkeypatch.setattr(live, "games_for", lambda w: ({}, {"stale": False, "failed": ["basketball/nba 20261112"]}))
    monkeypatch.setattr(V, "_kalshi_by_ep", lambda *a, **k: None)
    monkeypatch.setattr(PP, "attach_unabated", lambda *a, **k: {})
    l = leg(1, ["DraftKings"])
    V.refresh_legs([l], NOW)
    assert l.info["gone"] is False and l.info["board_unavailable"] is True
    assert l.quotes and "saved price" in l.quotes[0]["note"]


def test_check_cache_is_keyed_by_the_legs_not_the_record():
    a, b = [leg(1, ["DraftKings"])], [leg(1, ["FanDuel"])]
    assert V.signature(a) == V.signature(b)
    assert V.signature(a) != V.signature([leg(2, ["DraftKings"])])


def test_failing_league_is_backed_off_not_retried_by_every_visitor(monkeypatch):
    import unabated
    MC.clear()
    calls = []
    monkeypatch.setattr(unabated, "api_key", lambda: "k")
    monkeypatch.setattr(unabated, "_get", lambda *a, **k: calls.append(1) or (_ for _ in ()).throw(RuntimeError("Unexpected error")))
    assert PP.fetch_board("cfb") is None and PP.fetch_board("cfb") is None and PP.fetch_board("cfb") is None
    assert len(calls) == 1


def test_warmer_runs_once_and_snapshot_round_trips(tmp_path, monkeypatch):
    MC.clear()
    monkeypatch.setattr(MC, "SNAP", str(tmp_path / "s.json"))
    MC.get("persist:x", 60, lambda: {"a": 1}, persist=True)
    MC.clear()
    assert MC.load_snapshot() == 1 and MC.peek("persist:x")[1] == {"a": 1}
    ran = []
    monkeypatch.setitem(MC._WARMER, "thread", None)
    assert MC.start_warmer(lambda: [lambda: ran.append(1)], 3600) is True
    time.sleep(0.2)
    assert ran and MC.start_warmer(lambda: [], 3600) is False

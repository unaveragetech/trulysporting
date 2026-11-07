import pandas as pd

import parlay_track as T
import parlays as P

NOW = pd.Timestamp("2026-11-07T20:00:00Z")


def _leg(kind, **meta):
    base = {"kind": kind, "home": "Home", "away": "Away", "home_abbr": "HOM", "away_abbr": "AWY"}
    base.update(meta)
    return {"key": f"k{kind}{meta}", "game_id": "1", "ep": "basketball/nba", "league": "NBA", "matchup": "AWY @ HOM",
            "start": "2026-11-07T23:00:00Z", "kind": kind, "pick": kind, "p": 0.7, "price": None, "meta": base, "sources": [], "notes": []}


def _game(state="post", hs=100, as_=90, name="STATUS_FINAL", players=None, **kw):
    g = {"state": state, "name": name, "home_score": hs, "away_score": as_, "period": 4, "clock": "0:00", "start": "2026-11-07T23:00Z",
         "players": players or {}}
    g.update(kw)
    return g


def test_moneyline_spread_and_total_grading():
    assert T.grade_leg(_leg("ml", side="home"), _game(hs=100, as_=90))["status"] == "won"
    assert T.grade_leg(_leg("ml", side="away"), _game(hs=100, as_=90))["status"] == "lost"
    assert T.grade_leg(_leg("spread", side="home", line=-9.5), _game(hs=100, as_=90))["status"] == "won"
    assert T.grade_leg(_leg("spread", side="home", line=-10.0), _game(hs=100, as_=90))["status"] == "push"
    assert T.grade_leg(_leg("spread", side="away", line=10.5), _game(hs=100, as_=90))["status"] == "won"
    assert T.grade_leg(_leg("total", side="over", line=189.5), _game(hs=100, as_=90))["status"] == "won"
    assert T.grade_leg(_leg("total", side="under", line=189.5), _game(hs=100, as_=90))["status"] == "lost"


def test_player_leg_grading_and_did_not_play_is_void():
    leg = _leg("player", player="Nikola Jokić", cat="stats", stat="AST", thr=7.0)
    box = {T._norm("Nikola Jokic"): {"stats": {"AST": 9.0}}}
    assert T.grade_leg(leg, _game(players=box))["status"] == "won"  # accents and case do not matter
    assert T.grade_leg(leg, _game(players={T._norm("Nikola Jokic"): {"stats": {"AST": 5.0}}}))["status"] == "lost"
    assert T.grade_leg(leg, _game(players={}))["status"] == "void"  # did not play
    assert T.grade_leg(leg, _game(state="in", players={}))["status"] == "live"


def test_live_games_report_progress_and_flags():
    over = _leg("total", side="over", line=150.5)
    g = _game(state="in", name="STATUS_IN_PROGRESS", hs=80, as_=75)
    r = T.grade_leg(over, g)
    assert r["status"] == "live" and r["flag"] == "secured"  # already over: cannot lose
    under = _leg("total", side="under", line=150.5)
    assert T.grade_leg(under, g)["flag"] == "dead"
    assert T.grade_leg(_leg("ml", side="home"), _game(state="pre", hs=0, as_=0))["status"] == "pending"
    assert T.grade_leg(_leg("ml", side="home"), _game(state="post", name="STATUS_POSTPONED"))["status"] == "void"


def test_parlay_is_lost_the_moment_a_leg_loses_and_won_only_when_all_games_end():
    rec = {"legs": [dict(_leg("ml", side="home"), game_id="1"), dict(_leg("ml", side="home"), game_id="2")]}
    games = {("basketball/nba", "1"): _game(hs=90, as_=100), ("basketball/nba", "2"): _game(state="in", name="STATUS_IN_PROGRESS")}
    g = T.grade_parlay(rec, games)
    assert g["status"] == "lost" and not g["all_over"] and not g["settled"]  # lost early, other game still on
    games[("basketball/nba", "2")] = _game(hs=100, as_=90)
    g = T.grade_parlay(rec, games)
    assert g["status"] == "lost" and g["all_over"] and g["settled"]
    both_won = {("basketball/nba", "1"): _game(hs=100, as_=90), ("basketball/nba", "2"): _game(state="in", name="STATUS_IN_PROGRESS")}
    g = T.grade_parlay(rec, both_won)
    assert g["status"] == "live" and not g["settled"]  # not won until every game is over
    both_won[("basketball/nba", "2")] = _game(hs=101, as_=90)
    assert T.grade_parlay(rec, both_won)["status"] == "won"


def test_void_legs_drop_out_and_busted_is_flagged():
    rec = {"legs": [dict(_leg("ml", side="home"), game_id="1"), dict(_leg("player", player="X Y", cat="stats", stat="PTS", thr=10.0), game_id="2")]}
    games = {("basketball/nba", "1"): _game(hs=100, as_=90), ("basketball/nba", "2"): _game(players={})}
    g = T.grade_parlay(rec, games)
    assert g["status"] == "won" and g["legs"][1]["status"] == "void"
    rec2 = {"legs": [dict(_leg("total", side="under", line=150.5), game_id="1")]}
    live = {("basketball/nba", "1"): _game(state="in", name="STATUS_IN_PROGRESS", hs=80, as_=75)}
    assert T.grade_parlay(rec2, live)["status"] == "busted"


def test_resolution_times_use_start_plus_typical_length_and_clock_when_live():
    pre = {"state": "pre", "start": "2026-11-08T00:00:00Z"}
    e = T.est_end("basketball/nba", "", pre, NOW)
    assert e == pd.Timestamp("2026-11-08T02:30:00Z")
    assert T.est_end("basketball/nba", "", {"state": "post"}, NOW) is None
    live = {"state": "in", "period": 4, "clock": "6:00", "name": "STATUS_IN_PROGRESS"}
    e2 = T.est_end("basketball/nba", "", live, NOW)
    assert NOW < e2 < NOW + pd.Timedelta(hours=1)  # a quarter is left, not a whole game
    rec = {"legs": [dict(_leg("ml", side="home"), game_id="1", start="2026-11-08T00:00:00Z"),
                    dict(_leg("ml", side="home"), game_id="2", start="2026-11-08T03:00:00Z", matchup="C @ D")]}
    plan = T.resolution_plan(rec, {("basketball/nba", "1"): pre, ("basketball/nba", "2"): {"state": "pre", "start": "2026-11-08T03:00:00Z"}}, NOW)
    assert plan["resolves_at"] == pd.Timestamp("2026-11-08T05:30:00Z") and plan["first_end"] == e
    assert "in 6h 30m" in T.fmt_when(plan["resolves_at"], "UTC", NOW) or "in 9h" in T.fmt_when(plan["resolves_at"], "UTC", NOW)
    assert T.fmt_when(None, "UTC") == "final"


def test_unstarted_and_unbettable_legs_are_dropped_and_idle_leagues_excluded():
    def mk(start, state="pre", bettable=True, live=False):
        return P.Leg("k" + start + state, "1", "basketball/nba", "NBA", "A @ B", start, state, "ml", "x", 0.7, bettable=bettable, live=live)
    future = (pd.Timestamp.now(tz="UTC") + pd.Timedelta(hours=3)).isoformat()
    past = (pd.Timestamp.now(tz="UTC") - pd.Timedelta(hours=1)).isoformat()
    soon = (pd.Timestamp.now(tz="UTC") + pd.Timedelta(minutes=1)).isoformat()
    kept = P.drop_unbettable([mk(future), mk(past), mk(soon), mk(future, state="in"), mk(future, bettable=False), mk(future, live=True)])
    assert [l.start for l in kept] == [future]
    board = pd.DataFrame({"ep": ["basketball/nba", "basketball/wnba", "football/nfl"], "state": ["pre", "post", "pre"],
                          "start": [future, past, (pd.Timestamp.now(tz="UTC") + pd.Timedelta(days=5)).isoformat()]})
    assert P.eligible_leagues(board, 24, P.MODEL_LEAGUES) == {"basketball/nba": 1}  # WNBA idle, NFL game is days away


def test_leg_roundtrip_and_track_record():
    leg = P.Leg("k", "1", "basketball/nba", "NBA", "A @ B", "2026-11-08T00:00Z", "pre", "ml", "Home to win", 0.7, -200,
                [P.Source("Kalshi", "market", 0.68, "x")], ["n"], meta={"kind": "ml", "side": "home"}, edge=0.02)
    back = P.leg_from_dict(P.leg_to_dict(leg))
    assert back.p == 0.7 and back.meta["side"] == "home" and back.sources[0].name == "Kalshi" and back.edge == 0.02
    recs = [{"p_saved": 0.4, "legs": [{"p": 0.8}, {"p": 0.55}], "result": {"settled": True, "status": "lost",
            "legs": [{"status": "won"}, {"status": "lost"}]}}, {"p_saved": 0.5, "legs": [{"p": 0.7}], "result": None}]
    tr = T.track_record(recs)
    assert tr["parlays"] == 1 and tr["parlays_won"] == 0 and tr["legs"] == 2 and tr["legs_won"] == 1
    assert {b["range"] for b in tr["buckets"]} == {"50%-60%", "80%-90%"}


def test_parse_game_reads_scores_state_and_player_stats():
    s = {"header": {"competitions": [{"date": "2026-11-07T23:00Z", "status": {"period": 4, "displayClock": "0.0",
         "type": {"state": "post", "name": "STATUS_FINAL", "shortDetail": "Final"}},
         "competitors": [{"homeAway": "home", "score": "101"}, {"homeAway": "away", "score": "99"}]}]},
         "boxscore": {"players": [{"statistics": [{"name": "", "labels": ["MIN", "PTS", "3PT"],
                                    "athletes": [{"athlete": {"displayName": "Test Player Jr."}, "stats": ["30", "22", "4-9"]}]}]}]}}
    g = T.parse_game(s)
    assert g["state"] == "post" and g["home_score"] == 101 and g["away_score"] == 99
    assert g["players"][T._norm("Test Player")]["stats"] == {"MIN": 30.0, "PTS": 22.0, "3PT": 4.0}  # "4-9" -> 4 made

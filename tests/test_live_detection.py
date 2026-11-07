import pandas as pd

import parlays as P
import sporting_shared as ss
from live import event_row


def test_status_names_between_periods_and_overtime_count_as_live():
    for name in ["STATUS_IN_PROGRESS", "STATUS_END_PERIOD", "STATUS_HALFTIME", "STATUS_FIRST_HALF", "STATUS_SECOND_HALF",
                 "STATUS_OVERTIME", "STATUS_SHOOTOUT", "STATUS_RAIN_DELAY", "STATUS_DELAYED", "STATUS_END_OF_REGULATION"]:
        assert ss.status_is_live(name), name
    for name in ["STATUS_FINAL", "STATUS_FINAL_OT", "STATUS_FINAL_PENALTIES", "STATUS_SCHEDULED", "STATUS_POSTPONED",
                 "STATUS_CANCELED", "STATUS_FULL_TIME", ""]:
        assert not ss.status_is_live(name), name


def test_pandas_filter_matches_the_helper():
    s = pd.Series(["STATUS_END_PERIOD", "STATUS_FINAL_PENALTIES", "STATUS_SCHEDULED", "STATUS_IN_PROGRESS"])
    assert list(s.str.contains(ss.LIVE_STATUS_RE, case=False)) == [True, False, False, True]


def test_college_leagues_ask_for_groups_and_every_league_asks_for_today():
    today, yday = ss.et_dates()
    cfb = ss.board_requests("football/college-football")
    assert {r.get("groups") for r in cfb} == {"80", "81"} and all(r["limit"] == 300 for r in cfb)
    assert all("dates" in r for r in cfb)  # never the bare default scoreboard, which hides most college games
    nba = ss.board_requests("basketball/nba")
    assert {"limit": 300} in nba or any("dates" not in r for r in nba)  # ESPN's own current day is also asked for
    assert any(r.get("dates") == today for r in nba) and any(r.get("dates") == yday for r in nba)  # pro leagues: yesterday too


def test_event_row_parses_state_clock_and_embedded_odds():
    ev = {"id": "401", "date": "2026-11-07T01:00Z", "competitions": [{
        "status": {"period": 3, "displayClock": "4:12", "type": {"state": "in", "name": "STATUS_END_PERIOD", "shortDetail": "End 3rd"}},
        "competitors": [
            {"homeAway": "home", "score": "71", "team": {"id": "1", "displayName": "Home", "abbreviation": "HOM", "location": "H"}},
            {"homeAway": "away", "score": "64", "team": {"id": "2", "displayName": "Away", "abbreviation": "AWY", "location": "A"}}],
        "odds": [{"provider": {"name": "Book"}, "overUnder": 140.5, "spread": -4.5,
                  "moneyline": {"home": {"close": {"odds": "-190"}}, "away": {"close": {"odds": "+160"}}}}]}]}
    r = event_row("basketball/wnba", ev)
    assert r["state"] == "in" and r["status_name"] == "STATUS_END_PERIOD" and r["home_score"] == 71
    assert r["home_ml"] == -190 and r["away_ml"] == 160 and r["total"] == 140.5 and r["home_loc"] == "H"


def test_winner_legs_can_require_a_market_and_model_only_is_capped():
    g = {"id": "9", "ep": "basketball/nba", "league": "NBA", "home": "Home", "away": "Away", "home_abbr": "HOM", "away_abbr": "AWY",
         "start": "", "state": "pre", "home_ml": None, "away_ml": None, "book": "", "kalshi_home": None,
         "home_score": 0, "away_score": 0}
    pred = {"margin": 40.0, "p_home": 0.9999, "home_pts": 130, "away_pts": 90}
    assert P.ml_legs(g, pred, 0.3, None, None, require_market=True) == []  # no price, no leg
    loose = P.ml_legs(g, pred, 0.3, None, None, require_market=False)
    assert loose and max(l.p for l in loose) <= P.MAX_MODEL_ONLY_P


def test_player_legs_include_availability_allowance_and_skip_injured():
    import json

    class DB:
        def get_team_players_stats(self, ep, abbr):
            rows = []
            for ev in range(10):
                for name, pts in (("Star Guy", 28), ("Hurt Guy", 30)):
                    rows.append({"player_name": name, "category": "stats", "stat_labels": json.dumps(["PTS"]),
                                 "stat_values": json.dumps([str(pts + (ev % 3))]), "game_date": f"2026-10-{10 + ev}", "event_id": str(ev)})
            return pd.DataFrame(rows).itertuples() and pd.DataFrame(rows)

        def get_team_roster_players(self, ep, tid):
            return pd.DataFrame({"display_name": ["Star Guy", "Hurt Guy"], "injury_status": ["", "Out"]})

    g = {"id": "9", "ep": "basketball/nba", "away_abbr": "AWY", "home_abbr": "HOM", "league": "NBA", "start": "", "state": "pre"}
    legs = P.player_legs(DB(), g, "HOM", "1", 1.0)
    assert [l.pick.split(" 2")[0] for l in legs] == ["Star Guy"]  # the injured player is excluded
    assert legs[0].p <= P.MAX_PLAYER_P < 0.95 and "allowance" in legs[0].sources[0].detail

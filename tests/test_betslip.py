import pandas as pd

import betslip as B
import live
import parlay_pricing as PP
import parlay_venues as V
import parlays as P

NOW = pd.Timestamp("2026-11-09T12:00:00Z")
TS = "2026-11-09T11:59:00+00:00"
START = "2026-11-09T23:00:00Z"
HREF = ("https://sportsbook.draftkings.com/gateway?s=__s__&wpsrc=413&wpcn=ESPN&wpcrn=BetSlipDeepLink&preurl="
        "https%3A%2F%2Fsportsbook.draftkings.com%2Fevent%2F34973488%3Foutcomes%3D0ML87172468_1")


def dk(price, opp, sid, ts=TS):
    return PP.quote("DraftKings", "espn", price, opp, None, "ESPN", link=("https://sportsbook.draftkings.com/?outcomes=" + sid) if sid else None,
                    ts=ts, sid=sid)


def fd(price, opp, link="https://sportsbook.fanduel.com/addToBetslip?marketId=1&selectionId=2&utm_campaign=jessewinghart"):
    return PP.quote("FanDuel", "sportsbook", price, opp, None, "Unabated", link=link, ts=TS)


def leg(i, quotes, kind="ml"):
    return P.Leg(f"k{i}", f"g{i}", "basketball/nba", "NBA", f"A{i} @ B{i}", START, "pre", kind, f"Pick {i}", 0.7, quotes=quotes,
                 meta={"kind": kind, "side": "home"}, info={"live_state": "pre"})


def plan(legs, stake=10.0):
    return B.build(legs, V.evaluate(legs, NOW), stake)


def test_dk_outcome_id_is_read_from_the_embedded_betslip_link():
    assert live.dk_outcome_id(HREF) == "0ML87172468_1"
    assert live.dk_outcome_id("https://example.com/?outcomes=abc") is None
    assert live.dk_outcome_id(None) is None
    assert live.dk_outcome_id("https://sportsbook.draftkings.com/gateway?preurl=https%3A%2F%2Fsportsbook.draftkings.com%2Fe%3Foutcomes%3D%3Cscript%3E") is None


def test_espn_quote_carries_the_draftkings_id_and_a_plain_link_only_for_draftkings():
    g = {"book": "DraftKings", "home_ml": -150, "away_ml": 130, "dk_home_ml": "0ML1_1", "dk_away_ml": float("nan")}
    q = PP.espn_quotes(g, "ml", "home")[0]
    assert q["sid"] == "0ML1_1" and q["link"] == "https://sportsbook.draftkings.com/?outcomes=0ML1_1"
    assert PP.espn_quotes(g, "ml", "away")[0]["sid"] is None  # NaN column value is not an id
    other = PP.espn_quotes(dict(g, book="Caesars"), "ml", "home")[0]
    assert other["sid"] is None and other["link"] is None


def test_draftkings_gets_one_link_with_every_leg_when_all_ids_exist():
    legs = [leg(1, [dk(-150, 130, "0ML1_1")]), leg(2, [dk(-160, 140, "0ML2_3")]), leg(3, [dk(-130, 110, "0ML3_1")])]
    p = plan(legs)
    assert p["ok"] and p["best"] == "DraftKings"
    assert p["books"][0]["combined"] == "https://sportsbook.draftkings.com/?outcomes=0ML1_1+0ML2_3+0ML3_1"
    assert B.primary_action(p)["all_legs"] is True


def test_no_combined_link_if_any_leg_lacks_an_id_and_others_use_only_the_providers_own_links():
    legs = [leg(1, [dk(-150, 130, "0ML1_1"), fd(-140, 120)]), leg(2, [dk(-150, 130, None), fd(-160, 140)])]
    p = plan(legs)
    dkb = next(b for b in p["books"] if b["name"] == "DraftKings")
    assert dkb["combined"] is None
    fdb = next(b for b in p["books"] if b["name"] == "FanDuel")
    assert fdb["combined"] is None and fdb["linked"] == 2  # per-leg links, never merged into one
    assert all(r["link"].endswith("utm_campaign=jessewinghart") for r in fdb["legs"])


def test_moved_line_stale_price_or_started_game_never_produces_a_link():
    old = leg(1, [dk(-150, 130, "0ML1_1", ts="2026-11-09T08:00:00+00:00")])
    assert plan([old])["ok"] is False
    live_game = leg(2, [dk(-150, 130, "0ML2_1")])
    live_game.info["live_state"] = "in"
    assert plan([live_game])["ok"] is False
    moved = leg(3, [PP.quote("DraftKings", "espn", -110, -110, -3.5, "ESPN", link="https://x", ts=TS, sid="0HC3N350_3", exact=False)], kind="spread")
    p = plan([moved])
    assert p["ok"] is False  # a different line is not the saved bet, so its id must not be used


def test_player_legs_are_listed_to_add_by_hand_and_ticket_text_has_stake_and_payout():
    legs = [leg(1, [dk(-150, 130, "0ML1_1")]), P.Leg("kp", "g9", "basketball/nba", "NBA", "A @ B", START, "pre", "player", "Ace 20+ points", 0.8,
                                                      meta={"kind": "player"}, info={"live_state": "pre"})]
    p = plan(legs, stake=25)
    assert p["manual"] == ["Ace 20+ points"]
    t = p["books"][0]["ticket"]
    assert "Pick 1 (-150)" in t and "Ace 20+ points" in t and "Stake $25.00 -> returns $41.67" in t


def test_generator_skips_legs_priced_too_short_for_a_parlay():
    short = leg(1, [PP.quote("DraftKings", "espn", -50000, 5000, None, "ESPN", ts=TS)])
    short.p = 0.97
    ok = [leg(i, [dk(-300, 250, f"0ML{i}_1")]) for i in range(2, 6)]
    for l in ok:
        l.p = 0.8
    out = P.build_parlays([short] + ok, 2, 4, 5, 0.7)
    assert out and all("k1" not in [l.key for l in x.legs] for x in out)
    assert P.too_short(short) and not P.too_short(ok[0])


def test_build_placeable_only_returns_parlays_one_book_quotes_in_full():
    def L(i, books, p=0.8):
        qs = [PP.quote(b, "sportsbook", -200, 170, None, "Unabated", ts=TS) for b in books]
        x = leg(i, qs)
        x.p = p
        return x
    legs = [L(1, ["DraftKings", "FanDuel"]), L(2, ["DraftKings"]), L(3, ["DraftKings", "FanDuel"]), L(4, ["FanDuel"]), L(5, []),
            L(6, ["DraftKings", "FanDuel"])]
    out = P.build_placeable(legs, 3, 4, 10, 0.5)
    assert out
    for p in out:
        assert p.book in ("DraftKings", "FanDuel")
        assert all(p.book in P.book_names(l) for l in p.legs)          # every leg quoted at that one book
        assert all(l.key != "k5" for l in p.legs)                      # a leg no book quotes is never offered
    pl = P.Leg("kp", "g9", "basketball/nba", "NBA", "A @ B", START, "pre", "player", "Ace 20+ points", 0.95, meta={"kind": "player"})
    assert all(l.kind != "player" for p in P.build_placeable(legs + [pl], 3, 4, 10, 0.5) for l in p.legs)
    forced = P.build_placeable(legs, 3, 4, 10, 0.5, must_include=("k5",))
    assert forced == []                                                # a locked leg no book quotes cannot be placed


def test_parlay_keeps_reliability_and_book_in_separate_fields():
    legs = [leg(i, [dk(-200, 170, f"0ML{i}_1")]) for i in range(1, 4)]
    for l in legs:
        l.p = 0.8
    p = P._parlay(legs, "balanced")
    assert p.book is None and p.rel > 0
    out = P.build_placeable(legs, 2, 3, 5, 0.5)
    assert out and all(isinstance(x.book, str) and x.rel > 0 for x in out)

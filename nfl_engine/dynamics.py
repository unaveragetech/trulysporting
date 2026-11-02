"""Team dynamics tables built from the rich per-play data: coach decisions, play frequencies by what the team was
responding to, formations / personnel / coverage, player usage and head-to-head history.

All functions take a frame from ``tendencies.add_context`` extended with the rich columns (see ``load_context``) so
the same situation classes (``dd``, ``sc``, ``zone``, ``resp``) are used everywhere.
"""

from __future__ import annotations

import numpy as np
import pandas as pd

from nfl_engine.league import RESP_LABELS


def load_context(L, seasons, refresh: bool = False) -> pd.DataFrame:
    """Scrimmage + special-teams plays with situation classes and every rich column, for display and analysis."""
    from nfl_engine.tendencies import add_context
    from nfl_engine.tracking import load_rich

    parts = []
    for s in seasons:
        d = add_context(load_rich(s, refresh=refresh), L)
        d["season"] = s
        parts.append(d)
    return pd.concat(parts, ignore_index=True)


def _rate(num, den):
    return float(num) / den if den else np.nan


# ---------------------------------------------------------------- coach decisions


def coach_decisions(ctx: pd.DataFrame, L=None) -> pd.DataFrame:
    """One row per team: every kind of coaching decision we can see in the data, with league-relative columns."""
    rows = []
    d4 = ctx[(ctx["down"] == 4) & ctx["play_type"].isin(["pass", "run", "punt", "field_goal"]) & (ctx["qtr"] <= 4)].copy()
    d4["go"] = d4["play_type"].isin(["pass", "run"])
    d4["short"] = d4["ydstogo"] <= 3
    d4["fg_range"] = d4["yardline_100"] <= 38
    d4["trail"] = d4["score_differential"] < 0
    for team, g in ctx.groupby("posteam"):
        t4 = d4[d4["posteam"] == team]
        games = g["game_id"].nunique()
        sc = g[g["scrim"]]
        late_t = sc[(sc["qtr"] == 4) & (sc["score_differential"] <= -3)]
        late_l = sc[(sc["qtr"] == 4) & (sc["score_differential"] >= 3)]
        two = g[g["two_point_attempt"] == 1]
        td = (g["touchdown"] == 1) & g["scrim"]
        to_called = ctx[(ctx["timeout_team"] == team) & (ctx["timeout"] == 1)]
        rows.append({
            "team": team, "games": games, "4th_downs": len(t4),
            "go_rate": _rate(t4["go"].sum(), len(t4)),
            "go_short_opp_half": _rate(t4[t4["short"] & (t4["yardline_100"] <= 50)]["go"].sum(), (t4["short"] & (t4["yardline_100"] <= 50)).sum()),
            "go_own_half": _rate(t4[t4["yardline_100"] > 50]["go"].sum(), (t4["yardline_100"] > 50).sum()),
            "go_in_fg_range": _rate(t4[t4["fg_range"]]["go"].sum(), t4["fg_range"].sum()),
            "go_when_trailing": _rate(t4[t4["trail"]]["go"].sum(), t4["trail"].sum()),
            "two_pt_per_td": _rate(len(two), td.sum()),
            "timeouts_per_game": _rate(len(to_called), games),
            "q4_trailing_pass_rate": _rate(late_t["is_pass"].sum(), len(late_t)),
            "q4_leading_run_rate": _rate((1 - late_l["is_pass"]).sum(), len(late_l)),
            "early_down_pass_rate": _rate(sc[sc["down"].isin([1, 2])]["is_pass"].sum(), sc["down"].isin([1, 2]).sum()),
            "shotgun_rate": _rate(sc["shotgun"].fillna(0).sum(), len(sc)),
            "no_huddle_rate": _rate(sc["no_huddle"].fillna(0).sum(), len(sc)),
            "kneels": int(((g["qb_kneel"] == 1)).sum()),
        })
    t = pd.DataFrame(rows).set_index("team")
    lg = t.drop(columns=["games", "kneels", "4th_downs"]).mean()
    out = t.copy()
    for c in lg.index:
        out[c + "_vs_lg"] = t[c] - lg[c]
    return out


# ---------------------------------------------------------------- what they do in response to what just happened


def response_matrix(ctx: pd.DataFrame, team: str, side: str = "off") -> pd.DataFrame:
    """Share of each play type after each prior-play outcome, for the team (offense) or against it (defense)."""
    col = "posteam" if side == "off" else "defteam"
    s = ctx[ctx["scrim"] & (ctx[col] == team)].copy()
    s["kind"] = np.where(s["is_pass"] == 1, np.where(s["pass_length"].eq("deep"), "deep pass", "pass"), np.where(s["run_gap"].notna(), "run " + s["run_gap"].astype(str), "run"))
    s["kind"] = s["kind"].replace({"run end": "run outside", "run tackle": "run inside", "run guard": "run inside"})
    m = pd.crosstab(s["resp"], s["kind"], normalize="index").reindex(RESP_LABELS).fillna(0) * 100
    lg = ctx[ctx["scrim"]].copy()
    lg["kind"] = np.where(lg["is_pass"] == 1, np.where(lg["pass_length"].eq("deep"), "deep pass", "pass"), np.where(lg["run_gap"].notna(), "run " + lg["run_gap"].astype(str), "run"))
    lg["kind"] = lg["kind"].replace({"run end": "run outside", "run tackle": "run inside", "run guard": "run inside"})
    base = pd.crosstab(lg["resp"], lg["kind"], normalize="index").reindex(RESP_LABELS).fillna(0) * 100
    n = s["resp"].value_counts().reindex(RESP_LABELS).fillna(0)
    out = m.copy()
    out.insert(0, "plays", n.astype(int))
    for c in m.columns:
        out[c + " vs lg"] = m[c] - base.get(c, 0)
    return out.round(1)


def situational(ctx: pd.DataFrame, team: str, fam: str, side: str = "off") -> pd.DataFrame:
    """Pass rate by situation class: the team vs league, with sample size."""
    col = "posteam" if side == "off" else "defteam"
    s = ctx[ctx["scrim"]]
    t = s[s[col] == team].groupby(fam)["is_pass"].agg(["mean", "count"])
    lg = s.groupby(fam)["is_pass"].mean()
    out = pd.DataFrame({"plays": t["count"], "pass %": 100 * t["mean"], "league %": 100 * lg.reindex(t.index)})
    out["diff"] = out["pass %"] - out["league %"]
    return out.round(1)


# ---------------------------------------------------------------- formations / personnel / coverage


def personnel_profile(ctx: pd.DataFrame, team: str) -> pd.DataFrame:
    s = ctx[ctx["scrim"] & (ctx["posteam"] == team) & ctx.get("personnel", pd.Series(dtype=object)).notna()] if "personnel" in ctx else ctx.iloc[0:0]
    if s.empty:
        return pd.DataFrame()
    g = s.groupby("personnel").agg(snaps=("is_pass", "size"), pass_pct=("is_pass", "mean"), epa=("epa", "mean"),
                                   success=("success", "mean"))
    g["share %"] = 100 * g["snaps"] / g["snaps"].sum()
    g["pass_pct"] *= 100
    g["success"] *= 100
    return g.sort_values("snaps", ascending=False).head(8).round(2)


def defense_profile(ctx: pd.DataFrame, team: str) -> dict:
    """How a defense lines up: DB packages, coverage shells, man/zone, rushers and pressure."""
    if "def_db" not in ctx:
        return {}
    s = ctx[ctx["scrim"] & (ctx["defteam"] == team) & ctx["def_db"].notna()]
    p = s[s["is_pass"] == 1]
    out = {"packages %": (100 * s["def_db"].value_counts(normalize=True)).round(1).to_dict()}
    if "defense_coverage_type" in s:
        out["coverage % (pass plays)"] = (100 * p["defense_coverage_type"].value_counts(normalize=True).head(6)).round(1).to_dict()
        out["man / zone %"] = (100 * p["defense_man_zone_type"].value_counts(normalize=True)).round(1).to_dict()
    r = p["number_of_pass_rushers"].dropna()
    out["blitz rate (5+ rushers)"] = round(float((r >= 5).mean() * 100), 1) if len(r) else None
    out["pressure rate"] = round(float(p["was_pressure"].dropna().astype(float).mean() * 100), 1) if p["was_pressure"].notna().any() else None
    return out


# ---------------------------------------------------------------- players


def player_usage(ctx: pd.DataFrame, team: str, last_n: int = 4) -> pd.DataFrame:
    """Target / carry shares overall and in key situations, with the last ``last_n`` games vs the season."""
    s = ctx[ctx["scrim"] & (ctx["posteam"] == team)]
    order = s.groupby("game_id")["game_date"].first().sort_values().index.tolist()
    recent = set(order[-last_n:])
    rows = []
    tg = s[(s["is_pass"] == 1) & s["receiver_player_id"].notna() & (s["pass_attempt"] == 1)]
    for pid, g in tg.groupby("receiver_player_id", observed=True):
        n = len(g)
        if n < 15:
            continue
        r = g[g["game_id"].isin(recent)]
        rows.append({"player": g["receiver_player_name"].iloc[0], "role": "rec", "targets": n,
                     "target share %": 100 * n / len(tg),
                     "3rd/4th down share %": 100 * _rate(len(g[g["down"] >= 3]), len(tg[tg["down"] >= 3])),
                     "red zone share %": 100 * _rate(len(g[g["yardline_100"] <= 20]), len(tg[tg["yardline_100"] <= 20])),
                     "deep share %": 100 * _rate(len(g[g["air_yards"] >= 15]), len(tg[tg["air_yards"] >= 15])),
                     "yds/target": g["yards_gained"].mean(), "catch %": 100 * g["complete_pass"].mean(),
                     f"last {last_n} share %": 100 * _rate(len(r), len(tg[tg["game_id"].isin(recent)]))})
    rn = s[(s["is_pass"] == 0) & s["rusher_player_id"].notna() & (s["rush_attempt"] == 1) & (s["qb_scramble"] != 1)]
    for pid, g in rn.groupby("rusher_player_id", observed=True):
        n = len(g)
        if n < 15:
            continue
        r = g[g["game_id"].isin(recent)]
        rows.append({"player": g["rusher_player_name"].iloc[0], "role": "rush", "targets": n,
                     "target share %": 100 * n / len(rn),
                     "3rd/4th down share %": 100 * _rate(len(g[g["down"] >= 3]), len(rn[rn["down"] >= 3])),
                     "red zone share %": 100 * _rate(len(g[g["yardline_100"] <= 20]), len(rn[rn["yardline_100"] <= 20])),
                     "deep share %": np.nan, "yds/target": g["yards_gained"].mean(), "catch %": np.nan,
                     f"last {last_n} share %": 100 * _rate(len(r), len(rn[rn["game_id"].isin(recent)]))})
    out = pd.DataFrame(rows)
    if out.empty:
        return out
    out = out.rename(columns={"targets": "touches"})
    return out.sort_values(["role", "touches"], ascending=[False, False]).round(1)


# ---------------------------------------------------------------- head to head


def head_to_head(ctx: pd.DataFrame, games: pd.DataFrame, a: str, b: str, last: int = 6) -> pd.DataFrame:
    g = games[((games["home_team"] == a) & (games["away_team"] == b)) | ((games["home_team"] == b) & (games["away_team"] == a))]
    g = g[g["home_score"].notna()].sort_values("gameday").tail(last)
    rows = []
    for r in g.itertuples():
        a_pts, b_pts = (r.home_score, r.away_score) if r.home_team == a else (r.away_score, r.home_score)
        p = ctx[(ctx["game_id"] == r.game_id) & ctx["scrim"]]
        rows.append({"date": r.gameday.date(), "at": r.home_team, f"{a}": int(a_pts), f"{b}": int(b_pts),
                     f"{a} pass %": round(100 * p[p["posteam"] == a]["is_pass"].mean(), 1) if len(p) else np.nan,
                     f"{b} pass %": round(100 * p[p["posteam"] == b]["is_pass"].mean(), 1) if len(p) else np.nan})
    return pd.DataFrame(rows)

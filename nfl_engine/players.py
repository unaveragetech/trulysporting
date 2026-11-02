"""Player layer: who gets the ball, who covers/pressures them, and what that does to each play.

Skill is expressed *relative to the player's own team* (zero-sum within the team weights) so that picking
a different target or rusher redistributes production without double counting the team-level ratings
that already include the supporting cast.  Defender effects are approximate: public play-by-play has no
coverage assignments, so a defender's influence is inferred from sack / pass-breakup / interception share.
"""

from __future__ import annotations

import random
from collections import Counter, defaultdict
from dataclasses import dataclass, field

import numpy as np
import pandas as pd

from nfl_engine.data import CANON

ROSTER_URL = "https://github.com/nflverse/nflverse-data/releases/download/rosters/roster_{season}.parquet"
INJ_URL = "https://github.com/nflverse/nflverse-data/releases/download/injuries/injuries_{season}.parquet"
HALF_LIFE_DAYS = 75.0


@dataclass
class Rec:
    id: str
    name: str
    pos: str
    w: float  # target weight (sums to 1 over the team)
    catch_dev: float  # additive catch-rate vs team weighted mean
    ypc_dev: float  # yards per catch vs team weighted mean
    status: str = ""


@dataclass
class Rusher:
    id: str
    name: str
    pos: str
    w: float
    ypc_dev: float
    status: str = ""


@dataclass
class Defender:
    id: str
    name: str
    pos: str
    sack_w: float
    pbu_w: float
    int_w: float
    cov_dev: float  # additive change to completion probability when he is the nearest defender
    status: str = ""


@dataclass
class TeamRoster:
    team: str
    rec: list[Rec] = field(default_factory=list)
    rush: list[Rusher] = field(default_factory=list)
    defs: list[Defender] = field(default_factory=list)
    out: list[dict] = field(default_factory=list)  # players removed for injury/inactivity


@dataclass
class PlayerBook:
    teams: dict[str, TeamRoster]
    built_at: str = ""
    injury_week: int | None = None


def _load_optional(url: str) -> pd.DataFrame | None:
    try:
        return pd.read_parquet(url)
    except Exception:
        return None


def build_player_book(pbp: pd.DataFrame, season: int, week: int | None = None) -> PlayerBook:
    """Aggregate recent play-by-play to per-player share and skill, then filter by roster + injury report."""
    d = pbp[pbp["season"] >= season - 1].copy()
    d["game_date"] = pd.to_datetime(d["game_date"])
    newest = d["game_date"].max()
    d["w"] = 0.5 ** ((newest - d["game_date"]).dt.days.clip(lower=0) / HALF_LIFE_DAYS)

    roster = _load_optional(ROSTER_URL.format(season=season))
    inj = _load_optional(INJ_URL.format(season=season))
    pos_of, team_of, name_of, status_of = {}, {}, {}, {}
    if roster is not None:
        r = roster.dropna(subset=["gsis_id"])
        pos_of = dict(zip(r["gsis_id"], r["position"]))
        team_of = {k: CANON.get(v, v) for k, v in zip(r["gsis_id"], r["team"])}
        name_of = dict(zip(r["gsis_id"], r["full_name"]))
        status_of = dict(zip(r["gsis_id"], r["status"]))
    inj_status: dict[str, str] = {}
    inj_week = None
    if inj is not None and len(inj):
        inj_week = int(week or inj["week"].max())
        cur = inj[inj["week"] == min(inj_week, int(inj["week"].max()))]
        inj_status = dict(zip(cur["gsis_id"], cur["report_status"]))

    teams: dict[str, TeamRoster] = {}

    def team_for(pid, fallback):
        return team_of.get(pid, fallback)

    def available(pid):
        if status_of and status_of.get(pid, "ACT") != "ACT":
            return False, status_of.get(pid, "not on roster")
        if pid not in team_of and roster is not None:
            return False, "not on roster"
        s = inj_status.get(pid)
        if s in ("Out", "Doubtful"):
            return False, s
        return True, s or ""

    # ---- receivers
    att = d[d["pass_attempt"] == 1].dropna(subset=["receiver_player_id"])
    all_att = d[d["pass_attempt"] == 1]
    lg_catch = np.average(all_att["complete_pass"].fillna(0), weights=all_att["w"])
    lg_ypc = np.average(all_att.loc[all_att["complete_pass"] == 1, "passing_yards"].fillna(0),
                        weights=all_att.loc[all_att["complete_pass"] == 1, "w"])
    g = att.groupby("receiver_player_id")
    rec = pd.DataFrame({
        "T": g["w"].sum(),
        "C": (att["w"] * att["complete_pass"].fillna(0)).groupby(att["receiver_player_id"]).sum(),
        "Y": (att["w"] * att["passing_yards"].fillna(0) * att["complete_pass"].fillna(0)).groupby(att["receiver_player_id"]).sum(),
        "name": g["receiver_player_name"].last(), "team": g["posteam"].last(),
    })
    # ---- rushers (designed runs)
    ru = d[(d["rush_attempt"] == 1) & (d["qb_scramble"] != 1) & (d["qb_dropback"] != 1)].dropna(subset=["rusher_player_id"])
    lg_ypr = np.average(ru["rushing_yards"].fillna(0), weights=ru["w"])
    gr = ru.groupby("rusher_player_id")
    rus = pd.DataFrame({"N": gr["w"].sum(), "Y": (ru["w"] * ru["rushing_yards"].fillna(0)).groupby(ru["rusher_player_id"]).sum(),
                        "name": gr["rusher_player_name"].last(), "team": gr["posteam"].last()})
    # ---- defenders
    sk = d[d["sack"] == 1].dropna(subset=["sack_player_id"]).groupby("sack_player_id").agg(
        w=("w", "sum"), name=("sack_player_name", "last"), team=("defteam", "last"))
    pb = d[d["pass_attempt"] == 1].dropna(subset=["pass_defense_1_player_id"]).groupby("pass_defense_1_player_id").agg(
        w=("w", "sum"), name=("pass_defense_1_player_name", "last"), team=("defteam", "last"))
    it = d[d["interception"] == 1].dropna(subset=["interception_player_id"]).groupby("interception_player_id").agg(
        w=("w", "sum"), name=("interception_player_name", "last"), team=("defteam", "last"))

    def roster_of(team):
        return teams.setdefault(team, TeamRoster(team))

    # receivers: shrink, zero-sum within the team
    by_team: dict[str, list] = defaultdict(list)
    for pid, row in rec.iterrows():
        ok, st = available(pid)
        team = team_for(pid, CANON.get(row["team"], row["team"]))
        if not ok:
            if row["T"] >= 6:
                roster_of(team).out.append({"id": pid, "name": row["name"], "reason": st, "role": "receiver"})
            continue
        if row["T"] < 3:
            continue
        pos = pos_of.get(pid, "?")
        k_c, k_y = 40.0, 30.0
        catch = (row["C"] + k_c * lg_catch) / (row["T"] + k_c)
        ypc = (row["Y"] + k_y * lg_ypc) / (row["C"] + k_y)
        by_team[team].append([pid, row["name"], pos, row["T"], catch, ypc, st])
    for team, rows in by_team.items():
        tot = sum(r[3] for r in rows)
        wm_c = sum(r[3] * r[4] for r in rows) / tot
        wm_y = sum(r[3] * r[5] for r in rows) / tot
        for pid, name, pos, t, c, y, st in sorted(rows, key=lambda r: -r[3])[:12]:
            roster_of(team).rec.append(Rec(pid, name, pos, t / tot, c - wm_c, y - wm_y, st))
        rr = roster_of(team).rec
        s = sum(x.w for x in rr)
        for x in rr:
            x.w /= s

    by_team = defaultdict(list)
    for pid, row in rus.iterrows():
        ok, st = available(pid)
        team = team_for(pid, CANON.get(row["team"], row["team"]))
        if not ok:
            if row["N"] >= 15:
                roster_of(team).out.append({"id": pid, "name": row["name"], "reason": st, "role": "rusher"})
            continue
        if row["N"] < 4:
            continue
        ypc = (row["Y"] + 60.0 * lg_ypr) / (row["N"] + 60.0)
        by_team[team].append([pid, row["name"], pos_of.get(pid, "?"), row["N"], ypc, st])
    for team, rows in by_team.items():
        tot = sum(r[3] for r in rows)
        wm = sum(r[3] * r[4] for r in rows) / tot
        for pid, name, pos, n, y, st in sorted(rows, key=lambda r: -r[3])[:6]:
            roster_of(team).rush.append(Rusher(pid, name, pos, n / tot, y - wm, st))
        rr = roster_of(team).rush
        s = sum(x.w for x in rr)
        for x in rr:
            x.w /= s

    ids = set(sk.index) | set(pb.index) | set(it.index)
    rows_by_team: dict[str, list] = defaultdict(list)
    for pid in ids:
        ok, st = available(pid)
        info = sk.loc[pid] if pid in sk.index else pb.loc[pid] if pid in pb.index else it.loc[pid]
        team = team_for(pid, CANON.get(info["team"], info["team"]))
        if not ok:
            continue
        rows_by_team[team].append((pid, info["name"], pos_of.get(pid, "?"),
                                   float(sk["w"].get(pid, 0)), float(pb["w"].get(pid, 0)), float(it["w"].get(pid, 0)), st))
    for team, rows in rows_by_team.items():
        ts, tp, ti = (sum(r[i] for r in rows) or 1.0 for i in (3, 4, 5))
        n_db = max(1, sum(1 for r in rows if r[4] + r[5] > 0))
        for pid, name, pos, s_, p_, i_, st in sorted(rows, key=lambda r: -(r[3] + r[4] + 2 * r[5]))[:14]:
            share = (p_ + 3 * i_) / max(tp + 3 * ti, 1e-9)
            cov = -0.05 * float(np.clip(share * n_db - 1.0, -1.0, 2.0))  # ball-hawks cut completion probability
            roster_of(team).defs.append(Defender(pid, name, pos, s_ / ts, p_ / tp, i_ / ti, cov, st))
    return PlayerBook(teams, built_at=str(pd.Timestamp.now())[:16], injury_week=inj_week)


# ---------------------------------------------------------------- simulation hook


class PlayerHook:
    """Attaches players to the engine's anonymous plays and tallies per-player stat lines."""

    def __init__(self, rosters: tuple[TeamRoster, TeamRoster], rnd: random.Random, qb_names=("QB", "QB"),
                 scale: float = 1.0, target_override: dict | None = None, shadow: dict | None = None):
        self.R, self.rnd, self.scale = rosters, rnd, scale
        self.qb = qb_names
        self.override = target_override or {}  # side -> receiver id forced to be the target with prob `force`
        self.shadow = shadow or {}  # side(of defence) -> defender id who covers the override receiver
        self.force = 0.0
        self.lines: dict[str, Counter] = defaultdict(Counter)
        self.meta: dict[str, tuple[str, int]] = {}
        self._cw = [np.cumsum([x.w for x in r.rec]) if r.rec else None for r in rosters]
        self._rw = [np.cumsum([x.w for x in r.rush]) if r.rush else None for r in rosters]

    def _pick(self, items, cum):
        i = int(np.searchsorted(cum, self.rnd.random() * cum[-1]))
        return items[min(i, len(items) - 1)]

    def _line(self, key, name, side, role):
        self.meta[key] = (name, side, role)
        return self.lines[key]

    # -- selection
    def target(self, side: int):
        r = self.R[side]
        if not r.rec:
            return None
        ov = self.override.get(side)
        if ov:  # spotlight: he gets exactly `force` of the targets, everyone else shares the rest
            star = next((x for x in r.rec if x.id == ov), None)
            if star is not None:
                if self.rnd.random() < self.force:
                    return star
                others = [x for x in r.rec if x.id != ov]
                if others:
                    return self._pick(others, np.cumsum([x.w for x in others]))
        return self._pick(r.rec, self._cw[side])

    def cover(self, dside: int, tgt):
        r = self.R[dside]
        if not r.defs or tgt is None:
            return None
        sh = self.shadow.get(dside)
        if sh and self.override.get(1 - dside) == tgt.id and self.rnd.random() < 0.7:
            for x in r.defs:
                if x.id == sh:
                    return x
        w = np.array([x.pbu_w + x.int_w + 0.05 for x in r.defs])
        return r.defs[int(np.searchsorted(np.cumsum(w), self.rnd.random() * w.sum()))] if len(w) else None

    def rusher(self, side: int):
        r = self.R[side]
        return self._pick(r.rush, self._rw[side]) if r.rush else None

    # -- skill effects (zero-sum within the team)
    def dcomp(self, tgt, cov):
        return self.scale * ((tgt.catch_dev if tgt else 0.0) + (cov.cov_dev if cov else 0.0))

    def dyards(self, tgt):
        return self.scale * (tgt.ypc_dev if tgt else 0.0)

    def dyards_run(self, rb):
        return self.scale * (rb.ypc_dev if rb else 0.0)

    # -- bookkeeping
    def sack(self, side: int):
        d = self.R[1 - side].defs
        qb = self._line(f"qb{side}", self.qb[side], side, "QB")
        qb["sacked"] += 1
        if d:
            w = np.array([x.sack_w + 0.01 for x in d])
            x = d[int(np.searchsorted(np.cumsum(w), self.rnd.random() * w.sum()))]
            self._line(x.id, x.name, 1 - side, "DEF")["sacks"] += 1

    def interception(self, side: int, tgt, cov):
        qb = self._line(f"qb{side}", self.qb[side], side, "QB")
        qb["att"] += 1
        qb["int"] += 1
        if tgt:
            self._line(tgt.id, tgt.name, side, "REC")["targets"] += 1
        d = self.R[1 - side].defs
        if d:
            w = np.array([x.int_w + 0.01 for x in d])
            x = d[int(np.searchsorted(np.cumsum(w), self.rnd.random() * w.sum()))]
            self._line(x.id, x.name, 1 - side, "DEF")["ints"] += 1

    def play(self, side: int, kind: str, y: int, td: bool, tgt, rb, cov):
        qb = self._line(f"qb{side}", self.qb[side], side, "QB")
        if kind in ("comp", "inc"):
            qb["att"] += 1
            if tgt:
                self._line(tgt.id, tgt.name, side, "REC")["targets"] += 1
            if kind == "comp":
                qb["comp"] += 1
                qb["pass_yds"] += y
                qb["pass_td"] += td
                if tgt:
                    t = self._line(tgt.id, tgt.name, side, "REC")
                    t["rec"] += 1
                    t["rec_yds"] += y
                    t["rec_td"] += td
            elif cov is not None and self.rnd.random() < 0.3:
                self._line(cov.id, cov.name, 1 - side, "DEF")["pbu"] += 1
        elif kind == "run":
            if rb:
                t = self._line(rb.id, rb.name, side, "RB")
                t["car"] += 1
                t["rush_yds"] += y
                t["rush_td"] += td
        elif kind == "scr":
            q = self._line(f"qb{side}", self.qb[side], side, "QB")
            q["scr_yds"] += y


def project_players(L, spec, books: PlayerBook, home: str, away: str, qb_names=("QB", "QB"), n: int = 400,
                    seed: int = 0, scale: float = 1.0, override: dict | None = None, shadow: dict | None = None,
                    force: float = 0.0) -> dict:
    """Simulate a game ``n`` times with players attached; returns mean/p10/p90 stat lines per player."""
    from nfl_engine.sim import Engine

    rnd = random.Random(seed)
    eng = Engine(L, spec)
    rosters = (books.teams.get(home, TeamRoster(home)), books.teams.get(away, TeamRoster(away)))
    tallies: dict[str, list[Counter]] = defaultdict(list)
    meta: dict = {}
    pts = []
    for _ in range(n):
        hk = PlayerHook(rosters, rnd, qb_names, scale, override, shadow)
        hk.force = force
        eng.hook = hk
        r = eng.run(rnd)
        pts.append((r["home"], r["away"]))
        meta.update(hk.meta)
        for k, c in hk.lines.items():
            tallies[k].append(c)
    pos_of = {x.id: x.pos for r in rosters for x in (*r.rec, *r.rush, *r.defs)}
    out = []
    for k, cs in tallies.items():
        keys = set().union(*cs)
        stats = {}
        for key in keys:
            arr = np.array([c.get(key, 0) for c in cs] + [0] * (n - len(cs)), float)
            stats[key] = {"mean": float(arr.mean()), "p10": float(np.percentile(arr, 10)), "p90": float(np.percentile(arr, 90))}
        name, side, role = meta[k]
        out.append({"id": k, "name": name, "team": home if side == 0 else away, "role": pos_of.get(k, role), "stats": stats})
    return {"players": out, "score": {"home": float(np.mean([p[0] for p in pts])), "away": float(np.mean([p[1] for p in pts]))}}

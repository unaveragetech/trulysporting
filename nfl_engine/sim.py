"""Play-by-play Monte Carlo football engine.

Each simulated game steps through snaps: play-call -> pre-snap penalties -> outcome (sack / scramble /
completion / incomplete / interception / run / fumble) -> yardage -> down & distance -> clock burn ->
fourth-down decisions (go / punt / FG) -> scores, PAT / two-point, kickoffs, halftime, two-minute
behaviour, kneel-downs and overtime.  All base rates & distributions come from ``League`` (learned
from play-by-play); ``SideParams`` shifts them for the team, quarterback, coach, opponent, weather
and venue.
"""

from __future__ import annotations

import math
import random
from dataclasses import dataclass

from nfl_engine.league import (
    GSR_IDX, SD_IDX, YTG_MAX, League, clock_mode, pc_feats, punt_bin, ytg_bucket, zone)


@dataclass
class SideParams:
    """Additive deviations from league-average behaviour for one offence facing one defence."""
    d_sack: float = 0.0
    d_scr: float = 0.0
    d_comp: float = 0.0
    d_int: float = 0.0
    d_ypcomp: float = 0.0
    d_ypr: float = 0.0
    d_fum: float = 0.0
    pen_off: float = 0.04
    pen_def: float = 0.028  # by the defence facing this offence
    d_burn: float = 0.0
    proe: float = 0.0
    go_dev: float = 0.0
    fg_dev: float = 0.0
    qb_id: str | None = None


@dataclass
class GameSpec:
    home: str
    away: str
    sides: tuple  # (SideParams for home offence, SideParams for away offence)
    wind_ex: float = 0.0
    cold: float = 0.0
    dome: float = 0.0
    season: int = 2025
    playoff: bool = False
    home_receives: bool | None = None  # None -> coin toss


RET_TD_KICK = 0.006  # kickoff return touchdowns per kickoff
RET_TD_PUNT = 0.005
FUM_RET_TD = 0.09


def _sigmoid(x: float) -> float:
    return 1.0 / (1.0 + math.exp(-x)) if x > -30 else 0.0


class Engine:
    def __init__(self, L: League, spec: GameSpec):
        self.L, self.spec = L, spec
        self.sides = spec.sides
        self.pc_w = L.pc_model.coef_[0].tolist()
        self.pc_b = float(L.pc_model.intercept_[0])
        self.fg_w = L.fg_model.coef_[0].tolist()
        self.fg_b = float(L.fg_model.intercept_[0])
        self.grid = L.fourth_grid
        self.era = 0 if spec.season <= 2023 else 1 if spec.season == 2024 else 2
        self.kick_pool = L.kick_pool[self.era]
        self.ot_len = 900 if (spec.playoff or spec.season < 2017) else 600
        w = (spec.wind_ex, spec.cold, spec.dome)
        self.wx = w
        self.tdlog = None
        self.trace = None
        self.hook = None  # optional player-attribution hook (see players.PlayerHook)

    # ------------------------------------------------------------ small helpers
    def _fg_prob(self, dist: float, fg_dev: float) -> float:
        wx = self.wx
        x = (dist, dist * dist / 100.0, wx[0], wx[1], wx[2])
        z = self.fg_b + sum(a * b for a, b in zip(self.fg_w, x))
        return min(0.995, max(0.02, _sigmoid(z) + fg_dev))

    def _pass_prob(self, o: SideParams, down, ytg, yl, sd, qtr, hsr, gsr, mode) -> float:
        x = pc_feats(down, ytg, yl, sd, qtr, hsr, gsr, self.wx[0], self.wx[1], self.wx[2])
        z = self.pc_b
        for a, b in zip(self.pc_w, x):
            z += a * b
        p = _sigmoid(z)
        if mode == 0:
            p += o.proe
        return min(0.985, max(0.015, p))

    # ------------------------------------------------------------ one simulated game
    def run(self, rnd: random.Random) -> dict:
        L = self.L
        r = rnd.random
        self.rnd = rnd
        self.score = [0, 0]
        self.gsr = 3600.0
        self.pend = 1800.0
        self.half2 = False
        self.ot = False
        self.st = {k: [0, 0] for k in ("plays", "db", "pass_yds", "rush_yds", "to", "punts", "fga", "td", "pen")}
        first_recv = (0 if r() < 0.5 else 1) if self.spec.home_receives is None else (0 if self.spec.home_receives else 1)
        self.second_recv = 1 - first_recv
        poss, yl = first_recv, self._kickoff_yl()
        guard = 0
        while guard < 60:
            guard += 1
            ev, nyl, sc_by = self._drive(poss, yl)
            poss, yl, done = self._after_drive(ev, nyl, poss, sc_by)
            if done:
                break
        return {"home": self.score[0], "away": self.score[1], "ot": self.ot, **{k: v for k, v in self.st.items()}}

    def run_from(self, rnd: random.Random, score, gsr: float, poss: int, yl: int, down: int, ytg: int,
                 first_recv: int | None = None) -> dict | None:
        """Finish a game already in progress (regulation only).  Returns final scores or None for OT states."""
        self.rnd = rnd
        self.score = list(score)
        self.gsr = float(gsr)
        self.ot = False
        self.half2 = gsr <= 1800.0
        self.pend = 0.0 if self.half2 else 1800.0
        self.st = {k: [0, 0] for k in ("plays", "db", "pass_yds", "rush_yds", "to", "punts", "fga", "td", "pen")}
        fr = first_recv if first_recv is not None else (0 if rnd.random() < 0.5 else 1)
        self.second_recv = 1 - fr
        ev, nyl, _ = self._drive(poss, yl, down, ytg)
        poss, yl, done = self._after_drive(ev, nyl, poss, poss)
        guard = 0
        while not done and guard < 60:
            guard += 1
            ev, nyl, sc_by = self._drive(poss, yl)
            poss, yl, done = self._after_drive(ev, nyl, poss, sc_by)
        return {"home": self.score[0], "away": self.score[1], "ot": self.ot}

    def _kickoff_yl(self) -> int:
        """Receiving-team yardline_100; 0 means the return went the distance."""
        if self.rnd.random() < RET_TD_KICK:
            return 0
        p = self.kick_pool
        return p[int(self.rnd.random() * len(p))]

    # ------------------------------------------------------------ transitions between possessions
    def _after_drive(self, ev, nyl, poss, sc_by):
        """Apply drive result; returns (next_poss, next_yl, game_over)."""
        sc = self.score
        opp = 1 - poss
        rnd = self.rnd
        kicker = None  # team that kicks off next (receiver is the other)
        if ev == "TD":
            self._td_points(poss)
            kicker = poss
        elif ev == "FG":
            sc[poss] += 3
            kicker = poss
        elif ev == "DEF_TD":
            self._td_points(opp)
            kicker = opp
        elif ev == "SAFETY":
            sc[opp] += 2
            kicker = poss  # conceding team free-kicks to the scorer
        elif ev == "TIME":
            kicker = None
        if self.ot:
            return self._ot_next(ev, poss, nyl, kicker)
        # half / game boundaries
        if not self.half2 and self.gsr <= 1800.0:
            self.half2, self.pend = True, 0.0
            self.gsr = min(self.gsr, 1800.0)
            return self.second_recv, self._kickoff_yl(), False
        if self.gsr <= 0.0:
            if sc[0] == sc[1]:
                self.ot, self.gsr, self.pend = True, float(self.ot_len), 0.0
                self.ot_poss_n, self.ot_first = 0, 0 if rnd.random() < 0.5 else 1
                self.ot_sd = False
                self.ot_first_score = 0
                return self.ot_first, self._kickoff_yl(), False
            return poss, nyl or 75, True
        if kicker is not None:
            return self._kick_after_score(kicker)
        return opp, nyl, False

    def _kick_after_score(self, kicker: int):
        """(next possessor, yardline_100) after ``kicker`` kicks off, incl. late-game onside tries."""
        sc, rnd = self.score, self.rnd
        gsr = self.gsr
        if sc[kicker] < sc[1 - kicker] and self.half2 and gsr <= 360 and sc[1 - kicker] - sc[kicker] <= 16:
            if rnd.random() < (0.9 if gsr <= 150 else 0.35):
                if rnd.random() < 0.13:
                    return kicker, 52, False
                return 1 - kicker, 55, False
        return 1 - kicker, self._kickoff_yl(), False

    def _td_points(self, t: int) -> None:
        sc, rnd = self.score, self.rnd
        sc[t] += 6
        self.st["td"][t] += 1
        d = sc[t] - sc[1 - t]
        go2 = self.gsr <= 900 and self.half2 and d in (-16, -13, -10, -8, -5, -2, 1, 5)
        if not go2 and self.gsr <= 1800 and self.half2 and d in (-5, -2):
            go2 = True
        if go2:
            if rnd.random() < self.L.two_rate:
                sc[t] += 2
        elif rnd.random() < self.L.xp_rate:
            sc[t] += 1

    def _ot_next(self, ev, poss, nyl, kicker):
        sc = self.score
        self.ot_poss_n += 1
        scored = ev in ("TD", "FG", "DEF_TD", "SAFETY")
        if self.ot_sd:
            if scored:
                return poss, 0, True
        else:
            if self.ot_poss_n == 1:
                if ev == "TD" and not self.spec.playoff:
                    return poss, 0, True
                if ev == "DEF_TD":
                    return poss, 0, True
                if ev == "SAFETY":
                    return poss, 0, True
                if not scored:
                    self.ot_sd = True
                self.ot_first_score = 1 if scored else 0
            else:
                # second possession of the opening exchange
                self.ot_sd = True
                if scored and sc[poss] > sc[1 - poss]:
                    return poss, 0, True
                if sc[poss] < sc[1 - poss]:
                    return poss, 0, True
        if self.gsr <= 0.0:
            return poss, 0, True
        if kicker is not None:
            return 1 - kicker, self._kickoff_yl(), False
        return 1 - poss, nyl, False

    # ------------------------------------------------------------ a single possession
    def _drive(self, p: int, yl: int, down0: int = 1, ytg0: int | None = None):
        L, rnd, st = self.L, self.rnd, self.st
        r = rnd.random
        o = self.sides[p]
        d = self.sides[1 - p]  # unused attrs kept symmetric
        sc = self.score
        if yl <= 0:  # return touchdown
            return "TD", None, p
        down, ytg = down0, (ytg0 if ytg0 else min(10, yl))
        hk = self.hook
        while True:
            gsr = self.gsr
            if gsr <= self.pend:
                return "TIME", None, p
            sd = sc[p] - sc[1 - p]
            qtr = 5 if self.ot else (1 if gsr > 2700 else 2 if gsr > 1800 else 3 if gsr > 900 else 4)
            hsr = gsr if (self.ot or gsr <= 1800) else gsr - 1800
            mode = 0 if self.ot else clock_mode(sd, qtr, hsr)

            # ---- fourth down
            if down == 4:
                act = self._fourth(o, yl, ytg, sd, gsr)
                if act == "fg":
                    return self._field_goal(p, o, yl)
                if act == "punt":
                    return self._punt(p, yl)

            # ---- kneel when the lead is safe
            if sd > 0 and qtr == 4 and down < 4 and hsr <= 32 * (4 - down) and not self.ot:
                self._burn(mode, "run", o, kneel=True)
                st["plays"][p] += 1
                yl = min(99, yl + 1)
                ytg += 1
                down += 1
                if down > 4:
                    return "DOWNS", 100 - yl, p
                continue

            # ---- pre-snap penalties
            u = r()
            if u < o.pen_off + o.pen_def:
                st["pen"][p] += 1
                if u < o.pen_off:
                    pool = L.off_pen_pool
                    y = pool[int(r() * len(pool))]
                    y = min(y, 99 - yl) if yl + y > 99 else y
                    yl += y
                    ytg += y
                else:
                    pool = L.def_pen_pool
                    y, auto = pool[int(r() * len(pool))]
                    y = min(y, max(1, yl // 2))
                    yl -= y
                    ytg -= y
                    if yl <= 0:
                        yl = 1
                    if ytg <= 0 or (auto and r() < 0.5):
                        down, ytg = 1, min(10, yl)
                self._burn(mode, "pen", o)
                continue

            # ---- snap
            ppass = self._pass_prob(o, down, ytg, yl, sd, qtr, hsr, gsr, mode)
            z, b = zone(yl), ytg_bucket(ytg)
            rt = L.rates[(z, b)]
            st["plays"][p] += 1
            tgt = rb = cov = None
            fum_p = L.fum_rate + o.d_fum
            if r() < ppass:
                st["db"][p] += 1
                u = r()
                p_sack = max(0.0, rt["sack"] + o.d_sack)
                p_scr = max(0.0, rt["scr"] + o.d_scr)
                if u < p_sack:
                    pool = L.sack_pool
                    y, cat = pool[int(r() * len(pool))], "sack"
                    kind = "sack"
                    if hk:
                        hk.sack(p)
                elif u < p_sack + p_scr:
                    pool = L.scr_pool[z]
                    y, cat = pool[int(r() * len(pool))] + o.d_ypr * 0.5, "run"
                    kind = "scr"
                else:
                    u2 = r()
                    p_int = max(0.001, rt["int"] + o.d_int)
                    p_comp = min(0.95, max(0.2, rt["comp"] + o.d_comp))
                    dy = 0.0
                    if hk:
                        tgt = hk.target(p)
                        cov = hk.cover(1 - p, tgt)
                        p_comp = min(0.95, max(0.2, p_comp + hk.dcomp(tgt, cov)))
                        dy = hk.dyards(tgt)
                    if u2 < p_int:
                        if hk:
                            hk.interception(p, tgt, cov)
                        return self._interception(p, yl, mode, o)
                    if u2 < p_int + p_comp:
                        pool = L.comp_pool[(z, b)]
                        y, cat, kind = pool[int(r() * len(pool))] + o.d_ypcomp, "comp", "comp"
                        if y < 900:
                            y += dy
                    else:
                        y, cat, kind = 0, "inc", "inc"
                y = int(round(y))
            else:
                pool = L.run_pool[(z, b)]
                if hk:
                    rb = hk.rusher(p)
                y = pool[int(r() * len(pool))]
                y = int(round(y + o.d_ypr + (hk.dyards_run(rb) if hk and y < 900 else 0.0)))
                cat, kind = "run", "run"
            if y >= 900:  # sampled play was a touchdown from this field-position bin
                y = yl
            elif y >= yl:
                y = yl - 1

            self._burn(mode, cat, o)
            if self.trace is not None:
                self.trace.append((down, ytg, yl, y, kind))
            if kind in ("comp",):
                st["pass_yds"][p] += y
            elif kind in ("run", "scr"):
                st["rush_yds"][p] += y
            elif kind == "sack":
                st["pass_yds"][p] += y

            # fumble lost on live plays
            if kind != "inc" and r() < fum_p:
                st["to"][p] += 1
                if r() < FUM_RET_TD:
                    return "DEF_TD", None, p
                return "TO", 100 - max(1, min(99, yl - y)), p

            if hk:
                hk.play(p, kind, y, y >= yl, tgt, rb, cov)
            if y >= yl:
                if self.tdlog is not None:
                    self.tdlog.append((kind, yl))
                return "TD", None, p
            yl -= y
            if yl >= 100:
                return "SAFETY", 80, p
            if y >= ytg:
                down, ytg = 1, min(10, yl)
            else:
                down += 1
                ytg -= y
                if down > 4:
                    return "DOWNS", 100 - yl, p
            if self.gsr <= self.pend:
                return "TIME", None, p

    # ------------------------------------------------------------ pieces
    def _burn(self, mode: int, cat: str, o: SideParams, kneel: bool = False) -> None:
        rnd = self.rnd
        if kneel:
            self.gsr -= 40.0
            if self.gsr < self.pend:
                self.gsr = self.pend
            return
        pool = self.L.burn_pool.get((mode, cat)) or self.L.burn_pool[(0, "run")]
        b = pool[int(rnd.random() * len(pool))]
        if mode == 0:
            b = max(3.0, b + o.d_burn)
        self.gsr -= b
        if self.gsr < self.pend:
            self.gsr = self.pend

    def _fourth(self, o: SideParams, yl: int, ytg: int, sd: float, gsr: float) -> str:
        if yl > 99:
            return "punt"
        iy = min(ytg, YTG_MAX) - 1
        isd = SD_IDX[max(-30, min(30, int(sd))) + 30]
        ig = GSR_IDX[int(max(0, min(3600, gsr)) // 10)]
        pr = self.grid[iy, max(0, min(98, yl - 1)), isd, ig]
        pgo, ppunt, pfg = float(pr[0]), float(pr[1]), float(pr[2])
        if o.go_dev:
            v = max(1e-3, pgo * (1 - pgo))
            shift = max(-2.0, min(2.0, o.go_dev / v))
            lg = math.log(max(pgo, 1e-4) / max(1 - pgo, 1e-4)) + shift
            pgo = _sigmoid(lg)
        u = self.rnd.random()
        if u < pgo:
            return "go"
        rest = ppunt + pfg
        if rest <= 0:
            return "punt"
        if self.rnd.random() < pfg / rest:
            return "fg" if yl + 17 <= 64 else "punt"
        return "punt"

    def _field_goal(self, p: int, o: SideParams, yl: int):
        rnd, st = self.rnd, self.st
        st["fga"][p] += 1
        self.gsr = max(self.pend, self.gsr - (4.0 + 4.0 * rnd.random()))
        if rnd.random() < self._fg_prob(yl + 17, o.fg_dev):
            return "FG", None, p
        return "MISS", 100 - max(yl + 7, 20), p

    def _punt(self, p: int, yl: int):
        rnd, st, L = self.rnd, self.st, self.L
        st["punts"][p] += 1
        self.gsr = max(self.pend, self.gsr - (5.0 + 4.0 * rnd.random()))
        if rnd.random() < RET_TD_PUNT:
            return "PUNT", 0, p
        if rnd.random() < 0.012:  # block
            return "PUNT", max(5, 100 - yl - 3), p
        pool = L.punt_pool[punt_bin(yl)]
        net = pool[int(rnd.random() * len(pool))]
        after = yl - net
        if after <= 0:
            return "PUNT", 80, p
        return "PUNT", 100 - after, p

    def _interception(self, p: int, yl: int, mode: int, o: SideParams):
        rnd, L, st = self.rnd, self.L, self.st
        self._burn(mode, "inc", o)
        st["to"][p] += 1
        air = L.int_air[int(rnd.random() * len(L.int_air))]
        spot = yl - air
        dyl = 80 if spot <= 0 else 100 - spot
        ret = L.int_ret[int(rnd.random() * len(L.int_ret))]
        dyl -= ret
        if dyl <= 0:
            return "DEF_TD", None, p
        return "TO", dyl, p


# ---------------------------------------------------------------- driver


def simulate(L: League, spec: GameSpec, n: int = 500, seed: int = 0) -> dict:
    """Run ``n`` games; returns arrays and summary stats."""
    import numpy as np

    eng = Engine(L, spec)
    rnd = random.Random(seed)
    hs, as_, ot = [], [], 0
    box = {k: [[], []] for k in ("plays", "db", "pass_yds", "rush_yds", "to", "punts", "fga", "td", "pen")}
    for _ in range(n):
        res = eng.run(rnd)
        hs.append(res["home"])
        as_.append(res["away"])
        ot += res["ot"]
        for k in box:
            box[k][0].append(res[k][0])
            box[k][1].append(res[k][1])
    h, a = np.array(hs, float), np.array(as_, float)
    m = h - a
    return {
        "home_pts": h, "away_pts": a, "margin": m, "total": h + a,
        "p_home": float(((m > 0) + 0.5 * (m == 0)).mean()), "ot_rate": ot / n,
        "box": {k: (float(np.mean(v[0])), float(np.mean(v[1]))) for k, v in box.items()},
    }

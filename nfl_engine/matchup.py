"""Turn pre-game ratings + game context (weather, venue, rest, starters) into simulator parameters."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
import pandas as pd

from nfl_engine.league import League
from nfl_engine.ratings import Book, Snapshot
from nfl_engine.sim import GameSpec, SideParams

# per-unit home-field edge on the home offence (negated for the visitor); scaled by Tuning.hfa
HFA_VEC = {"comp": 0.006, "ypcomp": 0.15, "ypr": 0.04, "sack": -0.003, "int": -0.0006, "pen": -0.0008}
# per-unit "efficiency" lever used to align the league scoring level with reality
EFF_VEC = {"comp": 0.01, "ypcomp": 0.6, "ypr": 0.2}


# nightly live-play corrections (see livetune.py); additive, applied to every team
LIVE_ADJ: dict = {}


@dataclass
class Tuning:
    dev_scale: float = 1.0  # how much of the rated team/player/opponent deviation to trust
    qb_scale: float = 1.0
    hfa: float = 1.0
    eff: float = 0.0
    rest_pts: float = 0.0


def weather_of(row) -> tuple[float, float, float]:
    roof = str(getattr(row, "roof", "") or "")
    dome = 1.0 if roof in ("dome", "closed") else 0.0
    wind = getattr(row, "wind", np.nan)
    temp = getattr(row, "temp", np.nan)
    if dome:
        return 0.0, 0.0, 1.0
    wind_ex = 0.0 if wind != wind else float(np.clip(wind - 8, 0, 25) / 10.0)
    cold = 0.0 if temp != temp else float(np.clip(40 - temp, 0, 40) / 10.0)
    return wind_ex, cold, 0.0


def _wx_delta(L: League, stat: str, wx: tuple) -> float:
    b = L.wx[stat]
    return sum(bi * (xi - mi) for bi, xi, mi in zip(b, wx, L.wx_mean))


def side_params(L: League, base: dict, off: Snapshot, dfn: Snapshot, wx: tuple, tune: Tuning,
                sign: float) -> SideParams:
    """``sign`` = +1 home offence, -1 away offence, 0 neutral venue."""
    s = tune.dev_scale

    def dev(st: str) -> float:
        return s * (off.off[st] + tune.qb_scale * off.qb.get(st, 0.0) + dfn.deff[st])

    def adj(key: str) -> float:
        return (sign * tune.hfa * HFA_VEC.get(key, 0.0) + tune.eff * EFF_VEC.get(key, 0.0)
                + LIVE_ADJ.get(key, 0.0))

    return SideParams(
        d_sack=dev("sack") + _wx_delta(L, "sack", wx) + adj("sack"),
        d_scr=dev("scr") + LIVE_ADJ.get("scr", 0.0),
        d_comp=dev("comp") + _wx_delta(L, "comp", wx) + adj("comp"),
        d_int=dev("int") + _wx_delta(L, "int", wx) + adj("int"),
        d_ypcomp=dev("ypcomp") + _wx_delta(L, "ypcomp", wx) + adj("ypcomp"),
        d_ypr=dev("ypr") + _wx_delta(L, "ypr", wx) + adj("ypr"),
        d_fum=dev("fum"),
        pen_off=max(0.005, L.off_pen_rate + s * off.off["pen"] + adj("pen")),
        pen_def=max(0.005, L.def_pen_rate + s * dfn.deff["pen"] * 0.7),
        d_burn=s * off.off["burn"],
        proe=base["proe"] + s * off.off["proe"] + LIVE_ADJ.get("pass", 0.0),
        go_dev=s * off.coach_go,
        fg_dev=base["fgx"] + s * off.off["fgx"],
        qb_id=off.qb_id,
    )


def make_spec(row, book: Book, L: League, tune: Tuning) -> GameSpec:
    snaps = book.snaps[row.game_id]
    base = snaps["base"]
    wx = weather_of(row)
    neutral = getattr(row, "location", "Home") == "Neutral"
    h, a = snaps["home"], snaps["away"]
    sides = (
        side_params(L, base, h, a, wx, tune, 0.0 if neutral else 1.0),
        side_params(L, base, a, h, wx, tune, 0.0 if neutral else -1.0),
    )
    return GameSpec(home=row.home_team, away=row.away_team, sides=sides, wind_ex=wx[0], cold=wx[1], dome=wx[2],
                    season=int(row.season), playoff=str(getattr(row, "game_type", "REG")) != "REG")


def played(games: pd.DataFrame) -> pd.DataFrame:
    return games[games["home_score"].notna() & games["away_score"].notna()]

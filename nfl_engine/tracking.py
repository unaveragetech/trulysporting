"""Rich per-play tracking data: every snap with formation, personnel, coverage and the situation it came in response to.

Cached per season as ``rich_{season}.parquet`` (play-by-play joined to nflverse participation).  Everything that
studies *what teams do and why* (coach decisions, situational tendencies, player usage) starts from ``load_rich``.
"""

from __future__ import annotations

import io

import numpy as np
import pandas as pd

from nfl_engine.data import CANON, PBP_URL, SPORTS_DIR

PART_URL = "https://github.com/nflverse/nflverse-data/releases/download/pbp_participation/pbp_participation_{season}.parquet"

RICH_COLS = [
    "game_id", "play_id", "season", "season_type", "week", "game_date", "posteam", "defteam", "home_team", "away_team",
    "qtr", "down", "ydstogo", "yardline_100", "goal_to_go", "game_seconds_remaining", "half_seconds_remaining",
    "drive", "score_differential", "posteam_timeouts_remaining", "defteam_timeouts_remaining", "play_type",
    "yards_gained", "qb_dropback", "qb_kneel", "qb_spike", "qb_scramble", "sack", "qb_hit", "interception",
    "complete_pass", "incomplete_pass", "pass_attempt", "rush_attempt", "fumble_lost", "penalty", "penalty_team",
    "penalty_type", "touchdown", "field_goal_attempt", "field_goal_result", "punt_attempt", "kickoff_attempt",
    "extra_point_attempt", "two_point_attempt", "two_point_conv_result", "timeout", "timeout_team", "shotgun",
    "no_huddle", "pass_length", "pass_location", "run_location", "run_gap", "air_yards", "yards_after_catch",
    "epa", "wp", "success", "xpass", "pass_oe", "cpoe", "fourth_down_converted", "fourth_down_failed",
    "drive_start_yard_line", "drive_ended_with_score", "series_success", "play_clock",
    "passer_player_id", "passer_player_name", "receiver_player_id", "receiver_player_name",
    "rusher_player_id", "rusher_player_name", "wind", "temp", "roof",
]
PART_COLS = ["nflverse_game_id", "play_id", "offense_formation", "offense_personnel", "defenders_in_box",
             "defense_personnel", "number_of_pass_rushers", "was_pressure", "defense_coverage_type",
             "defense_man_zone_type", "time_to_throw", "route"]


def _download(url: str, want: list[str]) -> pd.DataFrame:
    import pyarrow.parquet as pq
    import requests

    r = requests.get(url, timeout=180)
    r.raise_for_status()
    pf = pq.ParquetFile(io.BytesIO(r.content))
    return pf.read(columns=[c for c in want if c in pf.schema_arrow.names]).to_pandas()


def _personnel(s) -> str:
    """'1 C, 1 QB, 1 RB, 4 T, 1 TE, 3 WR' -> '11' (RB count then TE count); unknown mixes -> 'other'."""
    if not isinstance(s, str):
        return ""
    n = {"RB": 0, "TE": 0, "WR": 0}
    for part in s.split(","):
        k = part.strip().split(" ")
        if len(k) == 2 and k[1] in ("RB", "FB", "HB"):
            n["RB"] += int(k[0])
        elif len(k) == 2 and k[1] in n:
            n[k[1]] += int(k[0])
    return f"{n['RB']}{n['TE']}" if n["RB"] + n["TE"] + n["WR"] >= 5 else "other"


def _def_front(s) -> str:
    """Defensive back count: 4 = base, 5 = nickel, 6 = dime, 7+ = quarter/dime-plus."""
    if not isinstance(s, str):
        return ""
    db = 0
    for part in s.split(","):
        k = part.strip().split(" ")
        if len(k) == 2 and k[1] in ("CB", "S", "FS", "SS", "DB"):
            db += int(k[0])
    return f"{min(db, 7)}DB" if db else ""


def load_rich(season: int, refresh: bool = False) -> pd.DataFrame:
    """Play-by-play + participation for one season, cached; canonical franchise ids."""
    SPORTS_DIR.mkdir(parents=True, exist_ok=True)
    path = SPORTS_DIR / f"rich_{season}.parquet"
    live = season >= pd.Timestamp.today().year - 1
    if path.exists() and not refresh and not (live and pd.Timestamp.now().timestamp() - path.stat().st_mtime > 12 * 3600):
        return pd.read_parquet(path)
    df = _download(PBP_URL.format(season=season), RICH_COLS)
    try:
        part = _download(PART_URL.format(season=season), PART_COLS)
        part = part.rename(columns={"nflverse_game_id": "game_id"})
        part["personnel"] = part["offense_personnel"].map(_personnel)
        part["def_db"] = part["defense_personnel"].map(_def_front)
        part = part.drop(columns=["offense_personnel", "defense_personnel", "route"])
        df = df.merge(part, on=["game_id", "play_id"], how="left")
    except Exception:  # noqa: BLE001  (participation is missing for some seasons / not yet published)
        pass
    for old, new in CANON.items():
        df["game_id"] = df["game_id"].str.replace(f"_{old}", f"_{new}", regex=False)
        for c in ("posteam", "defteam", "home_team", "away_team", "penalty_team", "timeout_team"):
            if c in df:
                df[c] = df[c].replace(old, new)
    for c in df.columns:  # keep the cache small
        if df[c].dtype == object and c not in ("game_id", "game_date"):
            df[c] = df[c].astype("category")
    df.to_parquet(path, index=False)
    return df

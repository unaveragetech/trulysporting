"""NFL data access: schedule/results/lines/weather (nfldata) and play-by-play (nflverse).

Everything is cached under ``data/sports`` so training and backtests are repeatable offline.
"""

from __future__ import annotations

import os

import time
from pathlib import Path

import pandas as pd


SPORTS_DIR = Path(os.environ.get("NFL_ENGINE_DIR", Path(__file__).resolve().parent.parent / "data" / "nfl_engine"))
GAMES_URL = "https://github.com/nflverse/nfldata/raw/master/data/games.csv"
PBP_URL = "https://github.com/nflverse/nflverse-data/releases/download/pbp/play_by_play_{season}.parquet"

CANON = {"OAK": "LV", "SD": "LAC", "STL": "LA"}

PBP_COLS = [
    "game_id", "season", "season_type", "week", "posteam", "defteam", "home_team", "away_team",
    "qtr", "down", "ydstogo", "yardline_100", "game_seconds_remaining", "half_seconds_remaining",
    "drive", "play_id", "play_type", "yards_gained", "qb_dropback", "qb_kneel", "qb_spike",
    "qb_scramble", "sack", "interception", "complete_pass", "incomplete_pass", "pass_attempt",
    "rush_attempt", "passing_yards", "rushing_yards", "fumble_lost", "penalty", "penalty_team",
    "penalty_yards", "first_down_penalty", "field_goal_attempt", "field_goal_result",
    "kick_distance", "kickoff_attempt", "punt_attempt", "touchback", "return_yards",
    "return_touchdown", "touchdown", "extra_point_attempt", "extra_point_result",
    "two_point_attempt", "two_point_conv_result", "score_differential", "temp", "wind", "roof",
    "passer_player_id", "kicker_player_id", "air_yards", "epa", "xpass", "safety", "punt_blocked",
    "aborted_play", "play_deleted", "yrdln", "posteam_timeouts_remaining",
    # player attribution
    "passer_player_name", "receiver_player_id", "receiver_player_name", "rusher_player_id",
    "rusher_player_name", "sack_player_id", "sack_player_name", "pass_defense_1_player_id",
    "pass_defense_1_player_name", "interception_player_id", "interception_player_name",
    "yards_after_catch", "game_date",
]


def _fresh(path: Path, max_age_s: float) -> bool:
    return path.exists() and (time.time() - path.stat().st_mtime) < max_age_s


def load_games(refresh: bool = False) -> pd.DataFrame:
    """Schedule + results + closing lines + weather + starting QBs + coaches."""
    SPORTS_DIR.mkdir(parents=True, exist_ok=True)
    path = SPORTS_DIR / "games.csv"
    if refresh or not _fresh(path, 6 * 3600):
        try:
            pd.read_csv(GAMES_URL).to_csv(path, index=False)
        except Exception:
            if not path.exists():
                raise
    g = pd.read_csv(path)
    g["gameday"] = pd.to_datetime(g["gameday"])
    for old, new in CANON.items():  # franchise moves -> one identity across seasons
        for col in ("home_team", "away_team"):
            g[col] = g[col].replace(old, new)
        g["game_id"] = g["game_id"].str.replace(f"_{old}", f"_{new}", regex=False)
    return g.sort_values(["gameday", "game_id"]).reset_index(drop=True)


def load_pbp(seasons: list[int], refresh: bool = False) -> pd.DataFrame:
    """Trimmed play-by-play for the given seasons (cached per season)."""
    SPORTS_DIR.mkdir(parents=True, exist_ok=True)
    frames = []
    this_year = max(seasons)
    for s in seasons:
        path = SPORTS_DIR / f"pbp_{s}.parquet"
        live = s == this_year and s >= pd.Timestamp.today().year - 1
        if refresh or not _fresh(path, 12 * 3600 if live else 10**12):
            try:
                df = pd.read_parquet(PBP_URL.format(season=s))
                df = df[[c for c in PBP_COLS if c in df.columns]]
                df.to_parquet(path, index=False)
            except Exception:
                if not path.exists():
                    continue
        df = pd.read_parquet(path)
        if "receiver_player_id" not in df.columns and not refresh:  # cache predates the player columns
            try:
                df = pd.read_parquet(PBP_URL.format(season=s))
                df = df[[c for c in PBP_COLS if c in df.columns]]
                df.to_parquet(path, index=False)
            except Exception:
                pass
        frames.append(df)
    if not frames:
        raise RuntimeError("no play-by-play available")
    return pd.concat(frames, ignore_index=True)

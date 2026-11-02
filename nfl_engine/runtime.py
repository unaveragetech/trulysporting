"""Process-wide sports engine state: trained model, fresh ratings, player book, per-game predictors."""

from __future__ import annotations

import pickle
import threading
import time

import pandas as pd

from nfl_engine import livetune
from nfl_engine.data import load_pbp
from nfl_engine.liveplay import PlayPredictor
from nfl_engine.matchup import make_spec
from nfl_engine.pipeline import MODEL_PATH, load_bundle
from nfl_engine.players import build_player_book
from nfl_engine.upcoming import catch_up, fresh_book, simulate_upcoming


class Runtime:
    def __init__(self):
        self.state = "idle"  # idle | loading | ready | error | missing
        self.error = ""
        self.bundle = None
        self.games: pd.DataFrame | None = None
        self.book = None
        self.players = None
        self.loaded_at = ""
        self._lock = threading.RLock()
        self._pred: dict = {}
        self._slate: tuple[float, pd.DataFrame] | None = None
        self.scheduler = livetune.NightlyScheduler(self)

    # ------------------------------------------------------------ loading
    def ensure(self, block: bool = False) -> None:
        with self._lock:
            if self.state in ("loading", "ready"):
                return
            if not MODEL_PATH.exists():
                self.state, self.error = "missing", "No trained model - run: python -m nfl_engine train"
                return
            self.state = "loading"
        t = threading.Thread(target=self._load, name="sports-load", daemon=True)
        t.start()
        if block:
            t.join()

    def _load(self, refresh: bool = False) -> None:
        try:
            livetune.load_adj()
            bundle = load_bundle()
            games, book = fresh_book(bundle, refresh=refresh)
            catch_up(bundle, games, book)
            season = int(games["season"].max())
            wk = games[games["home_score"].isna()]["week"].min()
            pbp = load_pbp([season - 1, season])
            players = build_player_book(pbp, season, int(wk) if wk == wk else None)
            del pbp
            with self._lock:
                self.bundle, self.games, self.book, self.players = bundle, games, book, players
                self._pred.clear()
                self._slate = None
                self.state, self.error = "ready", ""
                self.loaded_at = time.strftime("%Y-%m-%d %H:%M")
        except Exception as exc:  # noqa: BLE001
            with self._lock:
                self.state, self.error = "error", str(exc)[:300]

    def refresh_after_games(self) -> dict:
        """Nightly: re-download results, fold them into ratings/residuals, persist the model."""
        t0 = time.time()
        before = len(self.bundle.resbook.done) if self.bundle else 0
        self.state = "loading"
        self._load(refresh=True)
        if self.state != "ready":
            raise RuntimeError(self.error or "reload failed")
        with open(MODEL_PATH, "wb") as f:
            pickle.dump(self.bundle, f)
        return {"games_added_to_residuals": len(self.bundle.resbook.done) - before, "seconds": round(time.time() - t0, 1)}

    # ------------------------------------------------------------ helpers
    def ready(self) -> bool:
        return self.state == "ready"

    def game_row(self, home: str, away: str, start_iso: str | None = None):
        g = self.games
        sel = g[(g["home_team"] == home) & (g["away_team"] == away)]
        if start_iso is not None and len(sel):
            t = pd.Timestamp(start_iso).tz_convert(None).normalize() if pd.Timestamp(start_iso).tzinfo else pd.Timestamp(start_iso)
            sel = sel.iloc[(sel["gameday"] - t).abs().argsort()[:1]]
        elif len(sel):
            sel = sel.sort_values("gameday").tail(1)
        return next(sel.itertuples(), None)

    def predictor(self, home: str, away: str, start_iso: str | None = None):
        key = (home, away, start_iso)
        with self._lock:
            if key in self._pred:
                return self._pred[key]
            row = self.game_row(home, away, start_iso)
            if row is None:
                raise KeyError(f"{away} @ {home} is not on the schedule")
            spec = make_spec(row, self.book, self.bundle.league, self.bundle.tuning)
            spec.game_id = row.game_id
            self._pred[key] = (row, spec, PlayPredictor(self.bundle.league, spec))
            return self._pred[key]

    def slate(self, week: int | None = None, max_age: float = 900.0) -> pd.DataFrame:
        with self._lock:
            if self._slate and time.time() - self._slate[0] < max_age and week is None:
                return self._slate[1]
        df = simulate_upcoming(self.bundle, self.games, self.book, n=1500, week=week, workers=4)
        if week is None:
            with self._lock:
                self._slate = (time.time(), df)
        return df


RT = Runtime()

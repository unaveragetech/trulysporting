"""League data engine.

One background thread per league keeps the local SQLite database complete,
so every page can read from the DB instead of asking the user to load data:

  for each season (current first, then older):
    1. every game on the schedule (scoreboard date ranges)
    2. teams (+ rosters for the current season)
    3. the box score / summary of every completed game
  then sleep, and re-check the current season for newly finished games.

Past seasons are marked complete in the `config` table and never refetched.
"""
import threading
import time
from datetime import datetime, timedelta
from concurrent.futures import ThreadPoolExecutor
from typing import Any, Callable, Dict, List

DEFAULT_SEASONS = 6          # current + 5 previous
RECHECK_SECONDS = 600        # how often the current season is re-synced
SUMMARY_THREADS = 2          # requests are throttled globally anyway


class LeagueSync:
    def __init__(self, ep: str, db: Any, worker: Any,
                 season_for: Callable[[str], int], date_ranges: Callable,
                 seasons: int = DEFAULT_SEASONS):
        self.ep = ep
        self.cat, self.spt = ep.split('/')
        self.db, self.worker = db, worker
        self.season_for, self.date_ranges = season_for, date_ranges
        self.seasons = seasons
        self.status: Dict[str, Any] = {'phase': 'starting', 'season': None,
                                       'done': 0, 'total': 0, 'error': '', 'cycle': 0}
        self._stop = threading.Event()
        self.thread = threading.Thread(target=self._run, daemon=True,
                                       name=f'LeagueSync-{ep}')

    # ── public ──────────────────────────────────────────────
    def start(self) -> 'LeagueSync':
        self.thread.start()
        return self

    def stop(self) -> None:
        self._stop.set()

    def season_list(self) -> List[int]:
        cur = self.season_for(self.cat)
        return [cur - i for i in range(self.seasons)]

    # ── internals ───────────────────────────────────────────
    def _set(self, **kw) -> None:
        self.status.update(kw)

    def _run(self) -> None:
        while not self._stop.is_set():
            try:
                self._cycle()
                self._prune_cache()
                self._set(phase='idle', done=0, total=0)
            except Exception as e:  # keep the engine alive
                self._set(phase='error', error=str(e)[:200])
            self.status['cycle'] += 1
            self._stop.wait(RECHECK_SECONDS)

    def _cycle(self) -> None:
        seasons = self.season_list()
        cur = seasons[0]
        self._set(phase='teams', season=cur)
        self.worker.fetch_and_process(self.cat, self.spt, 'teams', force_refresh=True)
        teams = self.db.get_teams_df(self.ep)

        for yr in seasons:
            if self._stop.is_set():
                return
            done_key = f'engine_done_{self.ep}_{yr}'
            if yr != cur and self.db.get_config(done_key, ''):
                continue  # past season already complete
            self._sync_schedule(yr)
            if yr == cur and not teams.empty:
                self._sync_rosters(teams)
            ok = self._sync_box_scores(yr)
            # Only a past season with games and every box score is "complete".
            if yr != cur and ok and not self._stop.is_set():
                self.db.update_config(done_key, str(time.time()))

    def _prune_cache(self) -> None:
        """Raw game-summary JSON is already parsed into tables; don't keep it forever."""
        conn = self.db.get_connection()
        conn.execute("DELETE FROM api_cache WHERE endpoint_key LIKE '%\\_summary\\_%' ESCAPE '\\' "
                     "AND fetched_at < datetime('now', '-2 days')")
        conn.commit()
        conn.close()

    def _sync_schedule(self, yr: int) -> None:
        chunks = []
        for lbl, params in self.date_ranges(self.cat, self.spt, yr):
            rng = str(params.get('dates', ''))
            if '-' not in rng:
                chunks.append((lbl, params))
                continue
            # ESPN now rejects date ranges (HTTP 400): walk the range day by day,
            # skipping days in the future.
            a, b = (datetime.strptime(x, '%Y%m%d') for x in rng.split('-'))
            last = min(b, datetime.now())
            while a <= last:
                chunks.append((f'{a:%Y-%m-%d}', {**params, 'dates': f'{a:%Y%m%d}'}))
                a += timedelta(days=1)
        if yr == self.season_for(self.cat):
            # Current season: also re-check the next two weeks of schedule.
            for i in range(1, 15):
                d = datetime.now() + timedelta(days=i)
                if any('-' in str(p.get('dates', '')) for _, p in
                       self.date_ranges(self.cat, self.spt, yr)):
                    chunks.append((f'{d:%Y-%m-%d}', {'dates': f'{d:%Y%m%d}'}))
        self._set(phase='schedule', season=yr, done=0, total=len(chunks))
        for i, (_lbl, params) in enumerate(chunks, 1):
            if self._stop.is_set():
                return
            self._fetch_chunk(params)
            self._set(done=i)

    def _fetch_chunk(self, params: dict) -> None:
        """Fetch one scoreboard chunk; ESPN rejects long date ranges (HTTP 400),
        so split a failing range in half until it's accepted (down to a day)."""
        r = self.worker.fetch_and_process(self.cat, self.spt, 'scoreboard',
                                          force_refresh=True, params=params)
        rng = str(params.get('dates', ''))
        if r is not None or '400' not in str(self.worker.last_error) or '-' not in rng:
            return
        a, b = (datetime.strptime(x, '%Y%m%d') for x in rng.split('-'))
        if a >= b:
            return
        mid = a + (b - a) / 2
        mid = datetime(mid.year, mid.month, mid.day)
        for lo, hi in ((a, mid), (mid + timedelta(days=1), b)):
            if lo > hi or self._stop.is_set():
                continue
            d = lo.strftime('%Y%m%d') if lo == hi else f"{lo:%Y%m%d}-{hi:%Y%m%d}"
            self._fetch_chunk({**params, 'dates': d})

    def _sync_rosters(self, teams) -> None:
        self._set(phase='rosters', done=0, total=len(teams))
        for i, t in enumerate(teams.itertuples(), 1):
            if self._stop.is_set():
                return
            # fetch_team_roster caches for a day, so this is cheap on re-runs
            self.worker.fetch_team_roster(self.cat, self.spt, str(t.team_id), t.team_abbr)
            self._set(done=i)

    def _sync_box_scores(self, yr: int) -> bool:
        games = self.db.get_season_games_df(self.cat, self.spt, yr)
        if games.empty:
            return False  # nothing stored → never mark the season complete
        final = games[games['status'].astype(str).str.upper().str.contains('FINAL')]
        have = self.db.has_summaries(list(final['event_id']))
        missing = [str(e) for e in final['event_id'] if e and str(e) not in have]
        self._set(phase='box scores', season=yr, done=0, total=len(missing))
        if missing:
            done = 0
            with ThreadPoolExecutor(max_workers=SUMMARY_THREADS) as pool:
                for _ in pool.map(self._fetch_summary, missing):
                    done += 1
                    self._set(done=done)
                    if self._stop.is_set():
                        return False
            self.db.repopulate_player_game_stats()
        return len(self.db.has_summaries(missing)) == len(missing)

    def _fetch_summary(self, event_id: str) -> None:
        try:
            self.worker.fetch_game_summary(self.cat, self.spt, event_id)
        except Exception:
            pass


def describe(status: Dict[str, Any], label_season: Callable[[int], str]) -> str:
    """One-line human status for the header chip."""
    ph = status.get('phase')
    if ph == 'idle':
        return '✅ All seasons up to date'
    if ph == 'error':
        return f"⚠️ Sync paused: {status.get('error', '')}"
    if ph == 'starting':
        return '⏳ Starting data sync…'
    season = status.get('season')
    s = label_season(season) if season else ''
    done, total = status.get('done', 0), status.get('total', 0)
    prog = f' {done}/{total}' if total else ''
    return f'🔄 Syncing {s} {ph}{prog}'

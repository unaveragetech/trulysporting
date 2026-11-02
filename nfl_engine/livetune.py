"""Nightly tuning from live plays, run after the last game of the day has finished.

Every live play the engine predicted is logged with its pre-snap probabilities and what happened.  Each
night the mismatches (pass rate, completion, sack, interception, yards per completion, yards per rush) are
folded into small, shrunk, bounded additive corrections that every future simulation and live prediction
uses.  The nightly job also refreshes completed-game data and updates the team-residual book.
"""

from __future__ import annotations

import json
import os
import pickle
import threading
import time
from datetime import date, datetime
from pathlib import Path

import numpy as np

from nfl_engine import liveplay
from nfl_engine.data import SPORTS_DIR
from nfl_engine.matchup import LIVE_ADJ

ADJ_FILE = SPORTS_DIR / "live_tuning.json"
STATE_FILE = SPORTS_DIR / "tune_state.json"
# key -> (prior strength in plays, learning rate, bound)
SPEC = {
    "pass": (800.0, 0.5, 0.04), "comp": (600.0, 0.5, 0.04), "sack": (900.0, 0.5, 0.02),
    "int": (2000.0, 0.5, 0.01), "ypcomp": (500.0, 0.5, 1.5), "ypr": (500.0, 0.5, 0.8),
}
_lock = threading.Lock()


def load_adj() -> dict:
    try:
        d = json.loads(ADJ_FILE.read_text(encoding="utf-8"))
    except Exception:
        d = {}
    LIVE_ADJ.clear()
    LIVE_ADJ.update({k: float(v) for k, v in d.items() if k in SPEC})
    return dict(LIVE_ADJ)


def _save_adj() -> None:
    ADJ_FILE.write_text(json.dumps(LIVE_ADJ, indent=2), encoding="utf-8")


def load_state() -> dict:
    try:
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except Exception:
        return {"hour": int(os.getenv("SPORTS_TUNE_HOUR", "0")), "history": [], "last_run_date": None, "running": False}


def save_state(st: dict) -> None:
    STATE_FILE.write_text(json.dumps(st, indent=2, default=str), encoding="utf-8")


def tune_from_logs(eta_scale: float = 1.0) -> dict:
    """Fold every not-yet-used logged live play into LIVE_ADJ.  Returns a report."""
    rows, logs = [], []
    for f in sorted(liveplay.LIVE_DIR.glob("*.json")) if liveplay.LIVE_DIR.exists() else []:
        try:
            log = json.loads(f.read_text(encoding="utf-8"))
        except Exception:
            continue
        logs.append(log)
        rows += [p for p in log["plays"].values() if p.get("pred") and p.get("score", {}).get("p_actual_type")
                 and not p.get("tuned")]
    rep = {"plays": len(rows), "deltas": {}, "applied": {}}
    if len(rows) < 30:
        return rep
    passes = [r for r in rows if r["cat"] in ("comp", "inc", "int", "sack")]
    atts = [r for r in rows if r["cat"] in ("comp", "inc", "int")]
    comps = [r for r in rows if r["cat"] == "comp"]
    runs = [r for r in rows if r["cat"] == "run"]
    y = lambda r: (r["yards"] or 0)
    obs = {
        "pass": (len(rows), np.mean([r["cat"] in ("comp", "inc", "int", "sack") for r in rows])
                 - np.mean([r["pred"]["p_pass"] for r in rows])),
        "comp": (len(atts), (np.mean([r["cat"] == "comp" for r in atts]) - np.mean([r["pred"]["p_comp_att"] for r in atts]))
                 if atts else 0.0),
        "sack": (len(passes), (np.mean([r["cat"] == "sack" for r in passes]) - np.mean([r["pred"]["p_sack_db"] for r in passes]))
                 if passes else 0.0),
        "int": (len(atts), (np.mean([r["cat"] == "int" for r in atts]) - np.mean([r["pred"]["p_int_att"] for r in atts]))
                if atts else 0.0),
        "ypcomp": (len(comps), (np.mean([y(r) for r in comps]) - np.mean([r["pred"]["exp_comp_yards"] for r in comps]))
                   if comps else 0.0),
        "ypr": (len(runs), (np.mean([y(r) for r in runs]) - np.mean([r["pred"]["exp_run_yards"] for r in runs]))
                if runs else 0.0),
    }
    with _lock:
        for k, (n, delta) in obs.items():
            n0, eta, bound = SPEC[k]
            step = eta * eta_scale * n / (n + n0) * float(delta)
            new = float(np.clip(LIVE_ADJ.get(k, 0.0) + step, -bound, bound))
            rep["deltas"][k] = float(delta)
            rep["applied"][k] = new
            LIVE_ADJ[k] = new
        _save_adj()
    for log in logs:
        touched = False
        for p in log["plays"].values():
            if p.get("pred") and not p.get("tuned"):
                p["tuned"] = True
                touched = True
        if touched:
            liveplay.save_log(log)
    return rep


def _games_active_or_pending(now: datetime) -> bool:
    """True while any game is in progress, or scheduled to have started already but not final."""
    for g in liveplay.scoreboard():
        if g["state"] == "in":
            return True
        if g["state"] == "pre":
            start = datetime.fromisoformat(g["start"].replace("Z", "+00:00")).astimezone().replace(tzinfo=None)
            if start <= now:
                return True
    return False


def nightly(runtime, force: bool = False) -> dict:
    """The full nightly job; safe to call manually."""
    st = load_state()
    if st.get("running"):
        return {"skipped": "already running"}
    st["running"] = True
    save_state(st)
    t0 = time.time()
    entry: dict = {"started": datetime.now().isoformat(timespec="seconds")}
    try:
        entry["live"] = tune_from_logs()
        entry["refresh"] = runtime.refresh_after_games()
        entry["status"] = "ok"
    except Exception as exc:  # noqa: BLE001
        entry["status"] = f"error: {str(exc)[:200]}"
    entry["seconds"] = round(time.time() - t0, 1)
    st = load_state()
    st["running"] = False
    st["last_run_date"] = date.today().isoformat() if entry["status"] == "ok" else st.get("last_run_date")
    st["history"] = (st.get("history") or [])[-29:] + [entry]
    save_state(st)
    return entry


class NightlyScheduler:
    def __init__(self, runtime):
        self.rt = runtime
        self._stop = threading.Event()
        self._t: threading.Thread | None = None
        self.waiting_reason = ""

    def start(self):
        if self._t and self._t.is_alive():
            return
        self._stop.clear()
        self._t = threading.Thread(target=self._loop, name="sports-nightly", daemon=True)
        self._t.start()

    def stop(self):
        self._stop.set()

    def next_run(self) -> str:
        from datetime import timedelta

        st = load_state()
        now = datetime.now()
        slot = now.replace(hour=int(st.get("hour", 0)), minute=0, second=0, microsecond=0)
        ran_today = st.get("last_run_date") == now.date().isoformat()
        if now >= slot and not ran_today:
            return "due - waiting for games to finish" if self.waiting_reason else "due now"
        if now >= slot:
            slot += timedelta(days=1)
        return slot.isoformat(timespec="minutes")

    def _loop(self):
        while not self._stop.is_set():
            try:
                st = load_state()
                now = datetime.now()
                due = now.hour >= int(st.get("hour", 0)) and st.get("last_run_date") != now.date().isoformat()
                if due and not st.get("running"):
                    if _games_active_or_pending(now):
                        self.waiting_reason = "games still in progress"
                    else:
                        self.waiting_reason = ""
                        nightly(self.rt)
            except Exception as exc:  # noqa: BLE001
                self.waiting_reason = f"scheduler error: {str(exc)[:80]}"
            self._stop.wait(120)

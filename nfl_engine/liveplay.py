"""Live NFL feed (ESPN public JSON) and play-by-play engine predictions to compare with what happened."""

from __future__ import annotations

import json
import math
import random
import re
import threading
import time
from pathlib import Path

import numpy as np
import requests

from nfl_engine.data import CANON, SPORTS_DIR
from nfl_engine.league import GSR_IDX, SD_IDX, YTG_MAX, ytg_bucket, zone
from nfl_engine.sim import Engine, GameSpec, SideParams

LIVE_DIR = SPORTS_DIR / "live"
ESPN = "https://site.api.espn.com/apis/site/v2/sports/football/nfl"
ESPN_ABBR = {"WSH": "WAS", "LAR": "LA", "JAC": "JAX", "OAK": "LV", "SD": "LAC", "STL": "LA"}
_cache: dict[str, tuple[float, object]] = {}
_lock = threading.Lock()


def _get(url: str, ttl: float = 15.0):
    now = time.time()
    hit = _cache.get(url)
    if hit and now - hit[0] < ttl:
        return hit[1]
    r = requests.get(url, timeout=15, headers={"User-Agent": "trulysporting-nfl/1.0"})
    r.raise_for_status()
    data = r.json()
    _cache[url] = (now, data)
    return data


def abbr(a: str) -> str:
    a = ESPN_ABBR.get(a, a)
    return CANON.get(a, a)


def scoreboard(dates: str | None = None) -> list[dict]:
    url = f"{ESPN}/scoreboard" + (f"?dates={dates}" if dates else "")
    out = []
    for e in _get(url, 10)["events"]:
        c = e["competitions"][0]
        home = next(t for t in c["competitors"] if t["homeAway"] == "home")
        away = next(t for t in c["competitors"] if t["homeAway"] == "away")
        st = e["status"]
        out.append({
            "event": e["id"], "start": e["date"], "state": st["type"]["state"],  # pre | in | post
            "status": st["type"]["description"], "detail": st["type"].get("shortDetail", ""),
            "period": st.get("period", 0), "clock": st.get("displayClock", ""),
            "home": abbr(home["team"]["abbreviation"]), "away": abbr(away["team"]["abbreviation"]),
            "home_score": int(home.get("score") or 0), "away_score": int(away.get("score") or 0),
            "home_id": home["team"]["id"], "away_id": away["team"]["id"],
        })
    return out


def any_game_active() -> bool:
    return any(g["state"] == "in" for g in scoreboard())


# ---------------------------------------------------------------- classify ESPN plays


def classify(play: dict) -> tuple[str, bool]:
    """-> (category, is_td).  Categories: run comp inc sack int punt fg penalty other."""
    typ = (play.get("type") or {}).get("text", "").lower()
    txt = (play.get("text") or "").lower()
    td = bool(play.get("scoringPlay")) and "touchdown" in typ + txt
    if any(k in typ for k in ("timeout", "end of", "end period", "two-minute", "coin toss", "kickoff", "extra point",
                              "two point", "two-point")):
        return "other", False
    if "punt" in typ:
        return "punt", False
    if "field goal" in typ or "field goal" in txt[:80] and "no good" in txt:
        return "fg", False
    if "kneel" in txt or "spike" in txt or "kneel" in typ:
        return "other", False
    if "penalty" in typ and "reception" not in typ:
        return "penalty", False
    if "sack" in typ or " sacked " in txt:
        return "sack", False
    if "interception" in typ or "intercepted" in txt:
        return "int", False
    if "incomplet" in typ:
        return "inc", False
    if "pass" in typ or "reception" in typ:
        return "comp", td
    if "rush" in typ or "run" in typ or "scramble" in txt:
        return "run", td
    if "fumble" in typ:
        return ("comp" if " pass " in txt else "run"), td
    return "other", False


def clock_secs(s: str) -> int:
    m = re.match(r"(\d+):(\d+)", s or "")
    return int(m.group(1)) * 60 + int(m.group(2)) if m else 0


def parse_plays(summary: dict) -> tuple[list[dict], dict]:
    comp = summary["header"]["competitions"][0]
    ids = {}
    for t in comp["competitors"]:
        ids[t["id"]] = (abbr(t["team"]["abbreviation"]), t["homeAway"])
    drives = []
    d = summary.get("drives") or {}
    drives += d.get("previous") or []
    if d.get("current"):
        drives.append(d["current"])
    plays = []
    hs = as_ = 0
    for dr in drives:
        for p in dr.get("plays", []):
            st = p.get("start") or {}
            tid = (st.get("team") or {}).get("id")
            cat, td = classify(p)
            per = (p.get("period") or {}).get("number", 1)
            secs = clock_secs((p.get("clock") or {}).get("displayValue", ""))
            gsr = (4 - per) * 900 + secs if per <= 4 else secs
            plays.append({
                "id": p["id"], "seq": int(p.get("sequenceNumber") or 0), "text": p.get("text", ""), "cat": cat, "td": td,
                "period": per, "clock": (p.get("clock") or {}).get("displayValue", ""), "gsr": gsr,
                "down": st.get("down") or 0, "ytg": st.get("distance") or 0, "yl": st.get("yardsToEndzone"),
                "off": ids.get(tid, (None, None))[0], "off_side": ids.get(tid, (None, None))[1],
                "yards": p.get("statYardage"), "scoring": bool(p.get("scoringPlay")),
                "turnover": bool(p.get("isTurnover")), "is_penalty": bool(p.get("isPenalty")),
                "home_before": hs, "away_before": as_,
                "home_score": p.get("homeScore", hs), "away_score": p.get("awayScore", as_),
                "type": (p.get("type") or {}).get("text", ""),
                "end": p.get("end") or {},
                "end_side": ids.get(((p.get("end") or {}).get("team") or {}).get("id"), (None, None))[1],
            })
            hs, as_ = p.get("homeScore", hs), p.get("awayScore", as_)
    plays.sort(key=lambda x: x["seq"])
    return plays, {"home": next(v[0] for v in ids.values() if v[1] == "home"),
                   "away": next(v[0] for v in ids.values() if v[1] == "away")}


# ---------------------------------------------------------------- engine predictions for one snap


class PlayPredictor:
    """Pre-snap predictions for any game state, using the same rates/pools as the simulator."""

    def __init__(self, L, spec: GameSpec):
        self.L, self.spec = L, spec
        self.eng = Engine(L, spec)
        self._np: dict = {}

    def _arr(self, kind: str, key):
        k = (kind, key)
        if k not in self._np:
            src = {"run": self.L.run_pool, "comp": self.L.comp_pool, "scr": self.L.scr_pool}.get(kind)
            self._np[k] = np.array(src[key] if kind != "sack" else self.L.sack_pool, float)
        return self._np[k]

    def predict(self, side: int, down: int, ytg: int, yl: int, sd: int, gsr: int, period: int) -> dict:
        L, eng = self.L, self.eng
        o: SideParams = self.spec.sides[side]
        qtr = min(period, 4)
        hsr = gsr - 1800 if gsr > 1800 else gsr
        from nfl_engine.league import clock_mode

        mode = clock_mode(sd, qtr, hsr)
        p_pass = eng._pass_prob(o, down, ytg, yl, sd, qtr, hsr, gsr, mode)
        z, b = zone(yl), ytg_bucket(ytg)
        rt = L.rates[(z, b)]
        ps, pc_ = max(0.0, rt["sack"] + o.d_sack), max(0.0, rt["scr"] + o.d_scr)
        p_int_att = max(0.001, rt["int"] + o.d_int)
        p_comp_att = min(0.95, max(0.2, rt["comp"] + o.d_comp))
        p_att = max(0.0, 1 - ps - pc_)
        cats = {
            "run": 1 - p_pass, "sack": p_pass * ps, "scr": p_pass * pc_,
            "int": p_pass * p_att * p_int_att,
            "comp": p_pass * p_att * min(p_comp_att, 1 - p_int_att),
        }
        cats["inc"] = max(0.0, 1 - sum(cats.values()))
        # yardage mixture
        vals, wts = [], []

        def add(arr, w):
            vals.append(arr)
            wts.append(np.full(len(arr), w / len(arr)))

        run = self._arr("run", (z, b))
        run = np.where(run >= 900, yl, np.minimum(run + o.d_ypr, yl - 1))
        add(run, cats["run"])
        add(np.minimum(self._arr("sack", None), 0), cats["sack"])
        scr = self._arr("scr", z)
        add(np.where(scr >= 900, yl, np.minimum(scr + 0.5 * o.d_ypr, yl - 1)), cats["scr"])
        cp = self._arr("comp", (z, b))
        add(np.where(cp >= 900, yl, np.minimum(cp + o.d_ypcomp, yl - 1)), cats["comp"])
        add(np.zeros(1), cats["inc"] + cats["int"])
        v, w = np.concatenate(vals), np.concatenate(wts)
        order = np.argsort(v)
        v, w = v[order], w[order]
        cw = np.cumsum(w)
        q = lambda p: float(v[min(len(v) - 1, int(np.searchsorted(cw, p * cw[-1])))])
        out = {
            "p_pass": p_pass, "cats": cats, "p_comp_att": p_comp_att, "p_sack_db": ps, "p_int_att": p_int_att,
            "exp_yards": float((v * w).sum() / w.sum()),
            "y_p10": q(0.1), "y_p50": q(0.5), "y_p90": q(0.9),
            "p_first": float(w[v >= ytg].sum() / w.sum()), "p_td": float(w[v >= yl].sum() / w.sum()),
            "p_turnover": cats["int"] + L.fum_rate + o.d_fum,
            "exp_comp_yards": float(np.where(cp >= 900, yl, np.minimum(cp + o.d_ypcomp, yl - 1)).mean()),
            "exp_run_yards": float(run.mean()),
            "_v": v, "_cw": cw,
        }
        if down == 4:
            iy = min(ytg, YTG_MAX) - 1
            pr = L.fourth_grid[iy, max(0, min(98, yl - 1)), SD_IDX[max(-30, min(30, sd)) + 30],
                               GSR_IDX[int(max(0, min(3600, gsr)) // 10)]]
            out["dec"] = {"go": float(pr[0]), "punt": float(pr[1]), "fg": float(pr[2])}
        return out

    @staticmethod
    def pit(pred: dict, y: float) -> float:
        """Mid-rank percentile of the actual yardage in the predicted distribution (0-1)."""
        v, cw = pred["_v"], pred["_cw"]
        lo = cw[np.searchsorted(v, y, "left") - 1] if np.searchsorted(v, y, "left") > 0 else 0.0
        hi = cw[min(len(cw) - 1, np.searchsorted(v, y, "right") - 1)] if np.searchsorted(v, y, "right") > 0 else 0.0
        return float((lo + hi) / 2 / cw[-1])


# ---------------------------------------------------------------- scoring one logged play


def score_play(pred: dict, play: dict) -> dict:
    cat = play["cat"]
    c = pred["cats"]
    pcat = {"run": c["run"] + c["scr"], "sack": c["sack"], "int": c["int"], "comp": c["comp"], "inc": c["inc"]}
    res: dict = {}
    if cat in pcat:
        key = "run" if cat == "run" else cat
        p = max(1e-4, pcat[key])
        res["p_actual_type"] = p
        res["surprise"] = -math.log(p)
        y = play["yards"] if play["yards"] is not None else 0
        res["yard_pct"] = PlayPredictor.pit(pred, y)
        res["converted"] = bool(play["td"] or (y >= play["ytg"] and play["ytg"] > 0))
    if "dec" in pred and cat in ("run", "comp", "inc", "sack", "int", "punt", "fg"):
        d = "punt" if cat == "punt" else "fg" if cat == "fg" else "go"
        res["dec_actual"] = d
        res["dec_p"] = pred["dec"][d]
    return res


def public(pred: dict) -> dict:
    return {k: v for k, v in pred.items() if not k.startswith("_")}


# ---------------------------------------------------------------- persistent per-game logs


def log_path(event: str) -> Path:
    LIVE_DIR.mkdir(parents=True, exist_ok=True)
    return LIVE_DIR / f"{event}.json"


def load_log(event: str) -> dict:
    p = log_path(event)
    if p.exists():
        try:
            return json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            pass
    return {"event": event, "plays": {}}


def save_log(log: dict) -> None:
    log_path(log["event"]).write_text(json.dumps(log), encoding="utf-8")


def process_event(event: str, predictor: PlayPredictor, spec: GameSpec, home: str) -> dict:
    """Fetch the game, predict + score any plays not yet logged, return the log."""
    summ = _get(f"{ESPN}/summary?event={event}", 12)
    plays, teams = parse_plays(summ)
    with _lock:
        log = load_log(event)
        log.update({"home": teams["home"], "away": teams["away"], "game_id": getattr(spec, "game_id", None)})
        changed = False
        for pl in plays:
            if pl["id"] in log["plays"] and log["plays"][pl["id"]].get("done"):
                continue
            rec = {k: pl[k] for k in ("id", "seq", "text", "cat", "td", "period", "clock", "down", "ytg", "yl", "off",
                                       "yards", "scoring", "turnover", "type", "gsr", "home_score", "away_score")}
            scrim = pl["cat"] in ("run", "comp", "inc", "sack", "int", "punt", "fg") and 1 <= pl["down"] <= 4 \
                and pl["yl"] is not None and pl["off"] in (teams["home"], teams["away"]) and not pl["is_penalty"]
            if scrim:
                side = 0 if pl["off"] == teams["home"] else 1
                before = (pl["home_before"], pl["away_before"])
                sd = (before[0] - before[1]) * (1 if side == 0 else -1)
                pr = predictor.predict(side, pl["down"], max(1, pl["ytg"]), max(1, int(pl["yl"])), sd, pl["gsr"],
                                       pl["period"])
                rec["pred"] = public(pr)
                rec["score"] = score_play(pr, pl)
            rec["done"] = True
            log["plays"][pl["id"]] = rec
            changed = True
        if changed:
            save_log(log)
    log["_plays_parsed"] = plays
    return log


def summarize_log(log: dict) -> dict:
    rows = [p for p in log["plays"].values() if p.get("pred") and p.get("score", {}).get("p_actual_type")]
    if not rows:
        return {"n": 0}
    n = len(rows)
    passes = [r for r in rows if r["cat"] in ("comp", "inc", "int", "sack")]
    atts = [r for r in rows if r["cat"] in ("comp", "inc", "int")]
    pct = [r["score"]["yard_pct"] for r in rows if "yard_pct" in r["score"]]
    return {
        "n": n,
        "pass_rate_pred": float(np.mean([r["pred"]["p_pass"] for r in rows])),
        "pass_rate_act": float(np.mean([r["cat"] in ("comp", "inc", "int", "sack") for r in rows])),
        "yards_pred": float(np.mean([r["pred"]["exp_yards"] for r in rows])),
        "yards_act": float(np.mean([(r["yards"] or 0) for r in rows])),
        "first_pred": float(np.mean([r["pred"]["p_first"] for r in rows])),
        "first_act": float(np.mean([r["score"]["converted"] for r in rows])),
        "comp_pred": float(np.mean([r["pred"]["p_comp_att"] for r in atts])) if atts else None,
        "comp_act": float(np.mean([r["cat"] == "comp" for r in atts])) if atts else None,
        "sack_pred": float(np.mean([r["pred"]["p_sack_db"] for r in passes])) if passes else None,
        "sack_act": float(np.mean([r["cat"] == "sack" for r in passes])) if passes else None,
        "to_pred": float(np.sum([r["pred"]["p_turnover"] for r in rows])),
        "to_act": int(sum(r["turnover"] for r in rows)),
        "mean_surprise": float(np.mean([r["score"]["surprise"] for r in rows])),
        "pit_lo10": float(np.mean([p < 0.1 for p in pct])) if pct else None,
        "pit_hi10": float(np.mean([p > 0.9 for p in pct])) if pct else None,
    }


def live_win_prob(L, spec: GameSpec, plays: list[dict], sims: int = 300) -> float | None:
    """Engine's current home win probability from the latest game state (regulation only)."""
    last = next((p for p in reversed(plays) if p["cat"] != "other" or p["down"]), None)
    if last is None or not plays:
        return None
    end = last["end"]
    if last["period"] >= 5 or not end or end.get("yardsToEndzone") is None or last.get("end_side") is None:
        return None
    down, ytg, yl = end.get("down") or 1, end.get("distance") or 10, end["yardsToEndzone"]
    pos_side = 0 if last["end_side"] == "home" else 1
    hs, as_ = last["home_score"], last["away_score"]
    gsr = last["gsr"]
    first = next((p for p in plays if p["cat"] in ("run", "comp", "inc", "sack", "int", "punt", "fg")), None)
    fr = None if first is None else (0 if first["off_side"] == "home" else 1)
    eng = Engine(L, spec)
    rnd = random.Random(7)
    w = 0.0
    for _ in range(sims):
        r = eng.run_from(rnd, (hs, as_), max(gsr, 1), pos_side, int(yl), int(down), int(ytg), fr)
        w += 1.0 if r["home"] > r["away"] else 0.5 if r["home"] == r["away"] else 0.0
    return w / sims

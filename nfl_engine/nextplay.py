"""What happens next in a live game: the likely next call and a Monte-Carlo projection of the next several plays.

Validation (2024-25 held-out plays, ``docs/NFL_ENGINE.md``): the engine's pre-snap pass/run call is right 71.1% of the
time; what this offence has done earlier in the same game adds a little (log loss 0.5323 -> 0.5311, weight ``IG_W``);
past meetings between the same two teams add nothing measurable, so they are shown but not used.
"""

from __future__ import annotations

import copy
import random
from collections import Counter

import numpy as np

from nfl_engine.sim import Engine

IG_W = 2.8  # logit weight on (actual - predicted pass rate so far this game, shrunk with 20 pseudo-plays)
CALLS = ("pass", "run", "punt", "fg")
_KIND_CALL = {"comp": "pass", "inc": "pass", "sack": "pass", "int": "pass", "scr": "pass", "run": "run",
              "punt": "punt", "fg": "fg"}


def team_ig(log: dict, team: str) -> float:
    """This offence's pass-rate surprise so far in the game (log of graded live plays), shrunk to ~0."""
    s = n = 0
    for p in sorted(log.get("plays", {}).values(), key=lambda x: x["seq"]):
        if p.get("off") == team and p.get("pred") and p["cat"] in ("run", "comp", "inc", "sack", "int"):
            s += float(p["cat"] != "run") - p["pred"]["p_pass"]
            n += 1
    return s / (n + 20.0)


def _with_ig(spec, poss: int, ig: float):
    """Copy of the spec whose offence ``poss`` carries the in-game script shift."""
    sp = copy.copy(spec)
    sides = list(spec.sides)
    o = copy.copy(sides[poss])
    sh = None if o.tshift is None else {**o.tshift, "all": o.tshift["all"] + IG_W * ig}
    o.tshift = sh
    if sh is None:
        o.proe = o.proe + 0.25 * ig  # fallback without tendency data: small probability-space nudge
    sides[poss] = o
    sp.sides = tuple(sides)
    return sp


def project(L, spec, state: dict, n_plays: int = 5, sims: int = 400, ig: float = 0.0, seed: int = 11) -> dict:
    """Simulate the rest of the game ``sims`` times from ``state`` and summarise the next ``n_plays`` snaps.

    ``state``: down, ytg, yl (to the end zone), poss (0 home / 1 away), hs, as, gsr, first_recv.
    Returns per-step call probabilities with expected yardage, plus the most common call sequences.
    """
    sp = _with_ig(spec, state["poss"], ig) if ig else spec
    eng = Engine(L, sp)
    rnd = random.Random(seed)
    steps = [Counter() for _ in range(n_plays)]
    yards = [[] for _ in range(n_plays)]
    seqs: Counter = Counter()
    first_poss = state["poss"]
    for _ in range(sims):
        eng.trace = []
        eng.run_from(rnd, (state["hs"], state["as"]), max(state["gsr"], 1), state["poss"], int(state["yl"]),
                     int(state["down"]), int(state["ytg"]), state.get("first_recv"))
        ev = eng.trace[:n_plays]
        calls = []
        for k in range(n_plays):
            if k < len(ev):
                down, ytg, yl, y, kind, p = ev[k]
                call = _KIND_CALL.get(kind, "run")
                steps[k][call] += 1
                steps[k]["same_off" if p == first_poss else "other_off"] += 1
                if kind in ("comp", "inc", "run", "scr", "sack"):
                    yards[k].append(y)
                steps[k]["turnover"] += kind == "int"
                steps[k]["first"] += (kind in ("comp", "run", "scr") and y >= ytg)
                calls.append(call[0].upper() if call in ("pass", "run") else call)
            else:
                steps[k]["end"] += 1
        seqs["-".join(calls)] += 1
    out = []
    for k in range(n_plays):
        c = steps[k]
        n = sims - c["end"]
        out.append({"play": k + 1, **{f"p_{x}": c[x] / sims for x in CALLS}, "p_game_over": c["end"] / sims,
                    "exp_yards": float(np.mean(yards[k])) if yards[k] else 0.0,
                    "p_turnover": c["turnover"] / sims, "p_first_down": c["first"] / sims,
                    "p_same_offense": c["same_off"] / max(1, n)})
    top = [{"sequence": s, "prob": v / sims} for s, v in seqs.most_common(6)]
    return {"steps": out, "sequences": top, "sims": sims, "ig": ig}


# ---------------------------------------------------------------- ledger: grade the 5-plays-ahead calls once they have happened


def _proj_path(event: str):
    from nfl_engine.ingame import LEDGER_DIR

    LEDGER_DIR.mkdir(parents=True, exist_ok=True)
    return LEDGER_DIR / f"proj_{event}.jsonl"


def record_projection(event: str, last_seq: int, proj: dict) -> None:
    """Remember what we predicted would happen next, once per game state (keyed by the last play seen)."""
    import json

    path = _proj_path(event)
    if path.exists() and f'"seq": {last_seq},' in path.read_text(encoding="utf-8")[-400:]:
        return
    steps = [{k: round(s[k], 4) for k in ("p_pass", "p_run", "p_punt", "p_fg", "p_game_over")} for s in proj["steps"]]
    with open(path, "a", encoding="utf-8") as f:
        f.write(json.dumps({"seq": last_seq, "steps": steps}) + "\n")


def grade_projections() -> dict:
    """Per step ahead: how much probability we put on the call that actually came, and how often the top call was right."""
    import json
    import math

    from nfl_engine.ingame import LEDGER_DIR
    from nfl_engine.liveplay import load_log

    cls = {"run": "run", "comp": "pass", "inc": "pass", "sack": "pass", "int": "pass", "punt": "punt", "fg": "fg"}
    agg = {}
    for path in sorted(LEDGER_DIR.glob("proj_*.jsonl")):
        log = load_log(path.stem[5:])
        plays = sorted((p for p in log.get("plays", {}).values() if p["cat"] in cls), key=lambda p: p["seq"])
        for line in path.read_text(encoding="utf-8").splitlines():
            r = json.loads(line)
            later = [p for p in plays if p["seq"] > r["seq"]]
            for k, st in enumerate(r["steps"]):
                if k >= len(later):
                    break
                actual = cls[later[k]["cat"]]
                p = max(1e-3, st[f"p_{actual}"])
                top = max(("pass", "run", "punt", "fg"), key=lambda c: st[f"p_{c}"])
                a = agg.setdefault(k + 1, [0, 0.0, 0])
                a[0] += 1
                a[1] += -math.log(p)
                a[2] += top == actual
    return {k: {"n": v[0], "logloss": v[1] / v[0], "top_call_acc": v[2] / v[0]} for k, v in sorted(agg.items()) if v[0]}

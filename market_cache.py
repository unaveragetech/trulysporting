"""One cache for the whole server, shared by every visitor.

Streamlit runs every visitor's session in the same Python process, so a plain module-level store is global: the first
visitor pays for a scoreboard, odds board or price check and everyone else reads it.  Three properties matter:
  * single flight: if ten visitors ask for the same thing at once, one request goes out and the rest wait for it;
  * stale if error: when a feed fails we keep serving the last good copy (marked stale) instead of an empty page;
  * a small JSON snapshot on disk (best effort) so a restarted server starts warm instead of cold.
"""
import json
import os
import tempfile
import threading
import time
from typing import Any, Callable, Dict, Optional, Tuple

_STORE: Dict[str, Tuple[float, Any]] = {}
_LOCKS: Dict[str, threading.Lock] = {}
_GUARD = threading.Lock()
STATS = {'hits': 0, 'misses': 0, 'stale': 0, 'errors': 0}
SNAP = os.path.join(tempfile.gettempdir(), 'trulysporting_market_cache.json')
MAX_STALE_S = 6 * 3600          # never serve a copy older than this, even when the feed is down


def _lock(key: str) -> threading.Lock:
    with _GUARD:
        return _LOCKS.setdefault(key, threading.Lock())


def peek(key: str) -> Optional[Tuple[float, Any]]:
    return _STORE.get(key)


def put(key: str, value: Any) -> None:
    _STORE[key] = (time.time(), value)


def get(key: str, ttl: float, fn: Callable[[], Any], persist: bool = False) -> Tuple[Any, Dict[str, Any]]:
    """Value for ``key`` and a status dict {'age': seconds, 'stale': bool, 'hit': bool}.

    ``fn`` is called at most once at a time per key.  If it raises, the previous value (if any, and not absurdly old) is
    returned with ``stale`` True; with nothing to fall back on the exception propagates.
    """
    hit = _STORE.get(key)
    now = time.time()
    if hit and now - hit[0] < ttl:
        STATS['hits'] += 1
        return hit[1], {'age': now - hit[0], 'stale': False, 'hit': True}
    with _lock(key):
        hit = _STORE.get(key)
        now = time.time()
        if hit and now - hit[0] < ttl:       # someone else refreshed it while we waited
            STATS['hits'] += 1
            return hit[1], {'age': now - hit[0], 'stale': False, 'hit': True}
        STATS['misses'] += 1
        try:
            val = fn()
        except Exception:
            STATS['errors'] += 1
            if hit and now - hit[0] < MAX_STALE_S:
                STATS['stale'] += 1
                return hit[1], {'age': now - hit[0], 'stale': True, 'hit': True}
            raise
        _STORE[key] = (time.time(), val)
        if persist:
            _save()
        return val, {'age': 0.0, 'stale': False, 'hit': False}


def _save() -> None:
    try:
        keep = {k: v for k, v in _STORE.items() if k.startswith('persist:')}
        tmp = SNAP + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(keep, f, default=str)
        os.replace(tmp, SNAP)
    except Exception:
        pass


def load_snapshot() -> int:
    """Warm the store from the last snapshot (a restarted server).  Returns how many entries were loaded."""
    try:
        with open(SNAP, encoding='utf-8') as f:
            data = json.load(f)
    except Exception:
        return 0
    n = 0
    for k, (ts, v) in data.items():
        if time.time() - ts < MAX_STALE_S and k not in _STORE:
            _STORE[k] = (ts, v)
            n += 1
    return n


def clear() -> None:
    _STORE.clear()
    for k in STATS:
        STATS[k] = 0


_WARMER: Dict[str, Any] = {'thread': None}


def start_warmer(tasks: Callable[[], list], interval: float = 60.0) -> bool:
    """Start (once per server) a background thread that refreshes ``tasks()`` (a list of zero-argument callables) every
    ``interval`` seconds, so the first visitor after a quiet spell reads a warm cache instead of waiting on ESPN.
    Also loads the disk snapshot so a restarted server is warm immediately.  Returns True if it started a thread."""
    with _GUARD:
        t = _WARMER['thread']
        if t is not None and t.is_alive():
            return False
        load_snapshot()

        def loop() -> None:
            while True:
                for fn in tasks():
                    try:
                        fn()
                    except Exception:
                        STATS['errors'] += 1
                time.sleep(interval)
        _WARMER['thread'] = threading.Thread(target=loop, name='market-warmer', daemon=True)
        _WARMER['thread'].start()
        return True

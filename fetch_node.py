#!/usr/bin/env python3
"""
fetch_node.py  –  TrulySporting Outbound Fetch Node
====================================================
Run this script on any PC to make it act as an outbound fetch worker.
The node polls the coordinator for pending jobs, fetches the ESPN API,
and posts results back — growing the shared database without any extra
setup on the coordinator machine.

Usage:
    python fetch_node.py
    python fetch_node.py --coordinator http://192.168.1.10:8765
    python fetch_node.py --coordinator http://192.168.1.10:8765 --node-id my-laptop

Environment variables (override defaults / CLI):
    COORDINATOR_URL   e.g.  http://192.168.1.10:8765
    NODE_ID           any descriptive name for this machine

Requirements:
    pip install requests
"""

import argparse
import json
import logging
import os
import socket
import sys
import time
import uuid
from datetime import datetime
from typing import Optional

# ── dependency check ────────────────────────────────────────────────────────
try:
    import requests
    from requests.adapters import HTTPAdapter
    from urllib3.util.retry import Retry
except ImportError:
    print("ERROR: 'requests' is required.  Run:  pip install requests")
    sys.exit(1)

# ── logging ──────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("fetch_node")

# ESPN expects a browser-like User-Agent or it may throttle
ESPN_HEADERS = {
    "User-Agent":      "Mozilla/5.0 (TrulySporting/FetchNode; +https://github.com/trulysporting)",
    "Accept":          "application/json",
    "Accept-Language": "en-US,en;q=0.9",
}

# How long to wait between polls when the queue is empty
IDLE_POLL_SECONDS  = 2.0
# Brief pause between consecutive fetches (be polite to ESPN)
INTER_FETCH_PAUSE  = 0.5
# How long to wait before retrying after a coordinator connection error
CONNECT_RETRY_WAIT = 15
# ESPN fetch timeout (seconds)
ESPN_TIMEOUT       = 25


# ── helpers ──────────────────────────────────────────────────────────────────

def _build_session(retries: int = 2) -> requests.Session:
    """Return a requests Session with a retry adapter for transient errors."""
    session = requests.Session()
    session.headers.update(ESPN_HEADERS)
    retry = Retry(
        total        = retries,
        backoff_factor = 0.5,
        status_forcelist = [429, 500, 502, 503, 504],
        allowed_methods  = ["GET", "POST"],
    )
    adapter = HTTPAdapter(max_retries=retry)
    session.mount("https://", adapter)
    session.mount("http://",  adapter)
    return session


def _default_node_id() -> str:
    """Unique node ID: hostname + short random suffix."""
    host = socket.gethostname().replace(" ", "-").lower()
    rand = uuid.uuid4().hex[:6]
    return f"{host}-{rand}"


# ── core node class ──────────────────────────────────────────────────────────

class FetchNode:
    """
    The fetch node in 3 steps:
        1. GET /jobs/next?node_id=<id>     → receive a job (ESPN URL + params)
        2. Fetch the ESPN URL              → response JSON
        3. POST /jobs/result               → return result to coordinator

    The coordinator parses the JSON and writes it into the shared database.
    """

    def __init__(self, coordinator_url: str, node_id: str,
                 poll_interval: float = IDLE_POLL_SECONDS):
        self.coordinator_url = coordinator_url.rstrip("/")
        self.node_id         = node_id
        self.poll_interval   = poll_interval
        self._session        = _build_session()
        self.jobs_done       = 0
        self.jobs_failed     = 0
        self._running        = False

    # ── coordinator communication ────────────────────────────────────────

    def _coordinator(self, method: str, path: str, **kwargs) -> Optional[dict]:
        url = f"{self.coordinator_url}{path}"
        try:
            resp = self._session.request(method, url, timeout=10, **kwargs)
            resp.raise_for_status()
            return resp.json()
        except requests.exceptions.ConnectionError:
            log.warning("Cannot reach coordinator at %s", self.coordinator_url)
            return None
        except requests.exceptions.HTTPError as exc:
            log.warning("Coordinator HTTP error %s: %s", exc.response.status_code, path)
            return None
        except Exception as exc:
            log.warning("Coordinator request failed: %s", exc)
            return None

    def _poll_for_job(self) -> Optional[dict]:
        result = self._coordinator("GET", f"/jobs/next?node_id={self.node_id}")
        if not result:
            return None
        return result.get("job")

    def _submit_result(self, job_id: int, result_json: Optional[str],
                       success: bool, error: str = ""):
        payload = {
            "job_id":      job_id,
            "node_id":     self.node_id,
            "result_json": result_json,
            "success":     success,
            "error":       error,
        }
        ok = self._coordinator("POST", "/jobs/result", json=payload)
        if not ok:
            log.warning("Could not submit result for job %d — coordinator unreachable", job_id)

    # ── ESPN fetching ────────────────────────────────────────────────────

    def _fetch_espn(self, url: str, params: dict) -> tuple:
        """Fetch an ESPN endpoint.  Returns (result_json_str, success, error_msg)."""
        try:
            resp = self._session.get(url, params=params, timeout=ESPN_TIMEOUT)
            resp.raise_for_status()
            data        = resp.json()
            result_json = json.dumps(data)
            return result_json, True, ""
        except requests.exceptions.HTTPError as exc:
            code  = exc.response.status_code if exc.response is not None else "?"
            error = f"HTTP {code}: {str(exc)[:200]}"
            return None, False, error
        except requests.exceptions.Timeout:
            return None, False, f"Timeout after {ESPN_TIMEOUT}s"
        except Exception as exc:
            return None, False, str(exc)[:500]

    # ── main loop ────────────────────────────────────────────────────────

    def process_one(self) -> bool:
        """Claim and process one job.  Returns True if a job was processed."""
        job = self._poll_for_job()
        if not job:
            return False

        job_id   = job["id"]
        url      = job["url"]
        params   = json.loads(job.get("params_json", "{}"))
        ep_key   = job.get("endpoint_key", "")
        ep_type  = job.get("endpoint_type", "")
        sport_key = job.get("sport_key", "")

        display = f"[Job {job_id}] {sport_key}/{ep_type}  →  {url}"
        if params:
            display += f"  params={params}"
        log.info(display)

        result_json, success, error = self._fetch_espn(url, params)

        if success:
            self.jobs_done += 1
            size = len(result_json) if result_json else 0
            log.info("[Job %d] ✓  %s bytes received", job_id, f"{size:,}")
        else:
            self.jobs_failed += 1
            log.warning("[Job %d] ✗  %s", job_id, error)

        self._submit_result(job_id, result_json, success, error)
        return True

    def run(self):
        """Start the main polling loop (blocks until Ctrl-C)."""
        self._running = True
        start_time    = datetime.now()

        log.info("=" * 55)
        log.info(" TrulySporting Fetch Node")
        log.info("  Node ID:     %s", self.node_id)
        log.info("  Coordinator: %s", self.coordinator_url)
        log.info("  Poll delay:  %.1fs (when idle)", self.poll_interval)
        log.info("  Press Ctrl-C to stop")
        log.info("=" * 55)

        # Verify coordinator is reachable
        health = self._coordinator("GET", "/health")
        if health:
            q  = health.get("queue", {})
            log.info("Coordinator OK — queue: %s", q)
        else:
            log.warning("Coordinator did not respond — will keep retrying…")

        idle_ticks = 0
        while self._running:
            try:
                had_work = self.process_one()
                if had_work:
                    idle_ticks = 0
                    time.sleep(INTER_FETCH_PAUSE)
                else:
                    idle_ticks += 1
                    # Print a status heartbeat every 60 idle polls
                    if idle_ticks % 60 == 0:
                        uptime = str(datetime.now() - start_time).split(".")[0]
                        log.info(
                            "Idle… (uptime=%s  done=%d  failed=%d)",
                            uptime, self.jobs_done, self.jobs_failed,
                        )
                    time.sleep(self.poll_interval)

            except KeyboardInterrupt:
                break
            except Exception as exc:
                log.error("Unexpected error in main loop: %s", exc)
                time.sleep(5)

        log.info("Node stopped.  done=%d  failed=%d", self.jobs_done, self.jobs_failed)

    def stop(self):
        self._running = False


# ── CLI entry point ──────────────────────────────────────────────────────────

def main():
    default_coordinator = os.environ.get("COORDINATOR_URL", "http://localhost:8765")
    default_node_id     = os.environ.get("NODE_ID",         _default_node_id())

    parser = argparse.ArgumentParser(
        description="TrulySporting Fetch Node — connects to the coordinator and fetches ESPN data",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python fetch_node.py
  python fetch_node.py --coordinator http://192.168.1.5:8765
  python fetch_node.py --coordinator http://192.168.1.5:8765 --node-id gaming-pc
  NODE_ID=my-pi COORDINATOR_URL=http://192.168.1.5:8765 python fetch_node.py
        """,
    )
    parser.add_argument(
        "--coordinator",
        default=default_coordinator,
        metavar="URL",
        help=f"Coordinator URL  (default: {default_coordinator})",
    )
    parser.add_argument(
        "--node-id",
        default=default_node_id,
        metavar="ID",
        help=f"Descriptive node name  (default: {default_node_id})",
    )
    parser.add_argument(
        "--poll-interval",
        type=float,
        default=IDLE_POLL_SECONDS,
        metavar="SECS",
        help=f"Seconds to wait between polls when the queue is empty  (default: {IDLE_POLL_SECONDS})",
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Show DEBUG-level log messages",
    )
    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    node = FetchNode(
        coordinator_url = args.coordinator,
        node_id         = args.node_id,
        poll_interval   = args.poll_interval,
    )
    node.run()


if __name__ == "__main__":
    main()

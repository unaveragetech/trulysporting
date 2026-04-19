#!/usr/bin/env python3
"""
coordinator.py  –  TrulySporting Distributed Fetch Coordinator
===============================================================
Pure-Python HTTP server (stdlib only) that manages a distributed job queue for
ESPN data fetching.  Any PC on the LAN can run fetch_node.py to act as an
outbound fetch node.

Usage:
    python coordinator.py [--host 0.0.0.0] [--port 8765] [--db espn_deep_analytics.db]

API endpoints:
    GET  /health                      – Server health & queue stats
    GET  /queue/status                – Full queue status breakdown
    GET  /jobs/next?node_id=<id>      – Atomically claim next pending job
    GET  /jobs/list?status=&limit=50  – List recent jobs
    POST /jobs/result                 – Submit a completed job result
    POST /jobs/dispatch               – Add a single job manually
    POST /jobs/dispatch_all           – Enqueue all jobs for active leagues
    POST /jobs/clear                  – Delete done/failed jobs (cleanup)

The coordinator shares the same SQLite database as sporting.py
(espn_deep_analytics.db), so results are immediately visible in the UI.
"""

import argparse
import json
import logging
import sqlite3
import threading
import time
import urllib.parse
from datetime import datetime
from http.server import BaseHTTPRequestHandler
from socketserver import ThreadingMixIn, TCPServer
from typing import Dict, List, Optional

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("coordinator")

# ── ESPN endpoint catalogue ──────────────────────────────────────────────────

BASE_URL = "https://site.api.espn.com/apis/site/v2/sports"

LEAGUE_ENDPOINTS: Dict[str, List[str]] = {
    "football/college-football": ["scoreboard", "teams", "news", "rankings"],
    "football/nfl":              ["scoreboard", "teams", "news"],
    "baseball/mlb":              ["scoreboard", "teams", "news"],
    "hockey/nhl":                ["scoreboard", "teams", "news"],
    "basketball/nba":            ["scoreboard", "teams", "news"],
    "basketball/wnba":           ["scoreboard", "teams", "news"],
    "basketball/mens-college-basketball":    ["scoreboard", "teams", "news", "rankings"],
    "basketball/womens-college-basketball":  ["scoreboard", "teams", "news"],
    "soccer/eng.1": ["scoreboard", "teams", "news"],
    "soccer/usa.1": ["scoreboard", "teams", "news"],
}

# job priorities (lower = higher priority)
EP_PRIORITY = {"scoreboard": 1, "news": 2, "summary": 2, "rankings": 3,
               "team_detail": 4, "teams": 5}
# how long (seconds) a result stays fresh before the job can be re-queued
EP_TTL = {"scoreboard": 60, "news": 3600, "summary": 0,   # 0 = never re-queue (final games)
          "rankings": 86400, "team_detail": 604800, "teams": 86400}


def _make_espn_url(category: str, sport: str, endpoint_type: str) -> str:
    return f"{BASE_URL}/{category}/{sport}/{endpoint_type}"


# ── ESPN response parsers (no Streamlit dependency) ─────────────────────────

class ESPNParser:
    """Minimal ESPN response parsers shared with the coordinator."""

    @staticmethod
    def parse_scoreboard(data: Dict, category: str, sport: str) -> List[Dict]:
        games = []
        events = data.get("events", [])
        if not events:
            events = data.get("season", {}).get("events", [])
        for event in events:
            try:
                comp = event["competitions"][0]
                competitors = comp["competitors"]
                home = next((c for c in competitors if c.get("homeAway") == "home"), competitors[0])
                away = next((c for c in competitors if c.get("homeAway") == "away"), competitors[1])

                home_periods = [ls.get("displayValue", "") for ls in home.get("linescores", [])]
                away_periods = [ls.get("displayValue", "") for ls in away.get("linescores", [])]
                home_stats  = {s["name"]: s["displayValue"] for s in home.get("statistics", [])}
                away_stats  = {s["name"]: s["displayValue"] for s in away.get("statistics", [])}
                home_record = next((r["summary"] for r in home.get("records", []) if r.get("type") == "total"), "")
                away_record = next((r["summary"] for r in away.get("records", []) if r.get("type") == "total"), "")

                leaders = {}
                for lg in comp.get("leaders", []):
                    ls = lg.get("leaders", [])
                    if ls:
                        top = ls[0]
                        leaders[lg.get("name", "")] = {
                            "athlete": top["athlete"]["displayName"],
                            "value":   top.get("displayValue", ""),
                        }

                headline_text = comp["headlines"][0].get("description", "") if comp.get("headlines") else ""
                venue = comp.get("venue", {})
                note  = comp["notes"][0].get("headline", "") if comp.get("notes") else ""
                status_type = event.get("status", {}).get("type", {})

                event_links: Dict[str, str] = {}
                for link in event.get("links", []):
                    rels = link.get("rel", [])
                    if "boxscore" in rels:  event_links["boxscore"] = link["href"]
                    elif "recap"  in rels:  event_links["recap"]    = link["href"]
                    elif "summary" in rels: event_links["summary"]  = link["href"]
                    elif "pbp"    in rels:  event_links["pbp"]      = link["href"]

                games.append({
                    "event_id":     event["id"],
                    "date":         event["date"][:10],
                    "name":         event.get("name", ""),
                    "home_team":    home.get("team", {}).get("displayName", ""),
                    "home_abbr":    home.get("team", {}).get("abbreviation", ""),
                    "home_color":   home.get("team", {}).get("color", ""),
                    "home_logo":    home.get("team", {}).get("logo", ""),
                    "away_team":    away.get("team", {}).get("displayName", ""),
                    "away_abbr":    away.get("team", {}).get("abbreviation", ""),
                    "away_color":   away.get("team", {}).get("color", ""),
                    "away_logo":    away.get("team", {}).get("logo", ""),
                    "home_score":   float(home.get("score") or 0),
                    "away_score":   float(away.get("score") or 0),
                    "home_record":  home_record,
                    "away_record":  away_record,
                    "home_winner":  bool(home.get("winner", False)),
                    "status":       status_type.get("name", ""),
                    "status_detail": status_type.get("detail", ""),
                    "period":       event.get("status", {}).get("period", 0),
                    "clock":        event.get("status", {}).get("displayClock", ""),
                    "home_periods": json.dumps(home_periods),
                    "away_periods": json.dumps(away_periods),
                    "home_stats":   json.dumps(home_stats),
                    "away_stats":   json.dumps(away_stats),
                    "leaders":      json.dumps(leaders),
                    "headline":     headline_text,
                    "venue":        venue.get("fullName", ""),
                    "venue_city":   venue.get("address", {}).get("city", ""),
                    "attendance":   comp.get("attendance", 0),
                    "broadcast":    comp.get("broadcast", ""),
                    "note":         note,
                    "links":        json.dumps(event_links),
                    "category":     category,
                    "sport":        sport,
                })
            except Exception:
                continue
        return games

    @staticmethod
    def parse_teams(data: Dict, sport_key: str) -> List[Dict]:
        teams = []
        try:
            for team_obj in data["sports"][0]["leagues"][0]["teams"]:
                ti = team_obj["team"]
                logo_url = next(
                    (lg["href"] for lg in ti.get("logos", [])
                     if "full" in lg.get("rel", []) and "default" in lg.get("rel", [])),
                    ""
                )
                teams.append({
                    "sport_key":       sport_key,
                    "team_id":         ti.get("id", ""),
                    "team_name":       ti.get("displayName", ""),
                    "team_abbr":       ti.get("abbreviation", ""),
                    "team_slug":       ti.get("slug", ""),
                    "color":           ti.get("color", ""),
                    "alternate_color": ti.get("alternateColor", ""),
                    "logo_url":        logo_url,
                    "fetched_at":      datetime.now().isoformat(),
                })
        except Exception as exc:
            log.warning("parse_teams error: %s", exc)
        return teams

    @staticmethod
    def parse_news(data: Dict) -> List[Dict]:
        articles = []
        for art in data.get("articles", []):
            image_url = ""
            for img in art.get("images", []):
                if not image_url:
                    image_url = img.get("url", "")
                if img.get("type") == "header":
                    image_url = img.get("url", "")
                    break
            athletes = [c["description"] for c in art.get("categories", []) if c.get("type") == "athlete"]
            teams    = [c["description"] for c in art.get("categories", []) if c.get("type") == "team"]
            articles.append({
                "headline":      art.get("headline", ""),
                "description":   art.get("description", ""),
                "published":     art.get("published", ""),
                "last_modified": art.get("lastModified", ""),
                "link":          art.get("links", {}).get("web", {}).get("href", ""),
                "image":         image_url,
                "type":          art.get("type", ""),
                "byline":        art.get("byline", ""),
                "athletes":      json.dumps(athletes),
                "teams":         json.dumps(teams),
            })
        return articles

    @staticmethod
    def parse_rankings(data: Dict) -> List[Dict]:
        out = []
        for poll in data.get("rankings", []):
            poll_name   = poll.get("name", "Unknown Poll")
            season_type = poll.get("seasonType", {}).get("name", "")
            for ri in poll.get("ranks", []):
                ti = ri.get("team", {})
                rec_items = ti.get("record", {}).get("items", [])
                record = rec_items[0].get("summary", "") if rec_items else ""
                out.append({
                    "poll":              poll_name,
                    "season_type":       season_type,
                    "rank":              ri.get("current", 0),
                    "previous":          ri.get("previous", 0),
                    "team":              ti.get("displayName", ""),
                    "team_abbr":         ti.get("abbreviation", ""),
                    "record":            record,
                    "points":            ri.get("points", 0),
                    "first_place_votes": ri.get("firstPlaceVotes", 0),
                })
        return out

    @staticmethod
    def parse_team_detail(data: Dict, sport_key: str) -> Optional[Dict]:
        """Parse /teams/:abbr single-team response."""
        try:
            team = data["team"]
            records: Dict[str, Dict] = {}
            for item in team.get("record", {}).get("items", []):
                rec_type = item.get("type", "total")
                stats_dict = {s["name"]: s.get("value", s.get("displayValue", ""))
                              for s in item.get("stats", [])}
                stats_dict["summary"] = item.get("summary", "")
                records[rec_type] = stats_dict

            venue_data = team.get("franchise", {}).get("venue", {})
            logo_url = next(
                (lg["href"] for lg in team.get("logos", [])
                 if "full" in lg.get("rel", []) and "default" in lg.get("rel", [])),
                ""
            )
            return {
                "sport_key":        sport_key,
                "team_id":          team.get("id", ""),
                "team_abbr":        team.get("abbreviation", ""),
                "team_slug":        team.get("slug", ""),
                "team_name":        team.get("displayName", ""),
                "color":            team.get("color", ""),
                "alternate_color":  team.get("alternateColor", ""),
                "logo_url":         logo_url,
                "records_json":     json.dumps(records),
                "standing_summary": team.get("standingSummary", ""),
                "venue_name":       venue_data.get("fullName", ""),
                "venue_city":       venue_data.get("address", {}).get("city", ""),
                "venue_state":      venue_data.get("address", {}).get("state", ""),
                "venue_grass":      int(bool(venue_data.get("grass", False))),
                "venue_indoor":     int(bool(venue_data.get("indoor", False))),
                "next_event_json":  json.dumps(team.get("nextEvent", [])),
                "fetched_at":       datetime.now().isoformat(),
            }
        except Exception as exc:
            log.warning("parse_team_detail error: %s", exc)
            return None

    @staticmethod
    def parse_game_summary(data: Dict, sport_key: str) -> Optional[Dict]:
        """Parse /summary?event=X response for box score, injuries, last-5 games."""
        try:
            header = data.get("header", {})
            comps  = header.get("competitions", [])
            if not comps:
                return None
            event_id = comps[0].get("id", "")
            if not event_id:
                return None

            # Per-team aggregate stats (season averages / game totals)
            home_stats: Dict = {}
            away_stats: Dict = {}
            for t in data.get("boxscore", {}).get("teams", []):
                stats = {s["name"]: s.get("displayValue", "") for s in t.get("statistics", [])}
                if t.get("homeAway") == "home":
                    home_stats = stats
                else:
                    away_stats = stats

            # Statistical leaders
            leaders_data = []
            for team_leaders in data.get("leaders", []):
                team_id = team_leaders.get("team", {}).get("id", "")
                for cat in team_leaders.get("leaders", []):
                    for ldr in cat.get("leaders", []):
                        leaders_data.append({
                            "team_id": team_id,
                            "stat":    cat.get("displayName", ""),
                            "athlete": ldr.get("athlete", {}).get("displayName", ""),
                            "value":   ldr.get("displayValue", ""),
                        })

            # Last-5 game results per team
            home_id = next(
                (cp["team"]["id"] for cp in comps[0].get("competitors", [])
                 if cp.get("homeAway") == "home"), ""
            )
            last_five_home: List[Dict] = []
            last_five_away: List[Dict] = []
            for entry in data.get("lastFiveGames", []):
                team_id = entry.get("team", {}).get("id", "")
                games_list = [
                    {"id": e["id"], "result": e.get("gameResult", ""),
                     "score": e.get("score", ""), "date": e.get("gameDate", "")[:10]}
                    for e in entry.get("events", [])
                ]
                if team_id == home_id:
                    last_five_home = games_list
                else:
                    last_five_away = games_list

            # Injuries
            injuries_data = []
            for team_inj in data.get("injuries", []):
                team_id = team_inj.get("team", {}).get("id", "")
                for inj in team_inj.get("injuries", []):
                    injuries_data.append({
                        "team_id": team_id,
                        "athlete": inj.get("athlete", {}).get("displayName", ""),
                        "status":  inj.get("status", ""),
                        "type":    inj.get("type", {}).get("description", ""),
                        "detail":  inj.get("details", {}).get("detail", ""),
                        "return":  inj.get("details", {}).get("returnDate", ""),
                    })

            # Betting odds
            odds_data: Dict = {}
            pickcenter = data.get("pickcenter", [])
            if pickcenter:
                pc = pickcenter[0]
                odds_data = {
                    "home_ml":     pc.get("homeTeamOdds", {}).get("moneyLine", ""),
                    "away_ml":     pc.get("awayTeamOdds", {}).get("moneyLine", ""),
                    "spread":      pc.get("spread", ""),
                    "over_under":  pc.get("overUnder", ""),
                    "provider":    pc.get("provider", {}).get("name", ""),
                }

            venue = data.get("gameInfo", {}).get("venue", {})
            return {
                "event_id":        event_id,
                "sport_key":       sport_key,
                "home_stats_json": json.dumps(home_stats),
                "away_stats_json": json.dumps(away_stats),
                "leaders_json":    json.dumps(leaders_data),
                "last_five_home":  json.dumps(last_five_home),
                "last_five_away":  json.dumps(last_five_away),
                "injuries_json":   json.dumps(injuries_data),
                "standings_json":  json.dumps(data.get("standings", {})),
                "venue_name":      venue.get("fullName", ""),
                "venue_city":      venue.get("address", {}).get("city", ""),
                "odds_json":       json.dumps(odds_data),
                "fetched_at":      datetime.now().isoformat(),
            }
        except Exception as exc:
            log.warning("parse_game_summary error: %s", exc)
            return None


# ── Database manager ─────────────────────────────────────────────────────────

class CoordinatorDB:
    """
    Manages all coordinator state (jobs, nodes) plus writes parsed ESPN data
    into the same tables that sporting.py reads from.
    """

    def __init__(self, db_path: str = "espn_deep_analytics.db"):
        self.db_path = db_path
        self._lock   = threading.Lock()
        self._init_tables()

    # ── low-level connection ──

    def _conn(self) -> sqlite3.Connection:
        c = sqlite3.connect(self.db_path, timeout=30)
        c.row_factory = sqlite3.Row
        c.execute("PRAGMA journal_mode=WAL")
        c.execute("PRAGMA synchronous=NORMAL")
        return c

    # ── schema initialization ─────────────────────────────────────────────

    def _init_tables(self):
        with self._conn() as c:
            c.executescript("""
                -- Distributed job queue
                CREATE TABLE IF NOT EXISTS jobs (
                    id            INTEGER PRIMARY KEY AUTOINCREMENT,
                    endpoint_key  TEXT NOT NULL,
                    url           TEXT NOT NULL,
                    params_json   TEXT    DEFAULT '{}',
                    status        TEXT    DEFAULT 'pending',
                    sport_key     TEXT,
                    endpoint_type TEXT,
                    category      TEXT,
                    sport         TEXT,
                    priority      INTEGER DEFAULT 5,
                    node_id       TEXT,
                    created_at    TEXT    DEFAULT (datetime('now')),
                    claimed_at    TEXT,
                    completed_at  TEXT,
                    result_json   TEXT,
                    error         TEXT,
                    ttl_seconds   INTEGER DEFAULT 3600
                );

                -- Worker node registry
                CREATE TABLE IF NOT EXISTS nodes (
                    node_id         TEXT PRIMARY KEY,
                    ip              TEXT,
                    last_seen       TEXT,
                    jobs_completed  INTEGER DEFAULT 0,
                    jobs_failed     INTEGER DEFAULT 0,
                    version         TEXT    DEFAULT '1.0'
                );

                -- Extended single-team data (/teams/:abbr)
                CREATE TABLE IF NOT EXISTS team_detail (
                    id               INTEGER PRIMARY KEY AUTOINCREMENT,
                    sport_key        TEXT,
                    team_id          TEXT,
                    team_abbr        TEXT,
                    team_slug        TEXT,
                    team_name        TEXT,
                    color            TEXT,
                    alternate_color  TEXT,
                    logo_url         TEXT,
                    records_json     TEXT,
                    standing_summary TEXT,
                    venue_name       TEXT,
                    venue_city       TEXT,
                    venue_state      TEXT,
                    venue_grass      INTEGER DEFAULT 0,
                    venue_indoor     INTEGER DEFAULT 0,
                    next_event_json  TEXT,
                    fetched_at       TEXT,
                    UNIQUE(sport_key, team_id)
                );

                -- Per-game summaries (/summary?event=X)
                CREATE TABLE IF NOT EXISTS game_summaries (
                    id               INTEGER PRIMARY KEY AUTOINCREMENT,
                    event_id         TEXT UNIQUE,
                    sport_key        TEXT,
                    home_stats_json  TEXT,
                    away_stats_json  TEXT,
                    leaders_json     TEXT,
                    last_five_home   TEXT,
                    last_five_away   TEXT,
                    injuries_json    TEXT,
                    standings_json   TEXT,
                    venue_name       TEXT,
                    venue_city       TEXT,
                    odds_json        TEXT,
                    fetched_at       TEXT
                );

                -- Game history (written by coordinator AND sporting.py)
                CREATE TABLE IF NOT EXISTS game_history (
                    id              INTEGER PRIMARY KEY AUTOINCREMENT,
                    event_id        TEXT UNIQUE,
                    category        TEXT,
                    sport           TEXT,
                    event_date      TEXT,
                    name            TEXT,
                    home_team       TEXT,
                    home_abbr       TEXT,
                    home_color      TEXT,
                    home_logo       TEXT,
                    away_team       TEXT,
                    away_abbr       TEXT,
                    away_color      TEXT,
                    away_logo       TEXT,
                    home_score      REAL,
                    away_score      REAL,
                    home_record     TEXT,
                    away_record     TEXT,
                    home_winner     INTEGER,
                    status          TEXT,
                    status_detail   TEXT,
                    period          INTEGER,
                    clock           TEXT,
                    home_periods    TEXT,
                    away_periods    TEXT,
                    home_stats      TEXT,
                    away_stats      TEXT,
                    leaders_json    TEXT,
                    headline        TEXT,
                    venue           TEXT,
                    venue_city      TEXT,
                    attendance      INTEGER,
                    broadcast       TEXT,
                    note            TEXT,
                    links_json      TEXT,
                    created_at      TEXT DEFAULT (datetime('now'))
                );

                CREATE TABLE IF NOT EXISTS teams_registry (
                    id               INTEGER PRIMARY KEY AUTOINCREMENT,
                    sport_key        TEXT,
                    team_id          TEXT,
                    team_name        TEXT,
                    team_abbr        TEXT,
                    team_slug        TEXT,
                    color            TEXT,
                    alternate_color  TEXT,
                    logo_url         TEXT,
                    fetched_at       TEXT,
                    UNIQUE(sport_key, team_id)
                );

                CREATE TABLE IF NOT EXISTS news_archive (
                    id           INTEGER PRIMARY KEY AUTOINCREMENT,
                    sport_key    TEXT,
                    headline     TEXT,
                    link         TEXT UNIQUE,
                    published    TEXT,
                    last_modified TEXT,
                    description  TEXT,
                    image_url    TEXT,
                    article_type TEXT,
                    byline       TEXT,
                    athletes     TEXT,
                    teams        TEXT
                );

                CREATE TABLE IF NOT EXISTS rankings (
                    id                INTEGER PRIMARY KEY AUTOINCREMENT,
                    sport_key         TEXT,
                    poll              TEXT,
                    season_type       TEXT,
                    rank              INTEGER,
                    previous_rank     INTEGER,
                    team              TEXT,
                    team_abbr         TEXT,
                    record            TEXT,
                    points            REAL,
                    first_place_votes INTEGER,
                    fetched_at        TEXT,
                    UNIQUE(sport_key, poll, team)
                );

                CREATE TABLE IF NOT EXISTS api_cache (
                    endpoint_key  TEXT PRIMARY KEY,
                    response_json TEXT,
                    fetched_at    TEXT DEFAULT (datetime('now'))
                );

                CREATE TABLE IF NOT EXISTS config (
                    key   TEXT PRIMARY KEY,
                    value TEXT
                );
                INSERT OR IGNORE INTO config VALUES ('default_refresh_interval', '3600');
                INSERT OR IGNORE INTO config VALUES ('active_endpoints',
                    '["football/nfl","basketball/nba"]');
            """)

    # ── job queue operations ─────────────────────────────────────────────

    def claim_next_job(self, node_id: str, ip: str) -> Optional[Dict]:
        """Atomically grab the next pending job for a node."""
        with self._lock:
            with self._conn() as c:
                row = c.execute("""
                    SELECT id, endpoint_key, url, params_json,
                           sport_key, endpoint_type, category, sport, ttl_seconds
                    FROM   jobs
                    WHERE  status = 'pending'
                    ORDER  BY priority ASC, id ASC
                    LIMIT  1
                """).fetchone()
                if not row:
                    return None
                c.execute("""
                    UPDATE jobs
                    SET    status='claimed', node_id=?, claimed_at=datetime('now')
                    WHERE  id=? AND status='pending'
                """, (node_id, row["id"]))
                c.execute("""
                    INSERT INTO nodes (node_id, ip, last_seen)
                    VALUES (?, ?, datetime('now'))
                    ON CONFLICT(node_id) DO UPDATE
                    SET ip=excluded.ip, last_seen=excluded.last_seen
                """, (node_id, ip))
                return dict(row)

    def submit_result(self, job_id: int, node_id: str,
                      result_json: Optional[str], success: bool,
                      error: str = "") -> bool:
        status = "done" if success else "failed"
        with self._conn() as c:
            job = c.execute(
                "SELECT sport_key, endpoint_type, category, sport FROM jobs WHERE id=?",
                (job_id,)
            ).fetchone()
            if not job:
                return False

            c.execute("""
                UPDATE jobs
                SET status=?, completed_at=datetime('now'), result_json=?, error=?, node_id=?
                WHERE id=?
            """, (status, result_json, error, node_id, job_id))

            if success and result_json:
                self._process_result(c, job, result_json)

            col = "jobs_completed" if success else "jobs_failed"
            c.execute(f"UPDATE nodes SET {col}={col}+1, last_seen=datetime('now') WHERE node_id=?",
                      (node_id,))
        return True

    def _process_result(self, c: sqlite3.Connection, job: sqlite3.Row, result_json: str):
        """Parse ESPN JSON and write into the appropriate data tables."""
        try:
            data      = json.loads(result_json)
            sport_key = job["sport_key"] or ""
            ep_type   = job["endpoint_type"] or ""
            category  = job["category"] or ""
            sport_    = job["sport"] or ""

            if ep_type == "scoreboard":
                for g in ESPNParser.parse_scoreboard(data, category, sport_):
                    c.execute("""
                        INSERT OR REPLACE INTO game_history
                        (event_id, category, sport, event_date, name,
                         home_team, home_abbr, home_color, home_logo,
                         away_team, away_abbr, away_color, away_logo,
                         home_score, away_score, home_record, away_record, home_winner,
                         status, status_detail, period, clock,
                         home_periods, away_periods, home_stats, away_stats,
                         leaders_json, headline, venue, venue_city,
                         attendance, broadcast, note, links_json)
                        VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,
                                ?,?,?,?,?,?,?,?)
                    """, (
                        g["event_id"], g["category"], g["sport"], g["date"], g["name"],
                        g["home_team"], g["home_abbr"], g["home_color"], g["home_logo"],
                        g["away_team"], g["away_abbr"], g["away_color"], g["away_logo"],
                        g["home_score"], g["away_score"], g["home_record"], g["away_record"],
                        int(g["home_winner"]), g["status"], g["status_detail"],
                        g["period"], g["clock"], g["home_periods"], g["away_periods"],
                        g["home_stats"], g["away_stats"], g["leaders"], g["headline"],
                        g["venue"], g["venue_city"], g["attendance"], g["broadcast"],
                        g["note"], g["links"],
                    ))

            elif ep_type == "teams":
                for t in ESPNParser.parse_teams(data, sport_key):
                    c.execute("""
                        INSERT OR REPLACE INTO teams_registry
                        (sport_key, team_id, team_name, team_abbr, team_slug,
                         color, alternate_color, logo_url, fetched_at)
                        VALUES (?,?,?,?,?,?,?,?,?)
                    """, (t["sport_key"], t["team_id"], t["team_name"], t["team_abbr"],
                          t["team_slug"], t["color"], t["alternate_color"],
                          t["logo_url"], t["fetched_at"]))

            elif ep_type == "news":
                for a in ESPNParser.parse_news(data):
                    if not a.get("link"):
                        continue
                    c.execute("""
                        INSERT OR IGNORE INTO news_archive
                        (sport_key, headline, link, published, last_modified,
                         description, image_url, article_type, byline, athletes, teams)
                        VALUES (?,?,?,?,?,?,?,?,?,?,?)
                    """, (sport_key, a["headline"], a["link"], a["published"],
                          a.get("last_modified", ""), a["description"], a.get("image", ""),
                          a.get("type", ""), a.get("byline", ""),
                          a.get("athletes", "[]"), a.get("teams", "[]")))

            elif ep_type == "rankings":
                for r in ESPNParser.parse_rankings(data):
                    c.execute("""
                        INSERT OR REPLACE INTO rankings
                        (sport_key, poll, season_type, rank, previous_rank,
                         team, team_abbr, record, points, first_place_votes, fetched_at)
                        VALUES (?,?,?,?,?,?,?,?,?,?,?)
                    """, (sport_key, r["poll"], r.get("season_type", ""), r["rank"],
                          r.get("previous", 0), r["team"], r.get("team_abbr", ""),
                          r.get("record", ""), r.get("points", 0),
                          r.get("first_place_votes", 0), datetime.now().isoformat()))

            elif ep_type == "team_detail":
                detail = ESPNParser.parse_team_detail(data, sport_key)
                if detail:
                    c.execute("""
                        INSERT OR REPLACE INTO team_detail
                        (sport_key, team_id, team_abbr, team_slug, team_name,
                         color, alternate_color, logo_url, records_json, standing_summary,
                         venue_name, venue_city, venue_state, venue_grass, venue_indoor,
                         next_event_json, fetched_at)
                        VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                    """, (detail["sport_key"], detail["team_id"], detail["team_abbr"],
                          detail["team_slug"], detail["team_name"], detail["color"],
                          detail["alternate_color"], detail["logo_url"], detail["records_json"],
                          detail["standing_summary"], detail["venue_name"], detail["venue_city"],
                          detail["venue_state"], detail["venue_grass"], detail["venue_indoor"],
                          detail["next_event_json"], detail["fetched_at"]))

            elif ep_type == "summary":
                summary = ESPNParser.parse_game_summary(data, sport_key)
                if summary:
                    c.execute("""
                        INSERT OR REPLACE INTO game_summaries
                        (event_id, sport_key, home_stats_json, away_stats_json, leaders_json,
                         last_five_home, last_five_away, injuries_json, standings_json,
                         venue_name, venue_city, odds_json, fetched_at)
                        VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)
                    """, (summary["event_id"], summary["sport_key"],
                          summary["home_stats_json"], summary["away_stats_json"],
                          summary["leaders_json"], summary["last_five_home"],
                          summary["last_five_away"], summary["injuries_json"],
                          summary["standings_json"], summary["venue_name"],
                          summary["venue_city"], summary["odds_json"], summary["fetched_at"]))

        except Exception as exc:
            log.error("_process_result error: %s", exc)

    # ── job management helpers ───────────────────────────────────────────

    def add_job(self, endpoint_key: str, url: str, params: Dict,
                sport_key: str, endpoint_type: str, category: str, sport: str,
                priority: int = 5, ttl: int = 3600) -> int:
        with self._conn() as c:
            cur = c.execute("""
                INSERT INTO jobs (endpoint_key, url, params_json, status, sport_key,
                    endpoint_type, category, sport, priority, ttl_seconds)
                VALUES (?,?,?,'pending',?,?,?,?,?,?)
            """, (endpoint_key, url, json.dumps(params), sport_key, endpoint_type,
                  category, sport, priority, ttl))
            return cur.lastrowid

    def dispatch_all(self, endpoints: List[str]) -> int:
        """Enqueue standard jobs for a list of 'category/sport' strings."""
        today = datetime.now().strftime("%Y%m%d")
        count = 0
        for ep in endpoints:
            parts = ep.split("/")
            if len(parts) != 2:
                continue
            category, sport = parts
            ep_list = LEAGUE_ENDPOINTS.get(ep, ["scoreboard", "teams", "news"])
            for ep_type in ep_list:
                url    = _make_espn_url(category, sport, ep_type)
                params = {"dates": today} if ep_type == "scoreboard" else {}
                key    = f"{category}_{sport}_{ep_type}"
                if ep_type == "scoreboard":
                    key += f"_{today}"
                prio = EP_PRIORITY.get(ep_type, 5)
                ttl  = EP_TTL.get(ep_type, 3600)
                self.add_job(key, url, params, ep, ep_type, category, sport, prio, ttl)
                count += 1
        return count

    def get_queue_status(self) -> Dict:
        with self._conn() as c:
            rows  = c.execute("SELECT status, COUNT(*) cnt FROM jobs GROUP BY status").fetchall()
            nodes = c.execute("SELECT node_id, ip, last_seen, jobs_completed, jobs_failed "
                              "FROM nodes ORDER BY last_seen DESC").fetchall()
        return {
            "queue": {r["status"]: r["cnt"] for r in rows},
            "total": sum(r["cnt"] for r in rows),
            "nodes": [dict(n) for n in nodes],
        }

    def get_active_endpoints(self) -> List[str]:
        with self._conn() as c:
            row = c.execute("SELECT value FROM config WHERE key='active_endpoints'").fetchone()
        if row:
            try:
                return json.loads(row["value"])
            except Exception:
                pass
        return ["football/nfl", "basketball/nba"]


# ── HTTP request handler ─────────────────────────────────────────────────────

class CoordinatorHandler(BaseHTTPRequestHandler):
    db: CoordinatorDB  # injected before use

    def log_message(self, fmt, *args):          # redirect to Python logging
        log.debug("%s – %s", self.address_string(), fmt % args)

    def _send_json(self, data: object, status: int = 200):
        body = json.dumps(data, indent=2, default=str).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _read_body(self) -> Optional[Dict]:
        length = int(self.headers.get("Content-Length", 0))
        if length > 0:
            raw = self.rfile.read(length)
            try:
                return json.loads(raw)
            except Exception:
                return None
        return {}

    def _client_ip(self) -> str:
        xff = self.headers.get("X-Forwarded-For", "")
        return xff.split(",")[0].strip() if xff else self.client_address[0]

    # ── GET ──────────────────────────────────────────────────────────────

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        path   = parsed.path
        qs     = urllib.parse.parse_qs(parsed.query)

        if path == "/health":
            status = self.db.get_queue_status()
            self._send_json({"status": "ok", "time": datetime.now().isoformat(), **status})

        elif path == "/queue/status":
            self._send_json(self.db.get_queue_status())

        elif path == "/jobs/next":
            node_id = qs.get("node_id", ["unknown"])[0]
            job     = self.db.claim_next_job(node_id, self._client_ip())
            if job:
                log.info("Job %s claimed by %s (%s)", job["id"], node_id, job["endpoint_key"])
            self._send_json({"job": job, "message": "" if job else "No pending jobs"})

        elif path == "/jobs/list":
            limit  = int(qs.get("limit",  [50])[0])
            status = qs.get("status", [None])[0]
            with self.db._conn() as c:
                if status:
                    rows = c.execute(
                        "SELECT id, endpoint_key, status, sport_key, endpoint_type, "
                        "created_at, claimed_at, completed_at, node_id, error "
                        "FROM jobs WHERE status=? ORDER BY id DESC LIMIT ?",
                        (status, limit)).fetchall()
                else:
                    rows = c.execute(
                        "SELECT id, endpoint_key, status, sport_key, endpoint_type, "
                        "created_at, claimed_at, completed_at, node_id, error "
                        "FROM jobs ORDER BY id DESC LIMIT ?",
                        (limit,)).fetchall()
            self._send_json({"jobs": [dict(r) for r in rows]})

        else:
            self._send_json({"error": "Not found"}, 404)

    # ── POST ─────────────────────────────────────────────────────────────

    def do_POST(self):
        parsed = urllib.parse.urlparse(self.path)
        path   = parsed.path
        body   = self._read_body()

        if path == "/jobs/result":
            if not body:
                return self._send_json({"error": "Empty body"}, 400)
            job_id      = body.get("job_id")
            node_id     = body.get("node_id", "unknown")
            result_json = body.get("result_json")
            success     = bool(body.get("success", False))
            error       = body.get("error", "")
            ok = self.db.submit_result(job_id, node_id, result_json, success, error)
            if ok:
                log.info("Job %s %s from %s", job_id, "OK" if success else "FAIL", node_id)
                self._send_json({"status": "accepted"})
            else:
                self._send_json({"error": f"Job {job_id} not found"}, 404)

        elif path == "/jobs/dispatch":
            if not body:
                return self._send_json({"error": "Empty body"}, 400)
            job_id = self.db.add_job(
                endpoint_key  = body.get("endpoint_key", ""),
                url           = body.get("url", ""),
                params        = body.get("params", {}),
                sport_key     = body.get("sport_key", ""),
                endpoint_type = body.get("endpoint_type", ""),
                category      = body.get("category", ""),
                sport         = body.get("sport", ""),
                priority      = int(body.get("priority", 5)),
                ttl           = int(body.get("ttl", 3600)),
            )
            self._send_json({"status": "queued", "job_id": job_id})

        elif path == "/jobs/dispatch_all":
            endpoints = (body or {}).get("endpoints") or self.db.get_active_endpoints()
            count     = self.db.dispatch_all(endpoints)
            log.info("Dispatched %d jobs for %d leagues", count, len(endpoints))
            self._send_json({"status": "ok", "jobs_queued": count, "leagues": endpoints})

        elif path == "/jobs/clear":
            status_filter = (body or {}).get("status", "done")
            # Safety: only allow clearing terminal states
            if status_filter not in ("done", "failed"):
                return self._send_json({"error": "Only 'done' or 'failed' can be cleared"}, 400)
            with self.db._conn() as c:
                cur     = c.execute("DELETE FROM jobs WHERE status=?", (status_filter,))
                deleted = cur.rowcount
            self._send_json({"deleted": deleted, "status": status_filter})

        else:
            self._send_json({"error": "Not found"}, 404)


# ── Threaded HTTP server ─────────────────────────────────────────────────────

class ThreadingHTTPServer(ThreadingMixIn, TCPServer):
    allow_reuse_address = True
    daemon_threads      = True


# ── Auto-dispatch scheduler (optional background thread) ────────────────────

def _auto_dispatch_loop(db: CoordinatorDB, interval_secs: int = 3600):
    """Periodically re-queue all standard jobs so nodes always have work."""
    time.sleep(10)   # brief startup delay
    while True:
        try:
            endpoints = db.get_active_endpoints()
            count     = db.dispatch_all(endpoints)
            log.info("Auto-dispatch: %d jobs queued for %d leagues", count, len(endpoints))
        except Exception as exc:
            log.error("Auto-dispatch error: %s", exc)
        time.sleep(interval_secs)


# ── Entry point ──────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="TrulySporting Coordinator Server")
    parser.add_argument("--host",         default="0.0.0.0",
                        help="Bind host (default: 0.0.0.0, accepts all connections)")
    parser.add_argument("--port",         type=int, default=8765,
                        help="Listen port (default: 8765)")
    parser.add_argument("--db",           default="espn_deep_analytics.db",
                        help="SQLite database path (shared with sporting.py)")
    parser.add_argument("--auto-dispatch", action="store_true",
                        help="Periodically re-queue all active-league jobs automatically")
    parser.add_argument("--dispatch-interval", type=int, default=3600,
                        help="Auto-dispatch interval in seconds (default: 3600)")
    args = parser.parse_args()

    db = CoordinatorDB(args.db)
    CoordinatorHandler.db = db

    if args.auto_dispatch:
        t = threading.Thread(
            target=_auto_dispatch_loop,
            args=(db, args.dispatch_interval),
            daemon=True,
        )
        t.start()
        log.info("Auto-dispatch enabled every %ds", args.dispatch_interval)

    server = ThreadingHTTPServer((args.host, args.port), CoordinatorHandler)

    log.info("=" * 60)
    log.info(" TrulySporting Coordinator ready")
    log.info("  → http://%s:%d", args.host, args.port)
    log.info("  → database: %s", args.db)
    log.info("")
    log.info(" API:")
    log.info("  GET  /health")
    log.info("  GET  /queue/status")
    log.info("  GET  /jobs/next?node_id=<id>")
    log.info("  GET  /jobs/list?status=pending&limit=50")
    log.info("  POST /jobs/result         { job_id, node_id, result_json, success, error }")
    log.info("  POST /jobs/dispatch       { url, endpoint_key, sport_key, ... }")
    log.info("  POST /jobs/dispatch_all   { endpoints: [...] }  (uses config if omitted)")
    log.info("  POST /jobs/clear          { status: done|failed }")
    log.info("")
    log.info(" On any other PC, run:  python fetch_node.py --coordinator http://<this-ip>:%d", args.port)
    log.info("=" * 60)

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        log.info("Shutting down…")
        server.shutdown()


if __name__ == "__main__":
    main()

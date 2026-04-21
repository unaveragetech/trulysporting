import requests
import json
import re
import sqlite3
import time
import threading
import os
import hmac
import hashlib
import pathlib
import shutil
import logging
from datetime import datetime, timedelta, date
from typing import Optional, Dict, List, Any, Tuple
import pandas as pd
import streamlit as st
import plotly.graph_objects as go
import plotly.express as px

# ─────────────────────────────────────────────────────────────
# SCHEMA UTILITIES  (used by SchemaCrawler + Schema Explorer tab)
# ─────────────────────────────────────────────────────────────

def _flatten_json(obj: Any, prefix: str = '', depth: int = 0,
                  max_depth: int = 8) -> Dict[str, tuple]:
    """
    Recursively flatten a JSON structure into a dict of:
        { 'dot.notation[0].path' : (type_name, example_string) }
    Arrays are sampled at index [0] to keep output manageable.
    """
    if depth > max_depth:
        return {prefix: ('...truncated', '(max depth)')} if prefix else {}
    result: Dict[str, tuple] = {}
    if isinstance(obj, dict):
        for k, v in obj.items():
            new_key = f"{prefix}.{k}" if prefix else k
            result.update(_flatten_json(v, new_key, depth + 1, max_depth))
    elif isinstance(obj, list):
        if not obj:
            result[prefix or 'list'] = ('list', '[]')
        else:
            result.update(_flatten_json(obj[0], f"{prefix}[0]", depth + 1, max_depth))
    else:
        vtype = 'null' if obj is None else type(obj).__name__
        result[prefix] = (vtype, '' if obj is None else str(obj)[:150])
    return result


def _schema_extract_to_df(
    url: str,
    params: dict,
    field_paths: List[str],
) -> Tuple[pd.DataFrame, Optional[str]]:
    """
    Fetch a URL, detect the root array from field_paths, iterate every
    element of that array, extract the selected sub-paths as columns,
    and return (DataFrame, error_string|None).

    Example path:  'events[0].competitions[0].competitors[0].team.abbreviation'
    Root array:    'events'
    Per-item path: 'competitions[0].competitors[0].team.abbreviation'

    If no root array is detected (path starts with a plain key), the
    whole JSON object is treated as a single row.
    """

    def _nav(obj: Any, path: str) -> Any:
        """Navigate dot/bracket path on a nested dict/list."""
        for seg in re.split(r'[.\[]', path):
            seg = seg.rstrip(']')
            if not seg:
                continue
            try:
                obj = obj[int(seg)] if seg.isdigit() else obj[seg]
            except (KeyError, IndexError, TypeError):
                return None
        return obj

    def _root_and_sub(path: str) -> Tuple[Optional[str], str]:
        """Split 'root[0].rest.of.path' → ('root', 'rest.of.path')."""
        m = re.match(r'^(\w+)\[0\](\.(.+))?$', path)
        if m:
            return m.group(1), m.group(3) or ''
        return None, path

    try:
        hdrs = {'User-Agent': 'Mozilla/5.0 (TrulySporting/1.0)'}
        resp = requests.get(url, params=params, headers=hdrs, timeout=25)
        resp.raise_for_status()
        data = resp.json()
    except Exception as exc:
        return pd.DataFrame(), str(exc)

    # Determine root array — first one found across all selected paths
    root_key: Optional[str] = None
    for fp in field_paths:
        rk, _ = _root_and_sub(fp)
        if rk and rk in data and isinstance(data.get(rk), list):
            root_key = rk
            break

    def _safe_col(fp: str) -> str:
        """Human-readable column name: use the last 2-3 non-index segments."""
        parts = [p.rstrip(']') for p in re.split(r'[.\[]', fp) if p.rstrip(']') and not p.rstrip(']').isdigit()]
        return '.'.join(parts[-3:]) if len(parts) >= 3 else '.'.join(parts) or fp

    if root_key:
        root_arr = data[root_key]
        prefix = f'{root_key}[0].'
        rows = []
        for item in root_arr:
            if not isinstance(item, dict):
                continue
            row: Dict[str, Any] = {}
            for fp in field_paths:
                col = _safe_col(fp)
                if fp.startswith(prefix):
                    row[col] = _nav(item, fp[len(prefix):])
                elif fp == f'{root_key}[0]':
                    row[col] = str(item)[:80]
                else:
                    row[col] = _nav(data, fp)
            rows.append(row)
        return pd.DataFrame(rows), None
    else:
        # Single-object response (e.g. team_detail)
        row = {_safe_col(fp): _nav(data, fp) for fp in field_paths}
        return pd.DataFrame([row]), None


# ─────────────────────────────────────────────────────────────
# 1. ADVANCED ENDPOINT REGISTRY & PARSER
# ─────────────────────────────────────────────────────────────

class ESPNParser:
    """
    Specialized parsers for each ESPN API endpoint type.

    Live API response structures (confirmed by inspection):

    SCOREBOARD (/scoreboard):
      - NBA:  data['events'][] → competitions[0] → competitors[], status, leaders, ...
      - NFL:  data['season']['events'][] → same sub-structure
      - Each competitor: homeAway ("home"/"away"), score, linescores[], statistics[],
        leaders[], records[], team (displayName, abbreviation, color, logo)
      - Competition level: venue, attendance, broadcast, notes[], headlines[], links

    TEAMS (/teams):
      - data['sports'][0]['leagues'][0]['teams'][] → team {id, displayName, abbreviation,
        color, alternateColor, logos[], links[]}
      - NOTE: This endpoint returns team METADATA only — no roster/athlete data.
        Use /teams/:id for extended team details.

    NEWS (/news):
      - data['articles'][] → headline, description, published, lastModified,
        images[], categories[] (type: team/athlete/league/topic),
        links.web.href, type, byline

    RANKINGS (/rankings):
      - data['rankings'][] → name, ranks[] → current, previous, team, points,
        firstPlaceVotes
    """

    @staticmethod
    def parse_scoreboard(data: Dict, category: str, sport: str) -> List[Dict]:
        """
        Extracts per-game results including per-period linescores, team stats,
        win-loss records, player leaders with headshots, venue, broadcast, and links.
        Handles both NFL (events under data['season']) and NBA/others (data['events']).
        """
        games = []
        # NFL puts events inside season; NBA/others put them at top level
        events = data.get('events', [])
        if not events:
            events = data.get('season', {}).get('events', [])
        if not events:
            return games

        for event in events:
            try:
                comp = event['competitions'][0]
                competitors = comp['competitors']

                # Use homeAway field (NOT homeVenue — that field doesn't exist)
                home = next((c for c in competitors if c.get('homeAway') == 'home'), competitors[0])
                away = next((c for c in competitors if c.get('homeAway') == 'away'), competitors[1])

                # Per-period / per-quarter scores
                home_periods = [ls.get('displayValue', '') for ls in home.get('linescores', [])]
                away_periods = [ls.get('displayValue', '') for ls in away.get('linescores', [])]

                # Team-level statistics (FG%, REB, AST, passing/rushing yards, etc.)
                home_stats = {s['name']: s['displayValue'] for s in home.get('statistics', [])}
                away_stats = {s['name']: s['displayValue'] for s in away.get('statistics', [])}

                # Win-loss records
                home_record = next(
                    (r['summary'] for r in home.get('records', []) if r.get('type') == 'total'), ''
                )
                away_record = next(
                    (r['summary'] for r in away.get('records', []) if r.get('type') == 'total'), ''
                )

                home_team_info = home.get('team', {})
                away_team_info = away.get('team', {})

                # Top statistical leaders (points, rebounds, assists, passing, rushing, etc.)
                leaders = {}
                for leader_group in comp.get('leaders', []):
                    stat_name = leader_group.get('name', '')
                    leaders_list = leader_group.get('leaders', [])
                    if leaders_list:
                        top = leaders_list[0]
                        leaders[stat_name] = {
                            'athlete': top['athlete']['displayName'],
                            'value': top.get('displayValue', str(top.get('value', ''))),
                            'headshot': top['athlete'].get('headshot', ''),
                            'team_id': top.get('team', {}).get('id', ''),
                            'jersey': top['athlete'].get('jersey', ''),
                            'position': top['athlete'].get('position', {}).get('abbreviation', ''),
                        }

                # Game headline / recap description from competitions
                headline_text = ''
                if comp.get('headlines'):
                    headline_text = comp['headlines'][0].get('description', '')

                # Venue info
                venue = comp.get('venue', {})
                venue_name = venue.get('fullName', '')
                venue_city = venue.get('address', {}).get('city', '')

                # Game links (boxscore, recap, gamecast, pbp) from event-level AND
                # competition-level links — many non-football sports only put pbp at comp level
                event_links = {}
                _link_keys = {
                    'boxscore': 'boxscore', 'recap': 'recap',
                    'summary': 'summary', 'pbp': 'pbp',
                    'gamecast': 'gamecast', 'highlights': 'highlights',
                }
                for _src in (event.get('links', []), comp.get('links', [])):
                    for link in _src:
                        rels = link.get('rel', [])
                        for rel_key, store_key in _link_keys.items():
                            if rel_key in rels and store_key not in event_links:
                                event_links[store_key] = link.get('href', '')

                # Special event note (Super Bowl, Play-In, etc.)
                note = ''
                if comp.get('notes'):
                    note = comp['notes'][0].get('headline', '')

                # Status is at event level
                event_status = event.get('status', {})
                status_type = event_status.get('type', {})

                games.append({
                    'event_id': event['id'],
                    'date': event['date'][:10],
                    'name': event.get('name', ''),
                    'home_team': home_team_info.get('displayName', ''),
                    'home_abbr': home_team_info.get('abbreviation', ''),
                    'home_color': home_team_info.get('color', ''),
                    'home_logo': home_team_info.get('logo', ''),
                    'away_team': away_team_info.get('displayName', ''),
                    'away_abbr': away_team_info.get('abbreviation', ''),
                    'away_color': away_team_info.get('color', ''),
                    'away_logo': away_team_info.get('logo', ''),
                    'home_score': float(home.get('score') or 0),
                    'away_score': float(away.get('score') or 0),
                    'home_record': home_record,
                    'away_record': away_record,
                    'home_winner': bool(home.get('winner', False)),
                    'status': status_type.get('name', ''),
                    'status_detail': status_type.get('detail', ''),
                    'period': event_status.get('period', 0),
                    'clock': event_status.get('displayClock', ''),
                    'home_periods': json.dumps(home_periods),
                    'away_periods': json.dumps(away_periods),
                    'home_stats': json.dumps(home_stats),
                    'away_stats': json.dumps(away_stats),
                    'leaders': json.dumps(leaders),
                    'headline': headline_text,
                    'venue': venue_name,
                    'venue_city': venue_city,
                    'attendance': comp.get('attendance', 0),
                    'broadcast': comp.get('broadcast', ''),
                    'note': note,
                    'links': json.dumps(event_links),
                    'category': category,
                    'sport': sport,
                    # ── Fields discovered via Schema Crawler ──
                    'neutral_site':    int(bool(comp.get('neutralSite', False))),
                    'conference_game': int(bool(comp.get('conferenceCompetition', False))),
                    'odds_json': json.dumps(
                        {
                            'spread':     comp['odds'][0].get('details', ''),
                            'over_under': comp['odds'][0].get('overUnder', ''),
                            'home_ml':    comp['odds'][0].get('homeTeamOdds', {}).get('moneyLine', ''),
                            'away_ml':    comp['odds'][0].get('awayTeamOdds', {}).get('moneyLine', ''),
                            'provider':   comp['odds'][0].get('provider', {}).get('name', ''),
                        } if comp.get('odds') else {}
                    ),
                    'weather': (
                        f"{comp['weather'].get('temperature', '')}\u00b0 "
                        f"{comp['weather'].get('displayValue', '')}".strip()
                        if comp.get('weather') else ''
                    ),
                })
            except Exception as e:
                continue
        return games

    @staticmethod
    def parse_team_details(data: Dict, sport_key: str) -> List[Dict]:
        """
        Extracts team metadata from /teams endpoint.
        Returns: id, name, abbreviation, slug, color, alternate_color, logo_url.
        The /teams list endpoint does NOT include roster/athlete data.
        """
        teams = []
        try:
            league_teams = data['sports'][0]['leagues'][0]['teams']
            for team_obj in league_teams:
                team_info = team_obj['team']

                # Get the default (non-dark, non-scoreboard) logo
                logo_url = ''
                for logo in team_info.get('logos', []):
                    rels = logo.get('rel', [])
                    if 'full' in rels and 'default' in rels:
                        logo_url = logo.get('href', '')
                        break

                teams.append({
                    'sport_key': sport_key,
                    'team_id': team_info.get('id', ''),
                    'team_name': team_info.get('displayName', ''),
                    'team_abbr': team_info.get('abbreviation', ''),
                    'team_slug': team_info.get('slug', ''),
                    'color': team_info.get('color', ''),
                    'alternate_color': team_info.get('alternateColor', ''),
                    'logo_url': logo_url,
                    'fetched_at': datetime.now().isoformat(),
                })
        except Exception as e:
            print(f"Error parsing team details: {e}")
        return teams

    @staticmethod
    def parse_news(data: Dict) -> List[Dict]:
        """
        Extracts articles with headline, description, image URL,
        tagged athletes/teams, article type, and author byline.
        """
        articles = []
        for art in data.get('articles', []):
            # Prefer 'header' type image, fall back to first available
            image_url = ''
            for img in art.get('images', []):
                if not image_url:
                    image_url = img.get('url', '')
                if img.get('type') == 'header':
                    image_url = img.get('url', '')
                    break

            athletes = [c['description'] for c in art.get('categories', []) if c.get('type') == 'athlete']
            teams = [c['description'] for c in art.get('categories', []) if c.get('type') == 'team']

            articles.append({
                'headline': art.get('headline', ''),
                'description': art.get('description', ''),
                'published': art.get('published', ''),
                'last_modified': art.get('lastModified', ''),
                'link': art.get('links', {}).get('web', {}).get('href', ''),
                'image': image_url,
                'type': art.get('type', ''),
                'byline': art.get('byline', ''),
                'athletes': json.dumps(athletes),
                'teams': json.dumps(teams),
            })
        return articles

    @staticmethod
    def parse_rankings(data: Dict) -> List[Dict]:
        """
        Extracts AP/Coaches polls and other rankings.
        Returns rank, previous rank, team, record, points, first-place votes,
        plus trend, logo_url, color extracted directly from ESPN rank objects.
        """
        rankings = []
        for poll in data.get('rankings', []):
            poll_name = poll.get('name', 'Unknown Poll')
            season_obj = poll.get('season', {})
            season_year = season_obj.get('year', '') if isinstance(season_obj, dict) else ''
            season_display = (season_obj.get('displayName', str(season_year))
                              if isinstance(season_obj, dict) else '')
            for rank_item in poll.get('ranks', []):
                team_info = rank_item.get('team', {})
                # recordSummary is directly on rank_item (e.g. '37-3')
                record = rank_item.get('recordSummary', '')
                if not record:
                    rec_items = team_info.get('record', {}).get('items', [])
                    record = rec_items[0].get('summary', '') if rec_items else ''
                # Logo from team.logos[]
                logos = team_info.get('logos', [])
                logo_url = logos[0].get('href', '') if logos else ''
                # Location + name = displayName (e.g. 'Michigan Wolverines')
                display_name = (f"{team_info.get('location','')} "
                                f"{team_info.get('name','')}").strip()
                if not display_name:
                    display_name = team_info.get('displayName', team_info.get('nickname', 'Unknown'))
                rankings.append({
                    'poll':             poll_name,
                    'season_type':      season_display,
                    'season_year':      season_year,
                    'rank':             rank_item.get('current', 0),
                    'previous':         rank_item.get('previous', 0),
                    'trend':            str(rank_item.get('trend', '-')),
                    'team':             display_name,
                    'team_abbr':        team_info.get('abbreviation', ''),
                    'team_logo':        logo_url,
                    'team_color':       '#' + team_info.get('color', '1a73e8'),
                    'record':           record,
                    'points':           rank_item.get('points', 0),
                    'first_place_votes': rank_item.get('firstPlaceVotes', 0),
                })
        return rankings

    @staticmethod
    def parse_single_team(data: Dict, sport_key: str) -> Optional[Dict]:
        """
        Parses /teams/:abbr response for a single team.

        Confirmed live structure (NBA/NFL):
          data.team: id, abbreviation, slug, displayName, color, alternateColor, logos[]
          data.team.record.items[]: type (total/home/road), summary, stats[]
            stats include: wins, losses, avgPointsFor, avgPointsAgainst, differential,
                           winPercent, playoffSeed, streak, divisionRecord
          data.team.franchise.venue: fullName, address {city, state, zipCode}, grass, indoor
          data.team.standingSummary: e.g. '1st in Pacific Division'
          data.team.nextEvent[]: upcoming games with date, name, competitions[],
                                  broadcasts[], tickets, status
          data.team.groups: conference/division
        """
        try:
            team = data['team']
            # Record breakdown (total / home / road)
            records: Dict = {}
            for item in team.get('record', {}).get('items', []):
                rec_type = item.get('type', 'total')
                stats_dict = {s['name']: s.get('value', s.get('displayValue', ''))
                              for s in item.get('stats', [])}
                stats_dict['summary'] = item.get('summary', '')
                records[rec_type] = stats_dict

            venue_data = team.get('franchise', {}).get('venue', {})
            logo_url = next(
                (lg['href'] for lg in team.get('logos', [])
                 if 'full' in lg.get('rel', []) and 'default' in lg.get('rel', [])),
                ''
            )
            return {
                'sport_key':        sport_key,
                'team_id':          team.get('id', ''),
                'team_abbr':        team.get('abbreviation', ''),
                'team_slug':        team.get('slug', ''),
                'team_name':        team.get('displayName', ''),
                'color':            team.get('color', ''),
                'alternate_color':  team.get('alternateColor', ''),
                'logo_url':         logo_url,
                'records_json':     json.dumps(records),
                'standing_summary': team.get('standingSummary', ''),
                'venue_name':       venue_data.get('fullName', ''),
                'venue_city':       venue_data.get('address', {}).get('city', ''),
                'venue_state':      venue_data.get('address', {}).get('state', ''),
                'venue_grass':      int(bool(venue_data.get('grass', False))),
                'venue_indoor':     int(bool(venue_data.get('indoor', False))),
                'next_event_json':  json.dumps(team.get('nextEvent', [])),
                'fetched_at':       datetime.now().isoformat(),
            }
        except Exception as e:
            print(f'parse_single_team error: {e}')
            return None

    @staticmethod
    def parse_game_summary(data: Dict, sport_key: str) -> Optional[Dict]:
        """
        Parses /summary?event=X — extracts every meaningful field:
          boxscore.teams[]      → full team stats (all labels + values)
          boxscore.players[]    → per-player stats for every category
          leaders[]             → stat leaders with headshots
          injuries[]            → full injury report
          gameInfo.officials[]  → referee crew
          videos[]              → highlight clips
          winprobability[]      → per-play win %
          scoringPlays[]        → scoring-only play list
          pickcenter[]          → full betting data
          standings.groups[]    → division standings
        """
        try:
            header = data.get('header', {})
            comps  = header.get('competitions', [])
            if not comps:
                return None
            event_id = comps[0].get('id', '')
            if not event_id:
                return None

            # Identify home/away team IDs and abbreviations
            home_id   = ''
            away_id   = ''
            home_abbr = ''
            away_abbr = ''
            for cp in comps[0].get('competitors', []):
                tid   = cp.get('team', {}).get('id', '')
                tabbr = cp.get('team', {}).get('abbreviation', '')
                if cp.get('homeAway') == 'home':
                    home_id, home_abbr = tid, tabbr
                else:
                    away_id, away_abbr = tid, tabbr

            # ── Full team stats (all labels) ─────────────────
            home_stats:           Dict = {}
            away_stats:           Dict = {}
            team_stats_full:      List = []
            for t in data.get('boxscore', {}).get('teams', []):
                stats_raw = t.get('statistics', [])
                stats_dict = {s.get('name', ''): s.get('displayValue', '') for s in stats_raw}
                stats_list = [{'label': s.get('label', s.get('name', '')),
                               'name':  s.get('name', ''),
                               'value': s.get('displayValue', '')} for s in stats_raw]
                side = t.get('homeAway', '')
                tabbr_local = t.get('team', {}).get('abbreviation', '')
                team_stats_full.append({'team': tabbr_local, 'side': side, 'stats': stats_list})
                if side == 'home':
                    home_stats = stats_dict
                else:
                    away_stats = stats_dict

            # ── Player stats per category ────────────────────
            player_stats: List = []
            for side in data.get('boxscore', {}).get('players', []):
                tabbr_local = side.get('team', {}).get('abbreviation', '')
                tside = side.get('displayOrder', 1)
                for cat in side.get('statistics', []):
                    athletes_list = []
                    for ath_entry in cat.get('athletes', []):
                        ath = ath_entry.get('athlete', {})
                        hs  = ath.get('headshot', {})
                        athletes_list.append({
                            'name':     ath.get('displayName', ''),
                            'id':       ath.get('id', ''),
                            'jersey':   ath.get('jersey', ''),
                            'headshot': hs.get('href', '') if isinstance(hs, dict) else '',
                            'stats':    ath_entry.get('stats', []),
                        })
                    player_stats.append({
                        'team':        tabbr_local,
                        'order':       tside,
                        'category':    cat.get('name', ''),
                        'displayName': cat.get('text', cat.get('name', '')),
                        'labels':      cat.get('labels', []),
                        'descriptions': cat.get('descriptions', []),
                        'totals':      cat.get('totals', []),
                        'athletes':    athletes_list,
                    })

            # ── Stat leaders ─────────────────────────────────
            leaders_data: List = []
            for team_leaders in data.get('leaders', []):
                team_id_loc = team_leaders.get('team', {}).get('id', '')
                for cat in team_leaders.get('leaders', []):
                    for ldr in cat.get('leaders', []):
                        ath = ldr.get('athlete', {})
                        hs  = ath.get('headshot', {})
                        leaders_data.append({
                            'team_id':   team_id_loc,
                            'is_home':   team_id_loc == home_id,
                            'stat':      cat.get('displayName', ''),
                            'stat_name': cat.get('name', ''),
                            'athlete':   ath.get('displayName', ''),
                            'headshot':  hs.get('href', '') if isinstance(hs, dict) else '',
                            'jersey':    ath.get('jersey', ''),
                            'position':  (ath.get('position') or {}).get('abbreviation', ''),
                            'value':     ldr.get('displayValue', ''),
                            'summary':   ldr.get('summary', ''),
                        })

            # ── Last 5 game results ───────────────────────────
            last_five_home: List = []
            last_five_away: List = []
            for entry in data.get('lastFiveGames', []):
                team_id_loc = entry.get('team', {}).get('id', '')
                games_list = [
                    {'id': e.get('id', ''), 'result': e.get('gameResult', ''),
                     'score': e.get('score', ''),
                     'opponent': e.get('opponent', {}).get('abbreviation', ''),
                     'date': e.get('gameDate', '')[:10],
                     'atVs': e.get('atVs', '')}
                    for e in entry.get('events', [])
                ]
                if team_id_loc == home_id:
                    last_five_home = games_list
                else:
                    last_five_away = games_list

            # ── Injuries ──────────────────────────────────────
            injuries_data: List = []
            for team_inj in data.get('injuries', []):
                team_id_loc  = team_inj.get('team', {}).get('id', '')
                tabbr_local  = team_inj.get('team', {}).get('abbreviation', '')
                for inj in team_inj.get('injuries', []):
                    ath = inj.get('athlete', {})
                    det = inj.get('details', {})
                    hs  = ath.get('headshot', {})
                    injuries_data.append({
                        'team_id':  team_id_loc,
                        'team':     tabbr_local,
                        'athlete':  ath.get('displayName', ''),
                        'jersey':   ath.get('jersey', ''),
                        'pos':      (ath.get('position') or {}).get('abbreviation', ''),
                        'headshot': hs.get('href', '') if isinstance(hs, dict) else '',
                        'status':   inj.get('status', ''),
                        'type':     det.get('type', ''),
                        'detail':   det.get('detail', ''),
                        'return':   det.get('returnDate', ''),
                    })

            # ── Officials ─────────────────────────────────────
            gi = data.get('gameInfo', {})
            officials_data = [
                {'name': o.get('displayName', ''),
                 'role': o.get('position', {}).get('displayName', '')}
                for o in gi.get('officials', [])
            ]

            # ── Videos ────────────────────────────────────────
            videos_data = []
            for v in data.get('videos', []):
                links = v.get('links', {})
                web_href = (links.get('web') or {}).get('href', '')
                thumb = (v.get('thumbnail') or {}).get('href', '') if isinstance(v.get('thumbnail'), dict) else v.get('thumbnail', '')
                videos_data.append({
                    'id':          v.get('id', ''),
                    'headline':    v.get('headline', ''),
                    'description': v.get('description', ''),
                    'duration':    v.get('duration', 0),
                    'thumbnail':   thumb,
                    'link':        web_href,
                })

            # ── Win Probability ───────────────────────────────
            win_prob = data.get('winprobability', [])

            # ── Scoring Plays ─────────────────────────────────
            scoring_plays_data = []
            for sp in data.get('scoringPlays', []):
                scoring_plays_data.append({
                    'id':        sp.get('id', ''),
                    'type':      (sp.get('type') or {}).get('text', ''),
                    'text':      sp.get('text', ''),
                    'away':      sp.get('awayScore', 0),
                    'home':      sp.get('homeScore', 0),
                    'period':    (sp.get('period') or {}).get('number', 0),
                    'clock':     (sp.get('clock') or {}).get('displayValue', ''),
                    'team':      (sp.get('team') or {}).get('abbreviation', ''),
                })

            # ── Pick Center (full) ────────────────────────────
            pickcenter_data = []
            for pc in data.get('pickcenter', []):
                pickcenter_data.append({
                    'provider':       (pc.get('provider') or {}).get('name', ''),
                    'details':        pc.get('details', ''),
                    'overUnder':      pc.get('overUnder', ''),
                    'spread':         pc.get('spread', ''),
                    'overOdds':       pc.get('overOdds', ''),
                    'underOdds':      pc.get('underOdds', ''),
                    'home_ml':        (pc.get('homeTeamOdds') or {}).get('moneyLine', ''),
                    'away_ml':        (pc.get('awayTeamOdds') or {}).get('moneyLine', ''),
                    'home_spread':    (pc.get('homeTeamOdds') or {}).get('spreadOdds', ''),
                    'away_spread':    (pc.get('awayTeamOdds') or {}).get('spreadOdds', ''),
                    'home_favorite':  (pc.get('homeTeamOdds') or {}).get('favorite', False),
                })

            # ── Simple odds dict (for backwards compat) ──────
            odds_data: Dict = {}
            if pickcenter_data:
                pc0 = pickcenter_data[0]
                odds_data = {
                    'home_ml':    pc0['home_ml'],
                    'away_ml':    pc0['away_ml'],
                    'spread':     pc0['details'],
                    'over_under': pc0['overUnder'],
                    'provider':   pc0['provider'],
                }

            venue = gi.get('venue', {})
            return {
                'event_id':             event_id,
                'sport_key':            sport_key,
                'home_abbr':            home_abbr,
                'away_abbr':            away_abbr,
                'home_stats_json':      json.dumps(home_stats),
                'away_stats_json':      json.dumps(away_stats),
                'team_stats_full_json': json.dumps(team_stats_full),
                'player_stats_json':    json.dumps(player_stats),
                'leaders_json':         json.dumps(leaders_data),
                'last_five_home':       json.dumps(last_five_home),
                'last_five_away':       json.dumps(last_five_away),
                'injuries_json':        json.dumps(injuries_data),
                'officials_json':       json.dumps(officials_data),
                'videos_json':          json.dumps(videos_data),
                'win_prob_json':        json.dumps(win_prob),
                'scoring_plays_json':   json.dumps(scoring_plays_data),
                'pickcenter_json':      json.dumps(pickcenter_data),
                'standings_json':       json.dumps(data.get('standings', {})),
                'venue_name':           venue.get('fullName', ''),
                'venue_city':           venue.get('address', {}).get('city', ''),
                'odds_json':            json.dumps(odds_data),
                'fetched_at':           datetime.now().isoformat(),
            }
        except Exception as e:
            print(f'parse_game_summary error: {e}')
            return None


class EndpointRegistry:
    # Using https (consistent with actual API responses)
    BASE_URL = "https://site.api.espn.com/apis/site/v2/sports"

    REGISTRY = {
        'football': {
            'college-football': {
                'scoreboard': f"{BASE_URL}/football/college-football/scoreboard",
                'teams': f"{BASE_URL}/football/college-football/teams",
                'news': f"{BASE_URL}/football/college-football/news",
                'rankings': f"{BASE_URL}/football/college-football/rankings",
                # summary requires ?event=:gameId
                'summary': f"{BASE_URL}/football/college-football/summary",
            },
            'nfl': {
                'scoreboard': f"{BASE_URL}/football/nfl/scoreboard",
                'teams': f"{BASE_URL}/football/nfl/teams",
                'news': f"{BASE_URL}/football/nfl/news",
                'summary': f"{BASE_URL}/football/nfl/summary",
            },
        },
        'baseball': {
            'mlb': {
                'scoreboard': f"{BASE_URL}/baseball/mlb/scoreboard",
                'teams': f"{BASE_URL}/baseball/mlb/teams",
                'news': f"{BASE_URL}/baseball/mlb/news",
                'summary': f"{BASE_URL}/baseball/mlb/summary",
            },
            'college-baseball': {
                'scoreboard': f"{BASE_URL}/baseball/college-baseball/scoreboard",
            },
        },
        'hockey': {
            'nhl': {
                'scoreboard': f"{BASE_URL}/hockey/nhl/scoreboard",
                'teams': f"{BASE_URL}/hockey/nhl/teams",
                'news': f"{BASE_URL}/hockey/nhl/news",
                'summary': f"{BASE_URL}/hockey/nhl/summary",
            },
        },
        'basketball': {
            'nba': {
                'scoreboard': f"{BASE_URL}/basketball/nba/scoreboard",
                'teams': f"{BASE_URL}/basketball/nba/teams",
                'news': f"{BASE_URL}/basketball/nba/news",
                'summary': f"{BASE_URL}/basketball/nba/summary",
            },
            'wnba': {
                'scoreboard': f"{BASE_URL}/basketball/wnba/scoreboard",
                'teams': f"{BASE_URL}/basketball/wnba/teams",
                'news': f"{BASE_URL}/basketball/wnba/news",
                'summary': f"{BASE_URL}/basketball/wnba/summary",
            },
            'mens-college-basketball': {
                'scoreboard': f"{BASE_URL}/basketball/mens-college-basketball/scoreboard",
                'teams': f"{BASE_URL}/basketball/mens-college-basketball/teams",
                'news': f"{BASE_URL}/basketball/mens-college-basketball/news",
                'rankings': f"{BASE_URL}/basketball/mens-college-basketball/rankings",
                'summary': f"{BASE_URL}/basketball/mens-college-basketball/summary",
            },
            'womens-college-basketball': {
                'scoreboard': f"{BASE_URL}/basketball/womens-college-basketball/scoreboard",
                'teams': f"{BASE_URL}/basketball/womens-college-basketball/teams",
                'news': f"{BASE_URL}/basketball/womens-college-basketball/news",
                'rankings': f"{BASE_URL}/basketball/womens-college-basketball/rankings",
                'summary': f"{BASE_URL}/basketball/womens-college-basketball/summary",
            },
        },
        'soccer': {
            # League abbreviation ('eng.1' = EPL, 'usa.1' = MLS)
            'eng.1': {
                'scoreboard': f"{BASE_URL}/soccer/eng.1/scoreboard",
                'teams': f"{BASE_URL}/soccer/eng.1/teams",
                'news': f"{BASE_URL}/soccer/eng.1/news",
                'summary': f"{BASE_URL}/soccer/eng.1/summary",
            },
            'usa.1': {
                'scoreboard': f"{BASE_URL}/soccer/usa.1/scoreboard",
                'teams': f"{BASE_URL}/soccer/usa.1/teams",
                'news': f"{BASE_URL}/soccer/usa.1/news",
                'summary': f"{BASE_URL}/soccer/usa.1/summary",
            },
        },
    }

    @classmethod
    def get_all_keys(cls) -> List[str]:
        keys = []
        for cat, sports in cls.REGISTRY.items():
            for sport in sports.keys():
                keys.append(f"{cat}/{sport}")
        return keys

    @classmethod
    def get_url(cls, category: str, sport: str, endpoint_type: str) -> Optional[str]:
        try:
            return cls.REGISTRY[category][sport][endpoint_type]
        except KeyError:
            return None

    @classmethod
    def get_team_url(cls, category: str, sport: str, team_id: str) -> str:
        """URL for extended single-team details including roster."""
        return f"{cls.BASE_URL}/{category}/{sport}/teams/{team_id}"


# ─────────────────────────────────────────────────────────────
# 2. DATABASE MANAGER (Enhanced Schema)
# ─────────────────────────────────────────────────────────────

class SportsDB:
    def __init__(self, db_name: str = "espn_deep_analytics.db"):
        self.db_name = db_name
        self.init_db()

    def get_connection(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_name)
        conn.row_factory = sqlite3.Row
        return conn

    def init_db(self):
        conn = self.get_connection()
        c = conn.cursor()

        # Raw API response cache
        c.execute('''CREATE TABLE IF NOT EXISTS api_cache (
            endpoint_key TEXT PRIMARY KEY,
            response_json TEXT,
            fetched_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )''')

        # Full game history with per-period scores, stats, records, leaders, venue
        c.execute('''CREATE TABLE IF NOT EXISTS game_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            event_id TEXT UNIQUE,
            category TEXT,
            sport TEXT,
            event_date TEXT,
            name TEXT,
            home_team TEXT,
            home_abbr TEXT,
            home_color TEXT,
            home_logo TEXT,
            away_team TEXT,
            away_abbr TEXT,
            away_color TEXT,
            away_logo TEXT,
            home_score REAL,
            away_score REAL,
            home_record TEXT,
            away_record TEXT,
            home_winner INTEGER,
            status TEXT,
            status_detail TEXT,
            period INTEGER,
            clock TEXT,
            home_periods TEXT,
            away_periods TEXT,
            home_stats TEXT,
            away_stats TEXT,
            leaders_json TEXT,
            headline TEXT,
            venue TEXT,
            venue_city TEXT,
            attendance INTEGER,
            broadcast TEXT,
            note TEXT,
            links_json TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )''')

        # Team metadata registry (from /teams endpoint)
        c.execute('''CREATE TABLE IF NOT EXISTS teams_registry (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            sport_key TEXT,
            team_id TEXT,
            team_name TEXT,
            team_abbr TEXT,
            team_slug TEXT,
            color TEXT,
            alternate_color TEXT,
            logo_url TEXT,
            fetched_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(sport_key, team_id)
        )''')

        # News archive with image URLs, athlete/team tags, byline
        c.execute('''CREATE TABLE IF NOT EXISTS news_archive (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            sport_key TEXT,
            headline TEXT,
            link TEXT UNIQUE,
            published TEXT,
            last_modified TEXT,
            description TEXT,
            image_url TEXT,
            article_type TEXT,
            byline TEXT,
            athletes TEXT,
            teams TEXT
        )''')

        # Rankings (AP, Coaches, etc.)
        c.execute('''CREATE TABLE IF NOT EXISTS rankings (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            sport_key TEXT,
            poll TEXT,
            season_type TEXT,
            rank INTEGER,
            previous_rank INTEGER,
            team TEXT,
            team_abbr TEXT,
            record TEXT,
            points REAL,
            first_place_votes INTEGER,
            fetched_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(sport_key, poll, team)
        )''')

        # Rankings history — one row per (poll, team, snapshot_date) so we can chart rank movement
        c.execute('''CREATE TABLE IF NOT EXISTS rankings_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            sport_key TEXT,
            poll TEXT,
            snapshot_date TEXT,
            rank INTEGER,
            previous_rank INTEGER,
            points REAL,
            first_place_votes INTEGER,
            trend TEXT,
            record TEXT,
            team_name TEXT,
            team_abbr TEXT,
            team_logo TEXT,
            team_color TEXT,
            UNIQUE(sport_key, poll, snapshot_date, team_abbr)
        )''')

        # App configuration
        c.execute('''CREATE TABLE IF NOT EXISTS config (
            key TEXT PRIMARY KEY,
            value TEXT
        )''')

        # Extended single-team data (from /teams/:abbr endpoint)
        c.execute('''CREATE TABLE IF NOT EXISTS team_detail (
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
        )''')

        # Per-game summaries (from /summary?event=X)
        c.execute('''CREATE TABLE IF NOT EXISTS game_summaries (
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
        )''')

        # Distributed job queue (shared with coordinator.py)
        c.execute('''CREATE TABLE IF NOT EXISTS jobs (
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
        )''')

        # Node registry (managed by coordinator.py, readable here)
        c.execute('''CREATE TABLE IF NOT EXISTS nodes (
            node_id        TEXT PRIMARY KEY,
            ip             TEXT,
            last_seen      TEXT,
            jobs_completed INTEGER DEFAULT 0,
            jobs_failed    INTEGER DEFAULT 0,
            version        TEXT DEFAULT "1.0"
        )''')

        # Field schema catalog (populated by SchemaCrawler / Schema Explorer tab)
        c.execute('''CREATE TABLE IF NOT EXISTS field_schema (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            sport_key     TEXT NOT NULL,
            endpoint_type TEXT NOT NULL,
            url           TEXT,
            field_path    TEXT NOT NULL,
            value_type    TEXT,
            example_value TEXT,
            depth         INTEGER DEFAULT 0,
            discovered_at TEXT,
            UNIQUE(sport_key, endpoint_type, field_path)
        )''')

        # Play-by-play: one row per play, keyed by event_id + play_id
        c.execute('''CREATE TABLE IF NOT EXISTS play_by_play (
            id               INTEGER PRIMARY KEY AUTOINCREMENT,
            event_id         TEXT NOT NULL,
            sport_key        TEXT NOT NULL,
            drive_id         TEXT,
            drive_num        INTEGER,
            drive_desc       TEXT,
            drive_result     TEXT,
            drive_yards      INTEGER DEFAULT 0,
            drive_is_score   INTEGER DEFAULT 0,
            offensive_plays  INTEGER DEFAULT 0,
            team_abbr        TEXT,
            play_id          TEXT,
            sequence_num     INTEGER,
            play_type        TEXT,
            play_abbr        TEXT,
            play_text        TEXT,
            away_score       INTEGER DEFAULT 0,
            home_score       INTEGER DEFAULT 0,
            period           INTEGER DEFAULT 0,
            clock            TEXT,
            scoring_play     INTEGER DEFAULT 0,
            is_turnover      INTEGER DEFAULT 0,
            stat_yardage     INTEGER DEFAULT 0,
            yard_line        INTEGER DEFAULT 0,
            yards_to_endzone INTEGER DEFAULT 0,
            down             INTEGER DEFAULT 0,
            distance         INTEGER DEFAULT 0,
            down_dist_text   TEXT,
            fetched_at       TEXT,
            UNIQUE(event_id, play_id)
        )''')

        # Team roster: one row per player per team
        c.execute('''CREATE TABLE IF NOT EXISTS roster (
            id               INTEGER PRIMARY KEY AUTOINCREMENT,
            sport_key        TEXT NOT NULL,
            team_id          TEXT NOT NULL,
            team_abbr        TEXT,
            position_group   TEXT,
            player_id        TEXT NOT NULL,
            display_name     TEXT,
            first_name       TEXT,
            last_name        TEXT,
            jersey           TEXT,
            position         TEXT,
            position_name    TEXT,
            display_height   TEXT,
            display_weight   TEXT,
            age              INTEGER DEFAULT 0,
            college          TEXT,
            headshot_url     TEXT,
            injury_status    TEXT,
            status_name      TEXT DEFAULT \'Active\',
            player_slug      TEXT,
            experience       INTEGER DEFAULT 0,
            fetched_at       TEXT,
            UNIQUE(sport_key, team_id, player_id)
        )''')

        # Per-player per-game stats flattened from game summary boxscores
        c.execute('''CREATE TABLE IF NOT EXISTS player_game_stats (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            event_id     TEXT NOT NULL,
            game_date    TEXT,
            sport_key    TEXT NOT NULL,
            team_abbr    TEXT,
            player_id    TEXT,
            player_name  TEXT,
            headshot_url TEXT,
            category     TEXT,
            stat_labels  TEXT,
            stat_values  TEXT,
            fetched_at   TEXT,
            UNIQUE(event_id, player_id, category)
        )''')
        c.execute('CREATE INDEX IF NOT EXISTS idx_pgs_sport_player ON player_game_stats(sport_key, player_name)')
        c.execute('CREATE INDEX IF NOT EXISTS idx_pgs_event ON player_game_stats(event_id)')

        # Cached full player stat profiles (built once per player/season, reused)
        c.execute('''CREATE TABLE IF NOT EXISTS player_profiles (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            sport_key    TEXT NOT NULL,
            player_id    TEXT NOT NULL,
            player_name  TEXT,
            team_id      TEXT,
            team_abbr    TEXT,
            season_year  INTEGER,
            profile_json TEXT,
            sources      TEXT,
            built_at     TEXT,
            UNIQUE(sport_key, player_id, season_year)
        )''')
        c.execute('CREATE INDEX IF NOT EXISTS idx_pp_sport_player ON player_profiles(sport_key, player_name)')

        # Migrations: safely add new columns to existing tables
        _migrations = [
            "ALTER TABLE game_history ADD COLUMN neutral_site INTEGER DEFAULT 0",
            "ALTER TABLE game_history ADD COLUMN conference_game INTEGER DEFAULT 0",
            "ALTER TABLE game_history ADD COLUMN odds_json TEXT DEFAULT '{}'",
            "ALTER TABLE game_history ADD COLUMN weather TEXT DEFAULT ''",
            # Extended game summary columns
            "ALTER TABLE game_summaries ADD COLUMN player_stats_json TEXT DEFAULT '[]'",
            "ALTER TABLE game_summaries ADD COLUMN team_stats_full_json TEXT DEFAULT '[]'",
            "ALTER TABLE game_summaries ADD COLUMN officials_json TEXT DEFAULT '[]'",
            "ALTER TABLE game_summaries ADD COLUMN videos_json TEXT DEFAULT '[]'",
            "ALTER TABLE game_summaries ADD COLUMN win_prob_json TEXT DEFAULT '[]'",
            "ALTER TABLE game_summaries ADD COLUMN scoring_plays_json TEXT DEFAULT '[]'",
            "ALTER TABLE game_summaries ADD COLUMN pickcenter_json TEXT DEFAULT '[]'",
            "ALTER TABLE game_summaries ADD COLUMN home_abbr TEXT DEFAULT ''",
            "ALTER TABLE game_summaries ADD COLUMN away_abbr TEXT DEFAULT ''",
            # Extended roster columns
            "ALTER TABLE roster ADD COLUMN position_name TEXT DEFAULT ''",
            "ALTER TABLE roster ADD COLUMN status_name TEXT DEFAULT 'Active'",
            "ALTER TABLE roster ADD COLUMN player_slug TEXT DEFAULT ''",
            "ALTER TABLE player_game_stats ADD COLUMN game_date TEXT DEFAULT ''",
        ]
        for _m in _migrations:
            try:
                c.execute(_m)
            except sqlite3.OperationalError:
                pass  # column already exists — safe to skip

        c.execute("SELECT count(*) FROM config")
        if c.fetchone()[0] == 0:
            defaults = [
                ('default_refresh_interval', '3600'),
                ('active_endpoints', json.dumps([
                    'football/nfl',
                    'football/college-football',
                    'basketball/nba',
                    'basketball/wnba',
                    'basketball/mens-college-basketball',
                    'basketball/womens-college-basketball',
                    'baseball/mlb',
                    'baseball/college-baseball',
                    'hockey/nhl',
                    'soccer/eng.1',
                    'soccer/usa.1',
                ])),
            ]
            c.executemany("INSERT OR IGNORE INTO config VALUES (?, ?)", defaults)

        # Migration: if active_endpoints only has the old minimal defaults,
        # expand to the full league list so existing deployments get all leagues.
        _all_known = [
            'football/nfl', 'football/college-football',
            'basketball/nba', 'basketball/wnba',
            'basketball/mens-college-basketball', 'basketball/womens-college-basketball',
            'baseball/mlb', 'baseball/college-baseball',
            'hockey/nhl', 'soccer/eng.1', 'soccer/usa.1',
        ]
        _row = c.execute("SELECT value FROM config WHERE key='active_endpoints'").fetchone()
        if _row:
            _current = json.loads(_row[0])
            # If still only the original two defaults, upgrade to full list
            if set(_current) <= {'football/nfl', 'basketball/nba'}:
                c.execute("UPDATE config SET value=? WHERE key='active_endpoints'",
                          (json.dumps(_all_known),))

        conn.commit()
        conn.close()

    def save_games(self, games: List[Dict]):
        conn = self.get_connection()
        c = conn.cursor()
        for g in games:
            c.execute("""
                INSERT OR REPLACE INTO game_history
                (event_id, category, sport, event_date, name,
                 home_team, home_abbr, home_color, home_logo,
                 away_team, away_abbr, away_color, away_logo,
                 home_score, away_score, home_record, away_record, home_winner,
                 status, status_detail, period, clock,
                 home_periods, away_periods, home_stats, away_stats,
                 leaders_json, headline, venue, venue_city,
                 attendance, broadcast, note, links_json,
                 neutral_site, conference_game, odds_json, weather)
                VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
            """, (
                g['event_id'], g['category'], g['sport'], g['date'], g.get('name', ''),
                g['home_team'], g['home_abbr'], g['home_color'], g['home_logo'],
                g['away_team'], g['away_abbr'], g['away_color'], g['away_logo'],
                g['home_score'], g['away_score'], g['home_record'], g['away_record'],
                int(g['home_winner']),
                g['status'], g['status_detail'], g['period'], g['clock'],
                g['home_periods'], g['away_periods'], g['home_stats'], g['away_stats'],
                g['leaders'], g['headline'], g['venue'], g['venue_city'],
                g['attendance'], g['broadcast'], g['note'], g['links'],
                g.get('neutral_site', 0), g.get('conference_game', 0),
                g.get('odds_json', '{}'), g.get('weather', ''),
            ))
        conn.commit()
        conn.close()

    def save_teams(self, teams: List[Dict]):
        conn = self.get_connection()
        c = conn.cursor()
        for t in teams:
            c.execute("""
                INSERT OR REPLACE INTO teams_registry
                (sport_key, team_id, team_name, team_abbr, team_slug,
                 color, alternate_color, logo_url, fetched_at)
                VALUES (?,?,?,?,?,?,?,?,?)
            """, (
                t['sport_key'], t['team_id'], t['team_name'], t['team_abbr'],
                t['team_slug'], t['color'], t['alternate_color'], t['logo_url'],
                t['fetched_at'],
            ))
        conn.commit()
        conn.close()

    def save_news(self, sport_key: str, articles: List[Dict]):
        conn = self.get_connection()
        c = conn.cursor()
        for a in articles:
            if not a.get('link'):
                continue
            c.execute("""
                INSERT OR IGNORE INTO news_archive
                (sport_key, headline, link, published, last_modified,
                 description, image_url, article_type, byline, athletes, teams)
                VALUES (?,?,?,?,?,?,?,?,?,?,?)
            """, (
                sport_key, a['headline'], a['link'], a['published'],
                a.get('last_modified', ''), a['description'], a.get('image', ''),
                a.get('type', ''), a.get('byline', ''),
                a.get('athletes', '[]'), a.get('teams', '[]'),
            ))
        conn.commit()
        conn.close()

    def save_rankings(self, sport_key: str, rankings: List[Dict]):
        conn = self.get_connection()
        c = conn.cursor()
        for r in rankings:
            c.execute("""
                INSERT OR REPLACE INTO rankings
                (sport_key, poll, season_type, rank, previous_rank,
                 team, team_abbr, record, points, first_place_votes, fetched_at)
                VALUES (?,?,?,?,?,?,?,?,?,?,?)
            """, (
                sport_key, r['poll'], r.get('season_type', ''), r['rank'], r.get('previous', 0),
                r['team'], r.get('team_abbr', ''), r.get('record', ''), r.get('points', 0),
                r.get('first_place_votes', 0), datetime.now().isoformat(),
            ))
        conn.commit()
        conn.close()

    def save_rankings_snapshot(self, sport_key: str, rankings: List[Dict]):
        """Append a dated snapshot to rankings_history so we can chart rank over time."""
        today = datetime.now().strftime('%Y-%m-%d')
        conn = self.get_connection()
        c = conn.cursor()
        for r in rankings:
            c.execute("""
                INSERT OR REPLACE INTO rankings_history
                (sport_key, poll, snapshot_date, rank, previous_rank, points,
                 first_place_votes, trend, record, team_name, team_abbr,
                 team_logo, team_color)
                VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)
            """, (
                sport_key, r['poll'], today,
                r['rank'], r.get('previous', 0), r.get('points', 0),
                r.get('first_place_votes', 0), r.get('trend', '-'),
                r.get('record', ''), r['team'], r.get('team_abbr', ''),
                r.get('team_logo', ''), r.get('team_color', '#1a73e8'),
            ))
        conn.commit()
        conn.close()

    def get_rankings_history_df(self, sport_key: str, poll: str) -> pd.DataFrame:
        """All historical snapshots for a poll — used to chart rank movement over time."""
        conn = self.get_connection()
        df = pd.read_sql_query(
            """SELECT * FROM rankings_history
               WHERE sport_key=? AND poll=?
               ORDER BY snapshot_date, rank""",
            conn, params=(sport_key, poll))
        conn.close()
        return df

    def get_standings_df(self, category: str, sport: str) -> pd.DataFrame:
        """Returns standings parsed from cached ESPN standings API response."""
        cache_key = f"{category}_{sport}_standings"
        raw = self.get_cached_data(cache_key, 3600)
        if not raw:
            return pd.DataFrame()
        rows = []
        for conference in raw.get('children', []):
            conf_name = conference.get('name', '')
            abbrev    = conference.get('abbreviation', '')
            entries   = conference.get('standings', {}).get('entries', [])
            for entry in entries:
                team    = entry.get('team', {})
                stats   = {s['name']: s.get('value', s.get('displayValue', ''))
                           for s in entry.get('stats', [])}
                logos   = team.get('logos', [])
                logo    = logos[0].get('href', '') if logos else ''
                rows.append({
                    'conference':     conf_name,
                    'conf_abbr':      abbrev,
                    'team_id':        team.get('id', ''),
                    'team_abbr':      team.get('abbreviation', ''),
                    'team_name':      team.get('displayName', team.get('name', '')),
                    'team_logo':      logo,
                    'team_color':     '#' + (team.get('color') or '1a73e8'),
                    'wins':           float(stats.get('wins', 0)),
                    'losses':         float(stats.get('losses', 0)),
                    'ot_losses':      float(stats.get('otLosses', stats.get('OTLosses', 0))),
                    'win_pct':        float(stats.get('leagueWinPercent',
                                                       stats.get('winPercent', 0))),
                    'gb':             float(stats.get('gamesBehind', 0)),
                    'ppg':            float(stats.get('avgPointsFor', 0)),
                    'opp_ppg':        float(stats.get('avgPointsAgainst', 0)),
                    'diff':           float(stats.get('differential', 0)),
                    'playoff_seed':   float(stats.get('playoffSeed', 0)),
                    'clincher':       stats.get('clincher', ''),
                    'streak':         float(stats.get('streak', 0)),
                    'games_played':   float(stats.get('gamesPlayed', 0)),
                    'pts':            float(stats.get('points', stats.get('pts', 0))),
                })
        if not rows:
            return pd.DataFrame()
        return pd.DataFrame(rows)

    def get_cached_data(self, key: str, max_age: int) -> Optional[Dict]:
        conn = self.get_connection()
        c = conn.cursor()
        c.execute("SELECT response_json, fetched_at FROM api_cache WHERE endpoint_key = ?", (key,))
        row = c.fetchone()
        conn.close()
        if row:
            try:
                age = (datetime.now() - datetime.fromisoformat(row['fetched_at'])).total_seconds()
                if age < max_age:
                    return json.loads(row['response_json'])
            except Exception:
                pass
        return None

    def save_to_cache(self, key: str, data: Dict):
        conn = self.get_connection()
        c = conn.cursor()
        c.execute("""
            INSERT INTO api_cache (endpoint_key, response_json, fetched_at)
            VALUES (?, ?, ?)
            ON CONFLICT(endpoint_key) DO UPDATE SET
            response_json=excluded.response_json,
            fetched_at=excluded.fetched_at
        """, (key, json.dumps(data), datetime.now().isoformat()))
        conn.commit()
        conn.close()

    def get_config(self, key: str, default=None) -> Optional[str]:
        conn = self.get_connection()
        c = conn.cursor()
        c.execute("SELECT value FROM config WHERE key = ?", (key,))
        row = c.fetchone()
        conn.close()
        return row['value'] if row else default

    def update_config(self, key: str, value: str):
        conn = self.get_connection()
        c = conn.cursor()
        c.execute("INSERT OR REPLACE INTO config (key, value) VALUES (?, ?)", (key, value))
        conn.commit()
        conn.close()

    def get_games_df(self, category: str, sport: str,
                     date_str: Optional[str] = None) -> pd.DataFrame:
        conn = self.get_connection()
        query = "SELECT * FROM game_history WHERE category=? AND sport=?"
        params: list = [category, sport]
        if date_str:
            query += " AND event_date=?"
            params.append(date_str)
        query += " ORDER BY event_date DESC, id DESC"
        df = pd.read_sql_query(query, conn, params=params)
        conn.close()
        return df

    def get_season_games_df(self, category: str, sport: str,
                             season_year: int) -> pd.DataFrame:
        """Return ALL stored games for an entire season.

        ESPN season-year convention:
        - football:  season year = year season STARTS  (2025 → Aug 2025 – Mar 2026)
        - basketball/hockey: season year = year season ENDS (2026 → Oct 2025 – Jul 2026)
        - baseball:  season year = calendar year       (2026 → Feb 2026 – Nov 2026)
        - soccer:    season year = year season ENDS    (2026 → Jul 2025 – Jul 2026)
        """
        yr  = int(season_year)
        cat = category.lower()
        if cat == 'football':
            start, end = f'{yr}-08-01', f'{yr+1}-03-01'
        elif cat in ('basketball', 'hockey'):
            # season ENDS in yr, so it started in yr-1
            start, end = f'{yr-1}-09-01', f'{yr}-07-01'
        elif cat == 'baseball':
            start, end = f'{yr}-02-01', f'{yr}-11-30'
        else:
            # soccer: season ENDS in yr (e.g. EPL 2025-26 = season 2026)
            start, end = f'{yr-1}-07-01', f'{yr}-07-01'

        conn = self.get_connection()
        df = pd.read_sql_query(
            """SELECT * FROM game_history
               WHERE category=? AND sport=?
                 AND event_date >= ? AND event_date <= ?
               ORDER BY event_date DESC, id DESC""",
            conn, params=(category, sport, start, end)
        )
        conn.close()
        return df

    def get_most_recent_games_df(self, category: str, sport: str,
                                 limit: int = 30) -> pd.DataFrame:
        """Return the most recently stored games regardless of date."""
        conn = self.get_connection()
        df = pd.read_sql_query(
            """SELECT * FROM game_history
               WHERE category=? AND sport=?
               ORDER BY event_date DESC, id DESC LIMIT ?""",
            conn, params=(category, sport, limit)
        )
        conn.close()
        return df

    def get_latest_stored_date(self, category: str, sport: str) -> Optional[str]:
        """Most recent event_date stored for a sport (YYYY-MM-DD)."""
        conn = self.get_connection()
        c = conn.cursor()
        c.execute(
            "SELECT MAX(event_date) FROM game_history WHERE category=? AND sport=?",
            (category, sport)
        )
        row = c.fetchone()
        conn.close()
        return row[0] if row and row[0] else None

    def get_most_recent_games_df(self, category: str, sport: str,
                                 limit: int = 20) -> pd.DataFrame:
        """Return the most recently stored games for a sport regardless of date."""
        conn = self.get_connection()
        df = pd.read_sql_query(
            """
            SELECT * FROM game_history
            WHERE category=? AND sport=?
            ORDER BY event_date DESC, id DESC
            LIMIT ?
            """,
            conn, params=(category, sport, limit)
        )
        conn.close()
        return df

    def get_latest_stored_date(self, category: str, sport: str) -> Optional[str]:
        """Most recent event_date stored for a sport (YYYY-MM-DD)."""
        conn = self.get_connection()
        c = conn.cursor()
        c.execute(
            "SELECT MAX(event_date) FROM game_history WHERE category=? AND sport=?",
            (category, sport)
        )
        row = c.fetchone()
        conn.close()
        return row[0] if row and row[0] else None

    def get_team_history_df(self, team_name: str, category: str, sport: str) -> pd.DataFrame:
        conn = self.get_connection()
        query = """
            SELECT event_date, home_team, away_team, home_score, away_score,
                   home_winner, home_record, away_record, leaders_json,
                   status, note, broadcast, venue
            FROM game_history
            WHERE (home_team LIKE ? OR away_team LIKE ?)
              AND category=? AND sport=?
              AND status LIKE '%FINAL%'
            ORDER BY event_date DESC
        """
        df = pd.read_sql_query(query, conn,
                               params=(f"%{team_name}%", f"%{team_name}%", category, sport))
        conn.close()
        return df

    def get_team_schedule_games(self, category: str, sport: str,
                                team_id: str, season: int) -> pd.DataFrame:
        """Parse schedule cache for team_id/season into a tidy game DataFrame."""
        import json as _json
        cache_key = f"{category}_{sport}_sched_{team_id}_{season}"
        raw = self.get_cached_data(cache_key, 86400 * 365)  # return any cached value
        if not raw:
            return pd.DataFrame()
        events = raw.get('events', [])
        rows = []
        for ev in events:
            comps = ev.get('competitions', [])
            if not comps:
                continue
            comp = comps[0]
            status = comp.get('status', {})
            completed = status.get('type', {}).get('completed', False)
            competitors = comp.get('competitors', [])
            if len(competitors) < 2:
                continue
            # Identify home / away
            home_c = next((c for c in competitors if c.get('homeAway') == 'home'), competitors[0])
            away_c = next((c for c in competitors if c.get('homeAway') == 'away'), competitors[1])

            home_score_raw = home_c.get('score', {})
            away_score_raw = away_c.get('score', {})
            home_score = float(home_score_raw.get('value', 0) if isinstance(home_score_raw, dict)
                               else home_score_raw or 0)
            away_score = float(away_score_raw.get('value', 0) if isinstance(away_score_raw, dict)
                               else away_score_raw or 0)

            home_abbr = home_c.get('team', {}).get('abbreviation', '')
            away_abbr = away_c.get('team', {}).get('abbreviation', '')
            home_name = home_c.get('team', {}).get('displayName', home_abbr)
            away_name = away_c.get('team', {}).get('displayName', away_abbr)
            is_my_home = (str(home_c.get('team', {}).get('id', '')) == str(team_id))
            if is_my_home:
                my_score  = home_score
                opp_score = away_score
                opp_abbr  = away_abbr
            else:
                my_score  = away_score
                opp_score = home_score
                opp_abbr  = home_abbr

            winner = (home_c.get('winner', False) if is_my_home
                      else away_c.get('winner', False))

            venue_name = comp.get('venue', {}).get('fullName', '')
            broadcast = ', '.join(
                b.get('media', {}).get('shortName', '')
                for b in comp.get('broadcasts', [])
                if b.get('media', {}).get('shortName')
            )
            rows.append({
                'date':        ev.get('date', '')[:10],
                'name':        ev.get('shortName', ev.get('name', '')),
                'home_away':   'H' if is_my_home else 'A',
                'opponent':    opp_abbr,
                'my_score':    my_score,
                'opp_score':   opp_score,
                'diff':        my_score - opp_score,
                'won':         bool(winner),
                'completed':   completed,
                'venue':       venue_name,
                'broadcast':   broadcast,
            })
        df = pd.DataFrame(rows)
        if not df.empty:
            df['date'] = pd.to_datetime(df['date'], errors='coerce')
            df = df.sort_values('date').reset_index(drop=True)
        return df

    def get_teams_df(self, sport_key: str) -> pd.DataFrame:
        conn = self.get_connection()
        df = pd.read_sql_query(
            "SELECT * FROM teams_registry WHERE sport_key=? ORDER BY team_name",
            conn, params=(sport_key,))
        conn.close()
        return df

    def get_news_df(self, sport_key: str, limit: int = 20) -> pd.DataFrame:
        conn = self.get_connection()
        df = pd.read_sql_query(
            "SELECT * FROM news_archive WHERE sport_key=? ORDER BY published DESC LIMIT ?",
            conn, params=(sport_key, limit))
        conn.close()
        return df

    def get_rankings_df(self, sport_key: str) -> pd.DataFrame:
        conn = self.get_connection()
        df = pd.read_sql_query(
            "SELECT * FROM rankings WHERE sport_key=? ORDER BY poll, rank",
            conn, params=(sport_key,))
        conn.close()
        return df

    def save_team_detail(self, detail: Dict):
        conn = self.get_connection()
        c = conn.cursor()
        c.execute("""
            INSERT OR REPLACE INTO team_detail
            (sport_key, team_id, team_abbr, team_slug, team_name,
             color, alternate_color, logo_url, records_json, standing_summary,
             venue_name, venue_city, venue_state, venue_grass, venue_indoor,
             next_event_json, fetched_at)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, (
            detail['sport_key'], detail['team_id'], detail['team_abbr'],
            detail['team_slug'], detail['team_name'], detail['color'],
            detail['alternate_color'], detail['logo_url'], detail['records_json'],
            detail['standing_summary'], detail['venue_name'], detail['venue_city'],
            detail['venue_state'], detail['venue_grass'], detail['venue_indoor'],
            detail['next_event_json'], detail['fetched_at'],
        ))
        conn.commit()
        conn.close()

    def save_game_summary(self, summary: Dict):
        conn = self.get_connection()
        c = conn.cursor()
        c.execute("""
            INSERT OR REPLACE INTO game_summaries
            (event_id, sport_key, home_stats_json, away_stats_json, leaders_json,
             last_five_home, last_five_away, injuries_json, standings_json,
             venue_name, venue_city, odds_json,
             player_stats_json, team_stats_full_json, officials_json,
             videos_json, win_prob_json, scoring_plays_json, pickcenter_json,
             home_abbr, away_abbr,
             fetched_at)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, (
            summary['event_id'], summary['sport_key'],
            summary['home_stats_json'], summary['away_stats_json'],
            summary['leaders_json'], summary['last_five_home'],
            summary['last_five_away'], summary['injuries_json'],
            summary['standings_json'], summary['venue_name'],
            summary['venue_city'], summary['odds_json'],
            summary.get('player_stats_json', '[]'),
            summary.get('team_stats_full_json', '[]'),
            summary.get('officials_json', '[]'),
            summary.get('videos_json', '[]'),
            summary.get('win_prob_json', '[]'),
            summary.get('scoring_plays_json', '[]'),
            summary.get('pickcenter_json', '[]'),
            summary.get('home_abbr', ''),
            summary.get('away_abbr', ''),
            summary['fetched_at'],
        ))
        # Also flatten player_stats_json → player_game_stats for the Player Trends tab
        try:
            _ps = json.loads(summary.get('player_stats_json', '[]') or '[]')
            if _ps:
                # Look up the game_date from game_history
                _conn2 = self.get_connection()
                _row2 = _conn2.execute(
                    "SELECT event_date FROM game_history WHERE event_id=?",
                    (summary['event_id'],)
                ).fetchone()
                _gd = _row2[0] if _row2 else ''
                _conn2.close()
                self._flatten_player_stats(
                    summary['event_id'], summary['sport_key'], _gd, _ps
                )
        except Exception:
            pass
        conn.commit()
        conn.close()

    def _flatten_player_stats(self, event_id: str, sport_key: str,
                               game_date: str, player_stats: list):
        """Flatten player_stats_json list into player_game_stats rows."""
        conn = self.get_connection()
        c = conn.cursor()
        now = datetime.now().isoformat()
        rows = []
        for cat_block in player_stats:
            cat_name   = cat_block.get('category', cat_block.get('displayName', ''))
            labels     = cat_block.get('labels', [])
            team_abbr  = cat_block.get('team', '')
            for ath in cat_block.get('athletes', []):
                pid  = str(ath.get('id', ''))
                name = ath.get('name', '')
                hs   = ath.get('headshot', '')
                vals = ath.get('stats', [])
                if not name:
                    continue
                # Synthetic ID prevents UNIQUE(event_id,'',category) collision
                # when ESPN omits the athlete ID — gives each unique name its own key
                if not pid:
                    pid = '_pn_' + name.lower().replace(' ', '_')[:30]
                rows.append((
                    event_id, game_date, sport_key, team_abbr,
                    pid, name, hs,
                    cat_name,
                    json.dumps(labels),
                    json.dumps(vals),
                    now,
                ))
        if rows:
            # INSERT OR REPLACE so re-running after a fix updates stale rows
            c.executemany("""
                INSERT OR REPLACE INTO player_game_stats
                (event_id, game_date, sport_key, team_abbr, player_id,
                 player_name, headshot_url, category, stat_labels, stat_values, fetched_at)
                VALUES (?,?,?,?,?,?,?,?,?,?,?)
            """, rows)
            conn.commit()
        conn.close()

    def repopulate_player_game_stats(self) -> int:
        """Re-run _flatten_player_stats for every game_summary row whose event_id
        has no entries yet in player_game_stats.  Returns count of events processed."""
        conn = self.get_connection()
        rows = conn.execute("""
            SELECT gs.event_id, gs.sport_key, gs.player_stats_json,
                   COALESCE(h.event_date, '')
            FROM game_summaries gs
            LEFT JOIN game_history h ON h.event_id = gs.event_id
            WHERE gs.player_stats_json NOT IN ('[]', 'null', '')
              AND gs.player_stats_json IS NOT NULL
              AND gs.event_id NOT IN (
                  SELECT DISTINCT event_id FROM player_game_stats
              )
        """).fetchall()
        conn.close()
        count = 0
        for eid, sk, ps_json, gdate in rows:
            try:
                ps = json.loads(ps_json or '[]')
                if ps:
                    self._flatten_player_stats(eid, sk, gdate or '', ps)
                    count += 1
            except Exception:
                pass
        return count

    def get_game_summary(self, event_id: str) -> Optional[Dict]:
        """Return the stored game summary dict for event_id, or None if not found.

        Uses key-based access from sqlite3.Row (row_factory is already set in
        get_connection) so column order in SELECT * never matters — no off-by-one
        mapping between table columns and a hardcoded list.
        """
        conn = self.get_connection()
        row = conn.execute(
            "SELECT * FROM game_summaries WHERE event_id=?", (str(event_id),)
        ).fetchone()
        conn.close()
        if row is None:
            return None
        # sqlite3.Row supports key access; convert to plain dict by column name.
        return {k: row[k] for k in row.keys()}

    def get_player_game_log(self, sport_key: str, player_name: str,
                             player_id: str = '') -> pd.DataFrame:
        """Return per-game stat rows for a player.  Queries by player_id first
        (exact match) then falls back to display-name substring search so both
        properly-ID'd rows and legacy synthetic-ID rows are found."""
        conn = self.get_connection()
        if player_id:
            df = pd.read_sql_query("""
                SELECT p.event_id, p.game_date, p.team_abbr, p.player_name,
                       p.category, p.stat_labels, p.stat_values, p.headshot_url,
                       h.home_team, h.away_team, h.home_score, h.away_score, h.status
                FROM player_game_stats p
                LEFT JOIN game_history h ON h.event_id = p.event_id
                WHERE p.sport_key=?
                  AND (p.player_id=? OR LOWER(p.player_name) LIKE ?)
                ORDER BY p.game_date DESC
            """, conn, params=(sport_key, str(player_id), f'%{player_name.lower()}%'))
        else:
            df = pd.read_sql_query("""
                SELECT p.event_id, p.game_date, p.team_abbr, p.player_name,
                       p.category, p.stat_labels, p.stat_values, p.headshot_url,
                       h.home_team, h.away_team, h.home_score, h.away_score, h.status
                FROM player_game_stats p
                LEFT JOIN game_history h ON h.event_id = p.event_id
                WHERE p.sport_key=? AND LOWER(p.player_name) LIKE ?
                ORDER BY p.game_date DESC
            """, conn, params=(sport_key, f'%{player_name.lower()}%'))
        conn.close()
        return df

    def get_sport_player_names(self, sport_key: str) -> list:
        """Distinct player names stored for a sport (for autocomplete)."""
        conn = self.get_connection()
        rows = conn.execute(
            "SELECT DISTINCT player_name FROM player_game_stats WHERE sport_key=? ORDER BY player_name",
            (sport_key,)
        ).fetchall()
        conn.close()
        return [r[0] for r in rows]

    def get_category_leaders(self, sport_key: str, category: str,
                             stat_idx: int = 0, limit: int = 25) -> pd.DataFrame:
        """Return top players for a stat category from stored game-level data."""
        conn = self.get_connection()
        df = pd.read_sql_query("""
            SELECT player_name, team_abbr, headshot_url, COUNT(*) as games,
                   stat_labels, stat_values, game_date
            FROM player_game_stats
            WHERE sport_key=? AND category=?
            ORDER BY game_date DESC
        """, conn, params=(sport_key, category))
        conn.close()
        return df

    def get_available_categories(self, sport_key: str) -> list:
        """Distinct stat categories stored for a sport."""
        conn = self.get_connection()
        rows = conn.execute(
            "SELECT DISTINCT category FROM player_game_stats WHERE sport_key=? ORDER BY category",
            (sport_key,)
        ).fetchall()
        conn.close()
        return [r[0] for r in rows]

    def get_sport_team_abbrs(self, sport_key: str) -> list:
        """Distinct team abbreviations that have player stats stored for a sport."""
        conn = self.get_connection()
        try:
            rows = conn.execute(
                "SELECT DISTINCT team_abbr FROM player_game_stats WHERE sport_key=? ORDER BY team_abbr",
                (sport_key,)
            ).fetchall()
            return [r[0] for r in rows if r[0]]
        except Exception:
            return []
        finally:
            conn.close()

    def get_team_players_stats(self, sport_key: str, team_abbr: str) -> pd.DataFrame:
        """All player-game stat rows for a given team in a sport, newest first."""
        conn = self.get_connection()
        try:
            return pd.read_sql_query(
                """SELECT player_name, headshot_url, category,
                          stat_labels, stat_values, game_date
                   FROM player_game_stats
                   WHERE sport_key=? AND team_abbr=?
                   ORDER BY player_name, category, game_date DESC""",
                conn, params=(sport_key, team_abbr)
            )
        except Exception:
            return pd.DataFrame()
        finally:
            conn.close()

    def save_team_roster(self, sport_key: str, team_id: str, team_abbr: str,
                         position_groups: List[Dict]):
        """Bulk upsert roster rows from /teams/{abbr}/roster response."""
        conn = self.get_connection()
        c = conn.cursor()
        now = datetime.now().isoformat()
        rows = []
        for group in position_groups:
            group_name = group.get('position', '')
            for p in group.get('items', []):
                inj_list = p.get('injuries', [])
                inj_status = inj_list[0].get('status', '') if inj_list else ''
                pos_obj   = p.get('position') or {}
                pos_abbr  = pos_obj.get('abbreviation', '')
                pos_name  = pos_obj.get('displayName', pos_obj.get('name', ''))
                hs        = (p.get('headshot') or {}).get('href', '')
                exp       = (p.get('experience') or {}).get('years', 0)
                stat_obj  = p.get('status') or {}
                stat_name = stat_obj.get('name', 'Active')
                slug      = p.get('slug', '')
                rows.append((
                    sport_key, team_id, team_abbr, group_name,
                    str(p.get('id', '')),
                    p.get('displayName', ''),
                    p.get('firstName', ''),
                    p.get('lastName', ''),
                    p.get('jersey', ''),
                    pos_abbr,
                    pos_name,
                    p.get('displayHeight', ''),
                    p.get('displayWeight', ''),
                    int(p.get('age', 0) or 0),
                    (p.get('college') or {}).get('name', ''),
                    hs,
                    inj_status,
                    stat_name,
                    slug,
                    int(exp or 0),
                    now,
                ))
        c.executemany("""
            INSERT OR REPLACE INTO roster
            (sport_key, team_id, team_abbr, position_group, player_id,
             display_name, first_name, last_name, jersey, position,
             position_name, display_height, display_weight, age, college,
             headshot_url, injury_status, status_name, player_slug,
             experience, fetched_at)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, rows)
        conn.commit()
        conn.close()

    def get_roster_df(self, sport_key: str, team_id: str) -> pd.DataFrame:
        conn = self.get_connection()
        df = pd.read_sql_query(
            """SELECT * FROM roster WHERE sport_key=? AND team_id=?
               ORDER BY position_group, jersey""",
            conn, params=(sport_key, team_id)
        )
        conn.close()
        return df

    def get_team_detail_df(self, sport_key: str) -> pd.DataFrame:
        conn = self.get_connection()
        df = pd.read_sql_query(
            "SELECT * FROM team_detail WHERE sport_key=? ORDER BY team_name",
            conn, params=(sport_key,))
        conn.close()
        return df

    # ── PLAYER PROFILE METHODS ──────────────────────────────
    def save_player_profile(self, sport_key: str, player_id: str, player_name: str,
                             team_id: str, team_abbr: str, season_year: int,
                             profile: dict, sources: list):
        conn = self.get_connection()
        conn.execute("""
            INSERT OR REPLACE INTO player_profiles
            (sport_key, player_id, player_name, team_id, team_abbr,
             season_year, profile_json, sources, built_at)
            VALUES (?,?,?,?,?,?,?,?,?)
        """, (
            sport_key, str(player_id), player_name, str(team_id), team_abbr,
            int(season_year), json.dumps(profile), json.dumps(sources),
            datetime.now().isoformat(),
        ))
        conn.commit()
        conn.close()

    def get_player_profile(self, sport_key: str, player_id: str,
                            season_year: int) -> Optional[dict]:
        conn = self.get_connection()
        row = conn.execute(
            "SELECT * FROM player_profiles WHERE sport_key=? AND player_id=? AND season_year=?",
            (sport_key, str(player_id), int(season_year))
        ).fetchone()
        conn.close()
        if not row:
            return None
        d = dict(row)
        try:
            d['profile'] = json.loads(d['profile_json'])
        except Exception:
            d['profile'] = {}
        try:
            d['sources_list'] = json.loads(d['sources'])
        except Exception:
            d['sources_list'] = []
        return d

    def get_roster_teams_df(self, sport_key: str) -> pd.DataFrame:
        """Teams that have roster data loaded."""
        conn = self.get_connection()
        df = pd.read_sql_query(
            """SELECT DISTINCT team_id, team_abbr,
                      MIN(fetched_at) as fetched_at
               FROM roster WHERE sport_key=?
               GROUP BY team_id, team_abbr
               ORDER BY team_abbr""",
            conn, params=(sport_key,)
        )
        conn.close()
        # Merge team names from teams_registry where available
        teams_df = self.get_teams_df(sport_key)
        if not df.empty and not teams_df.empty:
            df = df.merge(
                teams_df[['team_id', 'team_name', 'logo_url']],
                on='team_id', how='left'
            )
        return df

    def get_team_roster_players(self, sport_key: str, team_id: str) -> pd.DataFrame:
        """All players in roster for a given team_id, ordered by position group."""
        conn = self.get_connection()
        df = pd.read_sql_query(
            """SELECT player_id, display_name, first_name, last_name, jersey,
                      position, position_name, position_group, headshot_url,
                      display_height, display_weight, age, college,
                      injury_status, status_name, player_slug, experience
               FROM roster WHERE sport_key=? AND team_id=?
               ORDER BY position_group, jersey""",
            conn, params=(sport_key, str(team_id))
        )
        conn.close()
        return df

    def get_player_pbp_mentions(self, sport_key: str, player_name: str) -> pd.DataFrame:
        """All PBP plays that mention a player by name (case-insensitive substring)."""
        conn = self.get_connection()
        df = pd.read_sql_query(
            """SELECT p.*, h.home_team, h.away_team, h.event_date, h.home_score, h.away_score
               FROM play_by_play p
               LEFT JOIN game_history h ON h.event_id = p.event_id
               WHERE p.sport_key=? AND LOWER(p.play_text) LIKE ?
               ORDER BY h.event_date DESC, p.sequence_num ASC""",
            conn, params=(sport_key, f'%{player_name.lower()}%')
        )
        conn.close()
        return df

    def get_game_events_for_player(self, sport_key: str, player_id: str,
                                    season_year: int) -> pd.DataFrame:
        """event_ids where this player appears in player_game_stats."""
        cat = sport_key.split('/')[0] if '/' in sport_key else ''
        conn = self.get_connection()
        df = pd.read_sql_query(
            """SELECT DISTINCT p.event_id, p.game_date, p.team_abbr,
                      h.home_team, h.away_team, h.home_score, h.away_score, h.status
               FROM player_game_stats p
               LEFT JOIN game_history h ON h.event_id = p.event_id
               WHERE p.sport_key=? AND p.player_id=?
               ORDER BY p.game_date DESC""",
            conn, params=(sport_key, str(player_id))
        )
        conn.close()
        return df


        conn = self.get_connection()
        c = conn.cursor()
        c.execute("SELECT * FROM game_summaries WHERE event_id=?", (event_id,))
        row = c.fetchone()
        conn.close()
        return dict(row) if row else None

    def is_game_final(self, event_id: str) -> bool:
        """True if we already have a FINAL result stored for this game."""
        conn = self.get_connection()
        c = conn.cursor()
        c.execute("SELECT status FROM game_history WHERE event_id=?", (event_id,))
        row = c.fetchone()
        conn.close()
        if row:
            return 'FINAL' in str(row['status']).upper()
        return False

    def get_job_stats(self) -> Dict:
        """Summary of coordinator job queue state (if coordinator is running)."""
        conn = self.get_connection()
        c = conn.cursor()
        try:
            rows  = c.execute("SELECT status, COUNT(*) cnt FROM jobs GROUP BY status").fetchall()
            nodes = c.execute("SELECT * FROM nodes ORDER BY last_seen DESC").fetchall()
            conn.close()
            return {
                'queue': {r['status']: r['cnt'] for r in rows},
                'nodes': [dict(n) for n in nodes],
            }
        except Exception:
            conn.close()
            return {'queue': {}, 'nodes': []}

    # ── Schema discovery methods ───────────────────────────────

    def save_schema_fields(self, sport_key: str, endpoint_type: str,
                           url: str, fields: Dict[str, tuple]):
        """Bulk-upsert discovered field paths for one endpoint fetch."""
        conn = self.get_connection()
        c = conn.cursor()
        now = datetime.now().isoformat()
        rows = [
            (sport_key, endpoint_type, url, path,
             vtype, example, path.count('.') + path.count('['), now)
            for path, (vtype, example) in fields.items()
        ]
        c.executemany("""
            INSERT OR REPLACE INTO field_schema
            (sport_key, endpoint_type, url, field_path,
             value_type, example_value, depth, discovered_at)
            VALUES (?,?,?,?,?,?,?,?)
        """, rows)
        conn.commit()
        conn.close()

    def get_schema_df(self, sport_key: str = None,
                      endpoint_type: str = None) -> pd.DataFrame:
        """Return all discovered fields, optionally filtered by sport or endpoint type."""
        conn = self.get_connection()
        q = "SELECT * FROM field_schema WHERE 1=1"
        params: list = []
        if sport_key:
            q += " AND sport_key=?"
            params.append(sport_key)
        if endpoint_type:
            q += " AND endpoint_type=?"
            params.append(endpoint_type)
        q += " ORDER BY sport_key, endpoint_type, depth, field_path"
        df = pd.read_sql_query(q, conn, params=params)
        conn.close()
        return df

    def get_schema_summary(self) -> pd.DataFrame:
        """Per (sport_key, endpoint_type): total field count and last crawl time."""
        conn = self.get_connection()
        df = pd.read_sql_query("""
            SELECT sport_key, endpoint_type,
                   COUNT(*) AS total_fields,
                   MAX(discovered_at) AS last_crawled
            FROM field_schema
            GROUP BY sport_key, endpoint_type
            ORDER BY sport_key, endpoint_type
        """, conn)
        conn.close()
        return df

    def clear_schema(self):
        """Delete all schema discovery data."""
        conn = self.get_connection()
        conn.execute("DELETE FROM field_schema")
        conn.commit()
        conn.close()

    # ── Play-by-play methods ───────────────────────────────────

    def save_play_by_play(self, event_id: str, sport_key: str, drives: List[Dict]):
        """Flatten drives+plays from ESPN summary API and bulk-insert."""
        conn = self.get_connection()
        c = conn.cursor()
        now = datetime.now().isoformat()
        rows = []
        for drive_num, drive in enumerate(drives):
            drive_id   = str(drive.get('id', ''))
            drive_desc = drive.get('description', '')
            drive_result = drive.get('shortDisplayResult', drive.get('result', ''))
            drive_yards  = int(drive.get('yards', 0) or 0)
            drive_score  = int(bool(drive.get('isScore', False)))
            off_plays    = int(drive.get('offensivePlays', 0) or 0)
            team_abbr    = (drive.get('team') or {}).get('abbreviation', '')
            for play in drive.get('plays', []):
                play_id  = str(play.get('id', ''))
                if not play_id:
                    continue
                ptype    = (play.get('type') or {})
                start    = (play.get('start') or {})
                rows.append((
                    event_id, sport_key,
                    drive_id, drive_num, drive_desc, drive_result,
                    drive_yards, drive_score, off_plays, team_abbr,
                    play_id,
                    int(play.get('sequenceNumber', 0) or 0),
                    ptype.get('text', ''),
                    ptype.get('abbreviation', ''),
                    play.get('text', ''),
                    int(play.get('awayScore', 0) or 0),
                    int(play.get('homeScore', 0) or 0),
                    int((play.get('period') or {}).get('number', 0) or 0),
                    (play.get('clock') or {}).get('displayValue', ''),
                    int(bool(play.get('scoringPlay', False))),
                    int(bool(play.get('isTurnover', False))),
                    int(play.get('statYardage', 0) or 0),
                    int(start.get('yardLine', 0) or 0),
                    int(start.get('yardsToEndzone', 0) or 0),
                    int(start.get('down', 0) or 0),
                    int(start.get('distance', 0) or 0),
                    start.get('downDistanceText', ''),
                    now,
                ))
        c.executemany("""
            INSERT OR IGNORE INTO play_by_play
            (event_id, sport_key, drive_id, drive_num, drive_desc, drive_result,
             drive_yards, drive_is_score, offensive_plays, team_abbr,
             play_id, sequence_num, play_type, play_abbr, play_text,
             away_score, home_score, period, clock,
             scoring_play, is_turnover, stat_yardage,
             yard_line, yards_to_endzone, down, distance, down_dist_text, fetched_at)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, rows)
        conn.commit()
        conn.close()

    def get_play_by_play(self, event_id: str) -> pd.DataFrame:
        """All plays for a game in drive/sequence order."""
        conn = self.get_connection()
        df = pd.read_sql_query(
            """SELECT * FROM play_by_play
               WHERE event_id=?
               ORDER BY drive_num, sequence_num""",
            conn, params=(event_id,)
        )
        conn.close()
        return df

    def get_scoring_plays(self, event_id: str) -> pd.DataFrame:
        """Scoring plays only for a game."""
        conn = self.get_connection()
        df = pd.read_sql_query(
            """SELECT period, clock, play_type, play_text,
                      team_abbr, away_score, home_score
               FROM play_by_play
               WHERE event_id=? AND scoring_play=1
               ORDER BY drive_num, sequence_num""",
            conn, params=(event_id,)
        )
        conn.close()
        return df

    def has_pbp(self, event_id: str) -> bool:
        """True if play-by-play has already been fetched for this game."""
        conn = self.get_connection()
        c = conn.cursor()
        c.execute("SELECT COUNT(*) FROM play_by_play WHERE event_id=?", (event_id,))
        n = c.fetchone()[0]
        conn.close()
        return n > 0

    def get_pbp_derived_stats(self, event_id: str) -> list:
        """Parse stored PBP play texts to produce per-player cumulative stats.

        Returns a list in the same format as parse_game_summary 'player_stats'
        so the Players tab render code can use it as a drop-in fallback when
        the boxscore player_stats_json is missing or empty (e.g. NFL games stored
        before schema additions, or games where ESPN omits the boxscore.players block).

        Patterns are tuned for NFL play texts but fall back gracefully for other
        sports — if no patterns match the plays will simply remain uncounted.
        """
        import re as _re
        from collections import defaultdict as _dd

        conn = self.get_connection()
        rows = conn.execute(
            """SELECT play_type, play_text, team_abbr
               FROM play_by_play
               WHERE event_id=?
               ORDER BY sequence_num""",
            (str(event_id),)
        ).fetchall()
        conn.close()

        if not rows:
            return []

        # ── accumulators (keyed by abbreviated name e.g. "S.Darnold") ──
        passing  = _dd(lambda: {'team': '', 'att': 0, 'cmp': 0, 'yds': 0,
                                 'td': 0, 'int': 0, 'sacked': 0})
        rushing  = _dd(lambda: {'team': '', 'car': 0, 'yds': 0, 'td': 0})
        receiving = _dd(lambda: {'team': '', 'rec': 0, 'yds': 0, 'td': 0})
        defense   = _dd(lambda: {'team': '', 'sacks': 0.0, 'int': 0, 'int_yds': 0})
        kicking   = _dd(lambda: {'team': '', 'fg_made': 0, 'fg_att': 0, 'long': 0})

        # abbreviated player name pattern — e.g. "S.Darnold", "K.Walker III"
        _P = r'([A-Z]\.[A-Za-z\'\-]+(?:\s+[A-Za-z\'\-]+(?:\s+[A-Z]{1,3})?)?)'

        def _yards(txt):
            m = _re.search(r'for (-?\d+) yards?', txt)
            return int(m.group(1)) if m else 0

        for play_type, txt, team in rows:
            if not txt:
                continue

            # strip formation prefix like "(Shotgun) " or "(No Huddle, Shotgun) "
            clean = _re.sub(r'^\([^)]+\)\s+', '', txt)

            # ── PASSING ──────────────────────────────────────────────────
            if play_type in ('Pass Reception', 'Pass Incompletion',
                             'Passing Touchdown',
                             'Pass Interception Return',
                             'Interception Return Touchdown',
                             'Sack', 'Sack Opp Fumble Recovery'):

                m_pr = _re.match(_P + r'\s+(?:pass|sacked)', clean)
                if not m_pr:
                    continue
                passer = m_pr.group(1)
                passing[passer]['team'] = passing[passer]['team'] or team

                if play_type in ('Pass Reception', 'Pass Incompletion',
                                 'Passing Touchdown',
                                 'Pass Interception Return',
                                 'Interception Return Touchdown'):
                    passing[passer]['att'] += 1

                if play_type == 'Pass Reception':
                    passing[passer]['cmp'] += 1
                    passing[passer]['yds'] += _yards(txt)
                    # receiver: "pass ... to R.Shaheed to NE 40 for 15 yards"
                    mR = _re.search(
                        r'pass\s+(?:short|deep|middle|complete to)?\s*'
                        r'(?:left|right|middle)?\s+(?:to\s+)?' + _P, clean)
                    if mR:
                        rec = mR.group(1)
                        receiving[rec]['team'] = receiving[rec]['team'] or team
                        receiving[rec]['rec'] += 1
                        receiving[rec]['yds'] += _yards(txt)

                elif play_type == 'Passing Touchdown':
                    passing[passer]['cmp'] += 1
                    passing[passer]['td']  += 1
                    passing[passer]['yds'] += _yards(txt)
                    mR = _re.search(r'to\s+' + _P + r'\s+for\s+\d+\s+yards?', clean)
                    if mR:
                        rec = mR.group(1)
                        receiving[rec]['team'] = receiving[rec]['team'] or team
                        receiving[rec]['rec'] += 1
                        receiving[rec]['td']  += 1
                        receiving[rec]['yds'] += _yards(txt)

                elif play_type in ('Pass Interception Return',
                                   'Interception Return Touchdown'):
                    passing[passer]['int'] += 1
                    mI = _re.search(r'INTERCEPTED by\s+' + _P, txt)
                    if mI:
                        defp = mI.group(1)
                        defense[defp]['team'] = defense[defp]['team'] or team
                        defense[defp]['int'] += 1
                        defense[defp]['int_yds'] += max(0, _yards(txt))

                elif play_type in ('Sack', 'Sack Opp Fumble Recovery'):
                    passing[passer]['sacked'] += 1
                    mS = _re.search(r'sacked at .+? \(([^)]+)\)', txt)
                    if mS:
                        sackers = _re.findall(
                            r'[A-Z]\.[A-Za-z\'\-]+(?:\s+[A-Za-z\'\-]+)?',
                            mS.group(1))
                        share = 1.0 / len(sackers) if sackers else 1.0
                        for s in sackers:
                            defense[s]['sacks'] += share

            # ── RUSHING ──────────────────────────────────────────────────
            elif play_type in ('Rush', 'Rushing Touchdown'):
                mRu = _re.match(
                    _P + r'\s+(?:up|left|right|ran|scrambles|rush|dive)', clean)
                if not mRu:
                    # try stat_yardage approach (play may not match pattern)
                    continue
                rusher = mRu.group(1)
                rushing[rusher]['team'] = rushing[rusher]['team'] or team
                rushing[rusher]['car'] += 1
                yds_r = _yards(txt)
                if 'no gain' in txt.lower():
                    yds_r = 0
                rushing[rusher]['yds'] += yds_r
                if 'TOUCHDOWN' in txt and 'NULLIFIED' not in txt:
                    rushing[rusher]['td'] += 1

            # ── KICKING ──────────────────────────────────────────────────
            elif play_type == 'Field Goal Good':
                mFG = _re.match(_P + r'\s+(\d+) yard field goal is GOOD', clean)
                if mFG:
                    kicker = mFG.group(1)
                    dist   = int(mFG.group(2))
                    kicking[kicker]['team'] = kicking[kicker]['team'] or team
                    kicking[kicker]['fg_made'] += 1
                    kicking[kicker]['fg_att']  += 1
                    kicking[kicker]['long'] = max(kicking[kicker]['long'], dist)

            elif play_type == 'Field Goal No Good':
                mFG = _re.match(_P + r'\s+\d+ yard field goal', clean)
                if mFG:
                    kicker = mFG.group(1)
                    kicking[kicker]['team'] = kicking[kicker]['team'] or team
                    kicking[kicker]['fg_att'] += 1

        # ── assemble player_stats blocks ─────────────────────────────────
        result = []

        def _ath(name, stats_vals):
            return {'name': name, 'id': '', 'jersey': '', 'headshot': '',
                    'stats': stats_vals}

        # Passing
        pass_athletes = sorted(
            [{'name': n, 'team': v['team'],
              'stats': [f"{v['cmp']}/{v['att']}", str(v['yds']),
                        str(round(v['yds'] / v['att'], 1)) if v['att'] else '0.0',
                        str(v['td']), str(v['int'])]}
             for n, v in passing.items() if v['att'] > 0],
            key=lambda x: int(x['stats'][1]), reverse=True
        )
        for ath in pass_athletes:
            result.append({
                'team': ath['team'], 'category': 'passing',
                'displayName': 'Passing',
                'labels': ['C/ATT', 'YDS', 'AVG', 'TD', 'INT'],
                'athletes': [_ath(ath['name'], ath['stats'])],
                'totals': []
            })

        # Rushing — merge into one block per team
        rush_athletes = sorted(
            [{'name': n, 'team': v['team'],
              'stats': [str(v['car']), str(v['yds']),
                        str(round(v['yds'] / v['car'], 1)) if v['car'] else '0.0',
                        str(v['td'])]}
             for n, v in rushing.items() if v['car'] > 0],
            key=lambda x: int(x['stats'][1]), reverse=True
        )
        if rush_athletes:
            teams_rush = list(dict.fromkeys(a['team'] for a in rush_athletes))
            for t in teams_rush:
                block_aths = [_ath(a['name'], a['stats'])
                              for a in rush_athletes if a['team'] == t]
                result.append({'team': t, 'category': 'rushing',
                               'displayName': 'Rushing',
                               'labels': ['CAR', 'YDS', 'AVG', 'TD'],
                               'athletes': block_aths, 'totals': []})

        # Receiving — merge into one block per team
        rec_athletes = sorted(
            [{'name': n, 'team': v['team'],
              'stats': [str(v['rec']), str(v['yds']),
                        str(round(v['yds'] / v['rec'], 1)) if v['rec'] else '0.0',
                        str(v['td'])]}
             for n, v in receiving.items() if v['rec'] > 0],
            key=lambda x: int(x['stats'][1]), reverse=True
        )
        if rec_athletes:
            teams_rec = list(dict.fromkeys(a['team'] for a in rec_athletes))
            for t in teams_rec:
                block_aths = [_ath(a['name'], a['stats'])
                              for a in rec_athletes if a['team'] == t]
                result.append({'team': t, 'category': 'receiving',
                               'displayName': 'Receiving',
                               'labels': ['REC', 'YDS', 'AVG', 'TD'],
                               'athletes': block_aths, 'totals': []})

        # Defense (sacks + interceptions)
        def_athletes = sorted(
            [{'name': n, 'team': v['team'],
              'stats': [str(v.get('sacks', 0.0)), str(v['int']), str(v['int_yds'])]}
             for n, v in defense.items()
             if v.get('sacks', 0) > 0 or v['int'] > 0],
            key=lambda x: float(x['stats'][0]), reverse=True
        )
        if def_athletes:
            teams_def = list(dict.fromkeys(a['team'] for a in def_athletes))
            for t in teams_def:
                block_aths = [_ath(a['name'], a['stats'])
                              for a in def_athletes if a['team'] == t]
                result.append({'team': t, 'category': 'defensive',
                               'displayName': 'Defense (PBP)',
                               'labels': ['SACKS', 'INT', 'INT YDS'],
                               'athletes': block_aths, 'totals': []})

        # Kicking
        kick_athletes = sorted(
            [{'name': n, 'team': v['team'],
              'stats': [f"{v['fg_made']}/{v['fg_att']}", str(v['long'])]}
             for n, v in kicking.items() if v['fg_att'] > 0],
            key=lambda x: int(x['stats'][0].split('/')[0]), reverse=True
        )
        if kick_athletes:
            teams_kick = list(dict.fromkeys(a['team'] for a in kick_athletes))
            for t in teams_kick:
                block_aths = [_ath(a['name'], a['stats'])
                              for a in kick_athletes if a['team'] == t]
                result.append({'team': t, 'category': 'kicking',
                               'displayName': 'Kicking',
                               'labels': ['FG', 'LONG'],
                               'athletes': block_aths, 'totals': []})

        return result


# ─────────────────────────────────────────────────────────────
# 3. WORKER ENGINE
# ─────────────────────────────────────────────────────────────

class ESPNWorker:
    def __init__(self, db: SportsDB):
        self.db = db
        self.session = requests.Session()
        self.session.headers.update({'User-Agent': 'Mozilla/5.0 (TrulySporting Analytics)'})
        self.running = False
        self.thread = None
        self.last_error = ''

    @staticmethod
    def _espn_season_year(category: str) -> int:
        """Return the correct ESPN season year for the current date.

        Football, basketball, and hockey seasons start in the latter half of
        the calendar year, so during Jan-Jul the most-recent completed season
        belongs to *last* year (e.g. April 2026 → 2025 NFL/NBA/NHL season).
        Baseball and soccer use the current calendar year.
        """
        import datetime as _dt
        now = _dt.datetime.now()
        yr  = now.year
        if category.lower() == 'football':
            # Football year = season-start year (NFL 2025 ran Aug 2025 – Feb 2026)
            return yr - 1 if now.month < 8 else yr
        elif category.lower() in ('basketball', 'hockey'):
            # End-year convention: "season 2026" = Oct 2025 – Jun 2026
            # Jan-Sep → season ending this year is active → return yr
            # Oct-Dec → new season just started, ends next year → return yr + 1
            return yr if now.month <= 9 else yr + 1
        return yr

    @staticmethod
    def _season_label(category: str, year: int) -> str:
        """Convert an ESPN season integer to a human-readable range label.

        football   2025 → '2025–2026'  (start-year; season spans two calendar years)
        basketball 2026 → '2025–2026'  (end-year  ; season started previous year)
        hockey     2026 → '2025–2026'  (end-year)
        soccer     2026 → '2025–2026'  (end-year)
        baseball   2026 → '2026'       (single calendar year)
        """
        cat = category.lower()
        if cat == 'football':
            return f"{year}\u2013{year + 1}"
        elif cat == 'baseball':
            return str(year)
        else:
            # basketball, hockey, soccer — end-year convention
            return f"{year - 1}\u2013{year}"

    def fetch_and_process(self, category: str, sport: str, endpoint_type: str,
                          force_refresh: bool = False,
                          params: Optional[Dict] = None) -> Optional[Dict]:
        cache_key = f"{category}_{sport}_{endpoint_type}"
        if params:
            cache_key += '_' + '_'.join(f"{k}={v}" for k, v in sorted(params.items()))

        url = EndpointRegistry.get_url(category, sport, endpoint_type)
        if not url:
            return None

        interval = int(self.db.get_config('default_refresh_interval', 3600))
        # Use short cache for current (non-dated) scoreboard so live games refresh quickly
        if endpoint_type == 'scoreboard' and not params:
            interval = 60

        if not force_refresh:
            cached = self.db.get_cached_data(cache_key, interval)
            if cached:
                return cached

        try:
            resp = self.session.get(url, params=params or {}, timeout=15)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)

            sport_key = f"{category}/{sport}"
            if endpoint_type == 'scoreboard':
                games = ESPNParser.parse_scoreboard(data, category, sport)
                self.db.save_games(games)
            elif endpoint_type == 'teams':
                teams = ESPNParser.parse_team_details(data, sport_key)
                self.db.save_teams(teams)
            elif endpoint_type == 'news':
                articles = ESPNParser.parse_news(data)
                self.db.save_news(sport_key, articles)
            elif endpoint_type == 'rankings':
                rankings = ESPNParser.parse_rankings(data)
                self.db.save_rankings(sport_key, rankings)
                self.db.save_rankings_snapshot(sport_key, rankings)
            elif endpoint_type == 'team_detail':
                detail = ESPNParser.parse_single_team(data, sport_key)
                if detail:
                    self.db.save_team_detail(detail)
            elif endpoint_type == 'summary':
                summary = ESPNParser.parse_game_summary(data, sport_key)
                if summary:
                    self.db.save_game_summary(summary)

            self.last_error = ''
            return data

        except Exception as e:
            self.last_error = str(e)
            print(f"Error fetching {cache_key}: {e}")
            return None

    def fetch_date_scoreboard(self, category: str, sport: str, date_str: str) -> Optional[Dict]:
        """Fetch scoreboard for a specific date (YYYYMMDD)."""
        return self.fetch_and_process(
            category, sport, 'scoreboard',
            force_refresh=True, params={'dates': date_str}
        )

    @staticmethod
    def _season_date_ranges(category: str, sport: str, season_year: int) -> list:
        """Return list of (label, params_dict) chunks that together cover a full season.

        ESPN season-year convention:
        - football:  season year = year season STARTS  → pass season=yr to ESPN API
        - basketball/hockey: season year = year season ENDS → calendar months start in yr-1
        - baseball:  season year = calendar year
        - soccer:    season year = year season ENDS    → calendar months start in yr-1

        Football uses ESPN's week+seasontype params (most reliable).
        All other sports use monthly date-range chunks (dates=STARTYYYYMMDD-ENDYYYYMMDD).
        """
        import calendar as _cal
        yr   = int(season_year)
        cat  = category.lower()
        chunks = []

        if cat == 'football':
            # Pre-season weeks 1-4
            for w in range(1, 5):
                chunks.append((f'Pre-Week {w}',
                                {'season': yr, 'seasontype': 1, 'week': w, 'limit': 100}))
            # Regular season weeks 1-18
            for w in range(1, 19):
                chunks.append((f'Week {w}',
                                {'season': yr, 'seasontype': 2, 'week': w, 'limit': 100}))
            # Post-season weeks 1-5 (Wild Card → Divisional → Championship → Pro Bowl → Super Bowl)
            for w in range(1, 6):
                chunks.append((f'Post-Week {w}',
                                {'season': yr, 'seasontype': 3, 'week': w, 'limit': 100}))
        else:
            if cat in ('basketball', 'hockey'):
                # season 2026 = Oct 2025 – Jun 2026
                months = [(yr - 1, m) for m in range(10, 13)] + \
                         [(yr, m) for m in range(1, 8)]
            elif cat == 'baseball':
                months = [(yr, m) for m in range(3, 11)]
            else:
                # Soccer: season 2026 = Jul 2025 – Jun 2026
                months = [(yr - 1, m) for m in range(7, 13)] + \
                         [(yr, m) for m in range(1, 8)]

            for m_yr, mo in months:
                _, last_day = _cal.monthrange(m_yr, mo)
                start = f'{m_yr}{mo:02d}01'
                end   = f'{m_yr}{mo:02d}{last_day:02d}'
                label = f'{m_yr}-{mo:02d}'
                chunks.append((label, {'dates': f'{start}-{end}', 'limit': 200}))

        return chunks

    def fetch_full_season(self, category: str, sport: str, season_year: int,
                          on_progress=None) -> int:
        """Fetch every game of a season from ESPN and persist to game_history.

        on_progress(done, total, label) is called after each chunk if provided.
        Returns the number of chunks successfully fetched.
        """
        chunks  = self._season_date_ranges(category, sport, season_year)
        total   = len(chunks)
        fetched = 0
        for i, (label, params) in enumerate(chunks):
            try:
                self.fetch_and_process(category, sport, 'scoreboard',
                                       force_refresh=True, params=params)
                fetched += 1
            except Exception as _e:
                self.last_error = str(_e)
            if on_progress:
                on_progress(i + 1, total, label)
        return fetched
    def fetch_team_detail(self, category: str, sport: str,
                          team_id: str, team_slug: str = '') -> Optional[Dict]:
        """Fetch extended single-team data.
        Uses numeric team_id (works for all sports).
        Falls back to slug only when team_id is empty.
        """
        sport_key = f'{category}/{sport}'
        # Prefer numeric id — works for every ESPN sport.
        # Slug-based URLs only work for football; basketball/MLB/NHL/soccer return 400.
        path = str(team_id).strip() if str(team_id).strip() else str(team_slug).strip()
        if not path:
            return None
        url = f"{EndpointRegistry.BASE_URL}/{category}/{sport}/teams/{path}"
        cache_key = f"{category}_{sport}_team_{path}"
        # Cache for 7 days
        cached = self.db.get_cached_data(cache_key, 604800)
        if cached:
            detail = ESPNParser.parse_single_team(cached, sport_key)
            if detail:
                self.db.save_team_detail(detail)
            return cached
        try:
            resp = self.session.get(url, timeout=15)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)
            detail = ESPNParser.parse_single_team(data, sport_key)
            if detail:
                self.db.save_team_detail(detail)
            return data
        except Exception as e:
            self.last_error = str(e)
            return None

    def fetch_team_roster(self, category: str, sport: str,
                          team_id: str, team_abbr: str) -> Optional[Dict]:
        """Fetch full player roster from /teams/{team_id}/roster"""
        sport_key = f'{category}/{sport}'
        url = f"{EndpointRegistry.BASE_URL}/{category}/{sport}/teams/{team_id}/roster"
        cache_key = f"{category}_{sport}_roster_{team_id}"
        # Cache for 1 day
        cached = self.db.get_cached_data(cache_key, 86400)
        if cached:
            athletes = cached.get('athletes', [])
            if athletes:
                team_id_actual = cached.get('team', {}).get('id', team_id)
                self.db.save_team_roster(sport_key, team_id_actual, team_abbr, athletes)
            return cached
        try:
            resp = self.session.get(url, timeout=15)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)
            athletes = data.get('athletes', [])
            if athletes:
                team_id_actual = data.get('team', {}).get('id', team_id)
                self.db.save_team_roster(sport_key, team_id_actual, team_abbr, athletes)
            return data
        except Exception as e:
            self.last_error = str(e)
            return None

    def fetch_team_schedule(self, category: str, sport: str,
                             team_id: str, season: int) -> Optional[Dict]:
        """Fetch a team's full season schedule/results from /teams/{id}/schedule?season=YYYY.
        Returns the raw API dict; caller can re-fetch with force_refresh=True."""
        cache_key = f"{category}_{sport}_sched_{team_id}_{season}"
        cached = self.db.get_cached_data(cache_key, 3600)
        if cached:
            return cached
        url = f"{EndpointRegistry.BASE_URL}/{category}/{sport}/teams/{team_id}/schedule"
        try:
            resp = self.session.get(url, params={'season': str(season)}, timeout=20)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)
            self.last_error = ''
            return data
        except Exception as e:
            self.last_error = str(e)
            return None

    def fetch_standings(self, category: str, sport: str) -> Optional[Dict]:
        """Fetch league standings from the ESPN standings API (NBA/NFL/MLB/NHL/soccer)."""
        cache_key = f"{category}_{sport}_standings"
        cached = self.db.get_cached_data(cache_key, 3600)
        if cached:
            return cached
        url = f"https://site.web.api.espn.com/apis/v2/sports/{category}/{sport}/standings"
        try:
            resp = self.session.get(url, timeout=15)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)
            self.last_error = ''
            return data
        except Exception as e:
            self.last_error = str(e)
            return None

    # ── PLAYER-SPECIFIC ESPN FETCH METHODS ───────────────────

    def fetch_athlete_info(self, category: str, sport: str,
                            athlete_id: str) -> Optional[Dict]:
        """Fetch athlete bio from /athletes/{id}.
        Returns name, DOB, height, weight, position, college, headshot etc."""
        cache_key = f"{category}_{sport}_athleteinfo_{athlete_id}"
        cached = self.db.get_cached_data(cache_key, 86400 * 7)  # cache 1 week
        if cached:
            return cached
        url = f"{EndpointRegistry.BASE_URL}/{category}/{sport}/athletes/{athlete_id}"
        try:
            resp = self.session.get(url, timeout=15)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)
            self.last_error = ''
            return data
        except Exception as e:
            self.last_error = str(e)
            return None

    def fetch_athlete_season_stats(self, category: str, sport: str,
                                    athlete_id: str,
                                    season: Optional[int] = None) -> Optional[Dict]:
        """Fetch season-level stat totals/averages from /athletes/{id}/statistics.
        Returns categories with labels + values (e.g. PPG, RPG, APG for NBA)."""
        import datetime as _dt
        yr = season or _dt.datetime.now().year
        cache_key = f"{category}_{sport}_athletestats_{athlete_id}_{yr}"
        cached = self.db.get_cached_data(cache_key, 3600 * 6)
        if cached:
            return cached
        url = f"{EndpointRegistry.BASE_URL}/{category}/{sport}/athletes/{athlete_id}/statistics"
        try:
            resp = self.session.get(url, params={'season': yr}, timeout=15)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)
            self.last_error = ''
            return data
        except Exception as e:
            self.last_error = str(e)
            return None

    def fetch_athlete_splits(self, category: str, sport: str,
                              athlete_id: str,
                              season: Optional[int] = None) -> Optional[Dict]:
        """Fetch situational splits from /athletes/{id}/splits?season=YYYY.
        Returns home/away, win/loss, by-month, vs-opponent splits."""
        import datetime as _dt
        yr = season or _dt.datetime.now().year
        cache_key = f"{category}_{sport}_athletesplits_{athlete_id}_{yr}"
        cached = self.db.get_cached_data(cache_key, 3600 * 6)
        if cached:
            return cached
        url = f"{EndpointRegistry.BASE_URL}/{category}/{sport}/athletes/{athlete_id}/splits"
        try:
            resp = self.session.get(url, params={'season': yr}, timeout=15)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)
            self.last_error = ''
            return data
        except Exception as e:
            self.last_error = str(e)
            return None

    def build_and_cache_player_profile(self, category: str, sport: str,
                                        player_id: str, player_name: str,
                                        team_id: str, team_abbr: str,
                                        season_year: int) -> dict:
        """Aggregate local DB data into a unified player profile dict and persist it.
        Uses only data already in the local SQLite DB — no ESPN API calls.
        Sources: roster (bio/headshot), player_game_stats (game log), play_by_play (PBP).
        """
        sport_key = f'{category}/{sport}'
        profile: dict = {
            'player_id':   str(player_id),
            'player_name': player_name,
            'team_id':     str(team_id),
            'team_abbr':   team_abbr,
            'season_year': season_year,
            'sport_key':   sport_key,
        }
        sources: list = []

        # 1. Bio from roster table (already populated when roster was fetched)
        try:
            _conn = self.db.get_connection()
            _rrow = _conn.execute(
                """SELECT display_name, first_name, last_name, jersey, position,
                          position_name, display_height, display_weight, age, college,
                          experience, headshot_url, injury_status, status_name
                   FROM roster WHERE sport_key=? AND player_id=? LIMIT 1""",
                (sport_key, str(player_id))
            ).fetchone()
            _conn.close()
        except Exception:
            _rrow = None

        if _rrow:
            _inj = _rrow[12] or ''
            profile['bio'] = {
                'display_name':  _rrow[0] or player_name,
                'first_name':    _rrow[1] or '',
                'last_name':     _rrow[2] or '',
                'jersey':        _rrow[3] or '',
                'position':      _rrow[4] or '',
                'position_name': _rrow[5] or '',
                'height':        _rrow[6] or '',
                'weight':        _rrow[7] or '',
                'age':           _rrow[8] or '',
                'college':       _rrow[9] or '',
                'experience':    _rrow[10] or '',
                'headshot':      _rrow[11] or '',
                'status':        (f'Injured: {_inj}' if _inj else (_rrow[13] or 'Active')),
            }
            sources.append('roster')
        else:
            profile['bio'] = {'display_name': player_name, 'headshot': ''}

        # 2. Boxscore game log from player_game_stats table
        pgs_df = self.db.get_player_game_log(sport_key, player_name, str(player_id))
        if not pgs_df.empty:
            import json as _j
            rows = []
            for _, row in pgs_df.iterrows():
                try:
                    labels = _j.loads(row['stat_labels']) if row['stat_labels'] else []
                    vals   = _j.loads(row['stat_values']) if row['stat_values'] else []
                except Exception:
                    labels, vals = [], []
                rows.append({
                    'event_id':    row['event_id'],
                    'game_date':   str(row['game_date']),
                    'team_abbr':   row['team_abbr'],
                    'category':    row['category'],
                    'home_team':   row.get('home_team', ''),
                    'away_team':   row.get('away_team', ''),
                    'stat_labels': labels,
                    'stat_values': vals,
                })
            profile['boxscore_gamelog'] = rows
            sources.append('player_game_stats')

        # 3. PBP mentions
        pbp_df = self.db.get_player_pbp_mentions(sport_key, player_name)
        if not pbp_df.empty:
            _pbp_cols = [c for c in [
                'event_id', 'event_date', 'period', 'clock',
                'play_text', 'play_type', 'scoring_play',
                'away_score', 'home_score', 'home_team', 'away_team',
            ] if c in pbp_df.columns]
            profile['pbp_mentions'] = pbp_df[_pbp_cols].to_dict('records')
            profile['pbp_mention_count'] = len(pbp_df)
            sources.append('play_by_play')

        self.db.save_player_profile(
            sport_key, str(player_id), player_name,
            str(team_id), team_abbr, season_year, profile, sources
        )
        self.last_error = ''
        return profile

    def fetch_league_leaders(self, category: str, sport: str,
                              season: Optional[int] = None) -> Optional[Dict]:
        """Fetch league statistical leaders for the current/specified season.
        Uses ESPN's /athletes/statistics endpoint which returns per-category
        top performers (scoring, rebounds, assists, ERA, etc.)."""
        import datetime as _dt
        yr = season or _dt.datetime.now().year
        cache_key = f"{category}_{sport}_leaders_{yr}"
        cached = self.db.get_cached_data(cache_key, 3600)
        if cached:
            return cached
        # ESPN stats leaders endpoint — works for NBA/NHL/MLB/NFL/soccer
        url = f"{EndpointRegistry.BASE_URL}/{category}/{sport}/athletes/statistics"
        try:
            resp = self.session.get(url, params={'season': yr, 'limit': 50}, timeout=20)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)
            self.last_error = ''
            return data
        except Exception as e:
            self.last_error = str(e)
            return None

    def fetch_athlete_gamelog(self, category: str, sport: str,
                               athlete_id: str, season: Optional[int] = None) -> Optional[Dict]:
        """Fetch a single athlete's game-by-game log for the season.
        Uses ESPN's /athletes/{id}/gamelog endpoint."""
        import datetime as _dt
        yr = season or _dt.datetime.now().year
        cache_key = f"{category}_{sport}_gamelog_{athlete_id}_{yr}"
        cached = self.db.get_cached_data(cache_key, 3600)
        if cached:
            return cached
        url = f"{EndpointRegistry.BASE_URL}/{category}/{sport}/athletes/{athlete_id}/gamelog"
        try:
            resp = self.session.get(url, params={'season': yr}, timeout=20)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)
            self.last_error = ''
            return data
        except Exception as e:
            self.last_error = str(e)
            return None

    def fetch_game_summary(self, category: str, sport: str, event_id: str) -> Optional[Dict]:
        """Fetch box score / summary for a completed game."""
        sport_key = f'{category}/{sport}'
        if not event_id or not str(event_id).strip():
            self.last_error = 'fetch_game_summary called with empty event_id'
            return None
        url = f"{EndpointRegistry.BASE_URL}/{category}/{sport}/summary"
        cache_key = f"{category}_{sport}_summary_{event_id}"
        def _extract_and_save_pbp(raw: dict):
            """Extract PBP from raw ESPN summary JSON and persist if not already stored."""
            if self.db.has_pbp(event_id):
                return
            drives = (raw.get('drives') or {}).get('previous', [])
            if drives:
                self.db.save_play_by_play(event_id, sport_key, drives)
            else:
                flat_plays = raw.get('plays') or raw.get('scoringPlays') or []
                if flat_plays:
                    self.db.save_play_by_play(
                        event_id, sport_key,
                        [{'plays': flat_plays, 'description': 'Plays'}]
                    )

        # Final games only need to be fetched once — but still extract PBP and
        # player_game_stats from cache if they were missed on earlier runs
        if self.db.is_game_final(event_id):
            cached = self.db.get_cached_data(cache_key, 86400 * 365)
            if cached:
                _extract_and_save_pbp(cached)
                # Back-fill player_game_stats if this event hasn't been processed yet
                conn_chk = self.db.get_connection()
                _has_pgs = conn_chk.execute(
                    'SELECT 1 FROM player_game_stats WHERE event_id=? LIMIT 1',
                    (str(event_id),)
                ).fetchone()
                conn_chk.close()
                if not _has_pgs:
                    _sum2 = ESPNParser.parse_game_summary(cached, sport_key)
                    if _sum2:
                        self.db.save_game_summary(_sum2)
                return cached
        try:
            resp = self.session.get(url, params={'event': str(event_id)}, timeout=20)
            resp.raise_for_status()
            data = resp.json()
            self.db.save_to_cache(cache_key, data)
            summary = ESPNParser.parse_game_summary(data, sport_key)
            if summary:
                self.db.save_game_summary(summary)
            # Extract play-by-play (football uses drives; all other sports use flat plays list)
            _extract_and_save_pbp(data)
            return data
        except Exception as e:
            self.last_error = str(e)
            return None

    def start(self):
        if self.running:
            return
        self.running = True
        self.thread = threading.Thread(target=self._loop, daemon=True)
        self.thread.start()

    def _loop(self):
        import datetime as _dt
        while self.running:
            try:
                active_eps = json.loads(self.db.get_config('active_endpoints', '[]'))
                for ep in active_eps:
                    if not self.running:
                        break
                    cat, sport = ep.split('/')
                    self.fetch_and_process(cat, sport, 'scoreboard')
                    time.sleep(2)
                    self.fetch_and_process(cat, sport, 'teams')
                    time.sleep(2)
                    self.fetch_and_process(cat, sport, 'news')
                    time.sleep(2)
                    # Rankings only where supported
                    if EndpointRegistry.get_url(cat, sport, 'rankings'):
                        self.fetch_and_process(cat, sport, 'rankings')
                        time.sleep(2)
                    # League leaders / player stats (best-effort, non-blocking)
                    try:
                        self.fetch_league_leaders(cat, sport,
                                                  ESPNWorker._espn_season_year(cat))
                    except Exception:
                        pass
                    time.sleep(2)

                time.sleep(int(self.db.get_config('default_refresh_interval', 3600)))
            except Exception as e:
                self.last_error = str(e)
                print(f"Worker Error: {e}")
                time.sleep(60)

    def stop(self):
        self.running = False


# ─────────────────────────────────────────────────────────────
# 4. SCHEMA CRAWLER
# ─────────────────────────────────────────────────────────────

class SchemaCrawler:
    """
    Iterates all endpoints from EndpointRegistry (plus team_detail and summary
    with example IDs), fetches live data, recursively flattens each JSON response
    into dot-notation field paths, and stores the full catalog in field_schema.

    Every tab can query field_schema to see what ESPN actually returns —
    including fields the parsers don't yet extract.
    """

    # Example team slugs for /teams/:slug endpoint
    EXAMPLE_TEAMS = {
        'football/nfl':                         'ne',
        'football/college-football':            'gt',
        'basketball/nba':                       'lal',
        'basketball/wnba':                      'sea',
        'basketball/mens-college-basketball':   'kentucky',
        'basketball/womens-college-basketball': 'uconn',
        'baseball/mlb':                         'nyy',
        'hockey/nhl':                           'bos',
        'soccer/eng.1':                         'arsenal',
        'soccer/usa.1':                         'la-galaxy',
    }

    # Example game IDs for /summary?event=X
    EXAMPLE_EVENTS = {
        'football/college-football': '400934572',
        'football/nfl':              '401671803',
        'basketball/nba':            '401869190',
        'baseball/mlb':              '401472463',
        'hockey/nhl':                '401559416',
    }

    def __init__(self, db: SportsDB):
        self.db = db
        self.session = requests.Session()
        self.session.headers.update({'User-Agent': 'Mozilla/5.0 (TrulySporting/1.0)'})

    def build_endpoints(self) -> List[Dict]:
        """Return all concrete crawlable endpoints with fully resolved URLs."""
        eps: List[Dict] = []
        base = EndpointRegistry.BASE_URL
        for cat, sports in EndpointRegistry.REGISTRY.items():
            for sport, ep_map in sports.items():
                sk = f"{cat}/{sport}"
                # Standard endpoints (scoreboard / teams / news / rankings)
                for ep_type, url in ep_map.items():
                    eps.append({'key': f"{sk}/{ep_type}", 'sport_key': sk,
                                'endpoint_type': ep_type, 'url': url, 'params': {}})
                # Extended single-team endpoint
                team = self.EXAMPLE_TEAMS.get(sk, '')
                if team:
                    eps.append({
                        'key': f"{sk}/team_detail", 'sport_key': sk,
                        'endpoint_type': 'team_detail',
                        'url': f"{base}/{cat}/{sport}/teams/{team}", 'params': {},
                    })
                # Game summary endpoint
                event = self.EXAMPLE_EVENTS.get(sk, '')
                if event:
                    sb_url = ep_map.get('scoreboard', f"{base}/{cat}/{sport}/scoreboard")
                    eps.append({
                        'key': f"{sk}/summary", 'sport_key': sk,
                        'endpoint_type': 'summary',
                        'url': sb_url.replace('/scoreboard', '/summary'),
                        'params': {'event': event},
                    })
        return eps


# ─────────────────────────────────────────────────────────────
# 5. UI HELPERS
# ─────────────────────────────────────────────────────────────

# Status colour helpers
_INJ_COLORS = {
    'Out':          ('#dc3545', '⛔'),
    'Doubtful':     ('#fd7e14', '🟠'),
    'Questionable': ('#ffc107', '🟡'),
    'Day-To-Day':   ('#20c997', '🟢'),
    'IR':           ('#6c757d', '🩹'),
}


def _inj_badge(status: str) -> str:
    color, icon = _INJ_COLORS.get(status, ('#aaa', '❓'))
    return (f'<span style="background:{color};color:white;padding:1px 5px;'
            f'border-radius:3px;font-size:10px">{icon} {status}</span>')


def render_game_detail(event_id: str, db: Any, home_abbr: str, away_abbr: str):
    """
    Full inside-game view rendered as sub-tabs:
      Box Score | Player Stats | Win Probability | Betting | Injuries | Officials | Videos
    Uses data already stored in game_summaries + play_by_play.
    """
    gs = db.get_game_summary(event_id)
    if not gs:
        st.info("No summary data yet — click **Fetch Summary** above.")
        return

    # Resolve team abbrs from stored summary if caller didn't supply them
    if not home_abbr:
        home_abbr = gs.get('home_abbr', 'HOME')
    if not away_abbr:
        away_abbr = gs.get('away_abbr', 'AWAY')

    try:
        team_stats_full  = json.loads(gs.get('team_stats_full_json') or '[]')
        player_stats     = json.loads(gs.get('player_stats_json') or '[]')
        injuries         = json.loads(gs.get('injuries_json') or '[]')
        officials        = json.loads(gs.get('officials_json') or '[]')
        videos           = json.loads(gs.get('videos_json') or '[]')
        win_prob         = json.loads(gs.get('win_prob_json') or '[]')
        scoring_plays    = json.loads(gs.get('scoring_plays_json') or '[]')
        pickcenter       = json.loads(gs.get('pickcenter_json') or '[]')
        leaders          = json.loads(gs.get('leaders_json') or '[]')
        standings        = json.loads(gs.get('standings_json') or '{}')
        last5_home       = json.loads(gs.get('last_five_home') or '[]')
        last5_away       = json.loads(gs.get('last_five_away') or '[]')
    except Exception:
        st.error("Could not parse stored summary data.")
        return

    dtab_labels = ["📊 Box Score", "🏃 Players", "📈 Win Prob",
                   "💰 Betting", "🩺 Injuries", "🎬 Highlights",
                   "🏆 Standings", "🏟 Game Info"]
    dt1, dt2, dt3, dt4, dt5, dt6, dt7, dt8 = st.tabs(dtab_labels)

    # ── Box Score ─────────────────────────────────────────────
    with dt1:
        st.caption(f"**{away_abbr}** @ **{home_abbr}**")

        # Team stats comparison
        if team_stats_full:
            home_s = next((t['stats'] for t in team_stats_full if t['side'] == 'home'), [])
            away_s = next((t['stats'] for t in team_stats_full if t['side'] != 'home'), [])
            # Build comparison DataFrame
            rows = []
            for hs in home_s:
                label = hs['label']
                av = next((x['value'] for x in away_s if x['label'] == label), '—')
                rows.append({'Stat': label, away_abbr: av, home_abbr: hs['value']})
            if rows:
                import pandas as _pd
                df_box = _pd.DataFrame(rows)
                st.dataframe(df_box, use_container_width=True, hide_index=True)
        else:
            st.info("Team stats not yet loaded.")

        # Scoring plays summary
        if scoring_plays:
            st.markdown("**Scoring Plays**")
            for sp in scoring_plays:
                q    = sp.get('period', '')
                clk  = sp.get('clock', '')
                team = sp.get('team', '')
                txt  = sp.get('text', '')
                away = sp.get('away', 0)
                home = sp.get('home', 0)
                st.html(
                    f'<div style="border-left:3px solid #28a745;padding:3px 8px;margin:3px 0;'
                    f'font-size:13px">🏈 <b>Q{q} {clk}</b> &nbsp;'
                    f'<span style="color:#0d6efd">{team}</span> — {txt} '
                    f'<span style="background:#333;color:#fff;padding:1px 6px;border-radius:3px;'
                    f'font-size:11px;margin-left:6px">{away_abbr} {away} – {home_abbr} {home}</span>'
                    f'</div>'
                )

        # Top stat leaders
        if leaders:
            st.markdown("**Stat Leaders**")
            key_stats = ['passingYards', 'rushingYards', 'receivingYards', 'sacks', 'totalTackles',
                         'points', 'assists', 'rebounds', 'goals', 'saves', 'hits', 'strikeouts']
            shown = [l for l in leaders if l.get('stat_name') in key_stats][:12]
            if shown:
                ldr_cols = st.columns(3)
                for i, ldr in enumerate(shown):
                    with ldr_cols[i % 3]:
                        hs = ldr.get('headshot', '')
                        nm = ldr.get('athlete', '?')
                        pos = ldr.get('position', '')
                        val = ldr.get('value', '')
                        stat = ldr.get('stat', '')
                        side_lbl = home_abbr if ldr.get('is_home') else away_abbr
                        st.html(
                            f'<div style="display:flex;align-items:center;gap:8px;margin:4px 0;'
                            f'border:1px solid #eee;border-radius:6px;padding:6px">'
                            f'{"<img src=" + repr(hs) + " style=height:40px;border-radius:50%>" if hs else ""}'
                            f'<div><div style="font-size:12px;font-weight:bold">{nm}'
                            f'{"  <span style=font-size:10px;color:#888>" + pos + "</span>" if pos else ""}'
                            f'</div>'
                            f'<div style="font-size:11px;color:#555">{stat}: <b>{val}</b>'
                            f' <span style="color:#999">({side_lbl})</span></div></div></div>'
                        )

        # Last 5 games
        if last5_home or last5_away:
            st.markdown("**Last 5 Games**")
            l5col1, l5col2 = st.columns(2)
            for label, games in [(home_abbr, last5_home), (away_abbr, last5_away)]:
                col = l5col1 if label == home_abbr else l5col2
                with col:
                    st.caption(f"**{label}**")
                    for g in games:
                        result = g.get('result', '')
                        color = '#28a745' if result == 'W' else '#dc3545'
                        opp = g.get('opponent', '')
                        vs  = g.get('atVs', 'vs')
                        score = g.get('score', '')
                        dt_s  = g.get('date', '')
                        st.html(
                            f'<div style="font-size:12px;margin:2px 0">'
                            f'<span style="background:{color};color:white;padding:1px 5px;'
                            f'border-radius:3px;font-weight:bold">{result}</span>'
                            f' {vs} {opp} — {score}'
                            f' <span style="color:#aaa;font-size:10px">{dt_s}</span></div>'
                        )

    # ── Player Stats ──────────────────────────────────────────
    with dt2:
        # If boxscore player_stats is missing/empty, try to derive from PBP
        _ps_source = 'boxscore'
        if not player_stats:
            _pbp_stats = db.get_pbp_derived_stats(event_id)
            if _pbp_stats:
                player_stats  = _pbp_stats
                _ps_source    = 'pbp'
        if not player_stats:
            st.info("Player stats not yet loaded. Fetch game summary to populate.")
        else:
            if _ps_source == 'pbp':
                st.caption(
                    "ℹ️ Showing stats derived from play-by-play text "
                    "(boxscore data unavailable). Abbreviated player names "
                    "(e.g. *S.Darnold*) are used as-is from the PBP log."
                )
            # Category selector
            cat_names = list({c['displayName']: 1 for c in player_stats}.keys())
            sel_cat = st.selectbox("Category", cat_names, key=f"ps_cat_{event_id}")
            sel_cats = [c for c in player_stats if c['displayName'] == sel_cat]
            for cat_block in sel_cats:
                team   = cat_block.get('team', '?')
                labels = cat_block.get('labels', [])
                totals = cat_block.get('totals', [])
                athletes_list = cat_block.get('athletes', [])
                if not athletes_list:
                    continue
                st.markdown(f"**{team}**")
                rows = []
                for ath in athletes_list:
                    row = {'#': ath.get('jersey', ''), 'Player': ath.get('name', '?')}
                    for i, lbl in enumerate(labels):
                        row[lbl] = ath['stats'][i] if i < len(ath['stats']) else '—'
                    rows.append(row)

                import pandas as _pd
                df_ps = _pd.DataFrame(rows)

                # Highlight non-zero rows
                def _highlight(row):
                    return ['background-color: #f0fff0' if row.get('Player','') else '' for _ in row]

                if not df_ps.empty:
                    # Show headshots inline in caption area
                    hs_html = ''.join(
                        f'<img src="{a["headshot"]}" title="{a["name"]}" '
                        f'style="height:28px;border-radius:50%;margin-right:3px">'
                        for a in athletes_list if a.get('headshot')
                    )
                    if hs_html:
                        st.html(f'<div style="margin-bottom:4px">{hs_html}</div>')
                    st.dataframe(df_ps, use_container_width=True, hide_index=True)

                if totals:
                    total_row = {'#': '', 'Player': 'TOTALS'}
                    for i, lbl in enumerate(labels):
                        total_row[lbl] = totals[i] if i < len(totals) else '—'
                    import pandas as _pd2
                    st.dataframe(_pd2.DataFrame([total_row]), use_container_width=True, hide_index=True)

    # ── Win Probability Chart ─────────────────────────────────
    with dt3:
        if not win_prob:
            st.info("Win probability data not available for this game.")
        else:
            x_vals = list(range(len(win_prob)))
            home_pct = [wp.get('homeWinPercentage', 0.5) * 100 for wp in win_prob]
            away_pct = [round(100 - p, 1) for p in home_pct]

            fig_wp = go.Figure()
            fig_wp.add_trace(go.Scatter(
                x=x_vals, y=home_pct, name=home_abbr,
                fill='tozeroy', fillcolor='rgba(13,110,253,0.15)',
                line=dict(color='#0d6efd', width=2),
            ))
            fig_wp.add_trace(go.Scatter(
                x=x_vals, y=away_pct, name=away_abbr,
                fill='tozeroy', fillcolor='rgba(220,53,69,0.1)',
                line=dict(color='#dc3545', width=2),
            ))
            fig_wp.add_hline(y=50, line_dash='dash', line_color='#aaa')
            fig_wp.update_layout(
                title=f"Win Probability — {away_abbr} @ {home_abbr}",
                yaxis_title="Win %",
                xaxis_title="Play #",
                yaxis=dict(range=[0, 100]),
                height=350,
                legend=dict(orientation='h', y=1.1),
                margin=dict(l=40, r=20, t=60, b=40),
            )
            st.plotly_chart(fig_wp, use_container_width=True)

            peak_home = max(home_pct)
            peak_away = max(away_pct)
            wpc1, wpc2 = st.columns(2)
            wpc1.metric(f"{home_abbr} peak win %", f"{peak_home:.1f}%")
            wpc2.metric(f"{away_abbr} peak win %", f"{peak_away:.1f}%")

    # ── Betting / Pick Center ─────────────────────────────────
    with dt4:
        if not pickcenter:
            st.info("No betting data available for this game.")
        else:
            for pc in pickcenter:
                prov = pc.get('provider', 'Unknown')
                st.markdown(f"#### {prov}")
                cols_bet = st.columns(4)
                cols_bet[0].metric("Spread", pc.get('details', '—'))
                cols_bet[1].metric("Over/Under", f"{pc.get('overUnder', '—')}")
                cols_bet[2].metric(f"{home_abbr} ML",
                                   f"{pc.get('home_ml', '—'):+d}"
                                   if isinstance(pc.get('home_ml'), (int, float)) else str(pc.get('home_ml', '—')))
                cols_bet[3].metric(f"{away_abbr} ML",
                                   f"{pc.get('away_ml', '—'):+d}"
                                   if isinstance(pc.get('away_ml'), (int, float)) else str(pc.get('away_ml', '—')))
                over_odds  = pc.get('overOdds', '')
                under_odds = pc.get('underOdds', '')
                if over_odds or under_odds:
                    st.caption(f"Over: {over_odds}  ·  Under: {under_odds}")
                fav_label = home_abbr if pc.get('home_favorite') else away_abbr
                st.caption(f"Favorite: **{fav_label}**")
                st.divider()

    # ── Injuries ──────────────────────────────────────────────
    with dt5:
        if not injuries:
            st.info("No injury data stored for this game.")
        else:
            for team_abbr_inj in sorted({i.get('team', '?') for i in injuries}):
                team_injuries = [i for i in injuries if i.get('team') == team_abbr_inj]
                st.markdown(f"**{team_abbr_inj}** — {len(team_injuries)} listed")
                rows_inj = []
                for inj in team_injuries:
                    rows_inj.append({
                        '#':        inj.get('jersey', ''),
                        'Player':   inj.get('athlete', '?'),
                        'Pos':      inj.get('pos', ''),
                        'Status':   inj.get('status', ''),
                        'Injury':   inj.get('type', ''),
                        'Detail':   inj.get('detail', ''),
                        'Est. Return': inj.get('return', '')[:10] if inj.get('return') else '',
                    })
                import pandas as _pdI
                df_inj = _pdI.DataFrame(rows_inj)

                def _status_color(val):
                    color_map = {'Out': 'color: #dc3545; font-weight: bold',
                                 'Doubtful': 'color: #fd7e14',
                                 'Questionable': 'color: #ffc107',
                                 'IR': 'color: #6c757d'}
                    return color_map.get(val, '')

                st.dataframe(
                    df_inj.style.map(_status_color, subset=['Status']),
                    use_container_width=True, hide_index=True
                )

    # ── Videos / Highlights ───────────────────────────────────
    with dt6:
        if not videos:
            st.info("No highlight videos available.")
        else:
            for v in videos:
                vcol1, vcol2 = st.columns([1, 2])
                with vcol1:
                    thumb = v.get('thumbnail', '')
                    if thumb:
                        st.image(thumb, use_container_width=True)
                with vcol2:
                    headline = v.get('headline', '')
                    link = v.get('link', '')
                    if link:
                        st.markdown(f"**[{headline}]({link})**")
                    else:
                        st.markdown(f"**{headline}**")
                    desc = v.get('description', '')
                    if desc:
                        st.write(desc[:200])
                    dur = v.get('duration', 0)
                    if dur:
                        st.caption(f"⏱ {dur}s")
                st.divider()

    # ── Division Standings ─────────────────────────────────────
    with dt7:
        groups = standings.get('groups', [])
        if not groups:
            st.info("Standings not available.")
        else:
            for grp in groups:
                header = grp.get('header', '')
                entries = grp.get('standings', {}).get('entries', [])
                if not entries:
                    continue
                st.markdown(f"**{header}**")
                rows_std = []
                for e in entries:
                    if not isinstance(e, dict):
                        continue
                    team_info = e.get('team', {})
                    if not isinstance(team_info, dict):
                        continue
                    abbr = team_info.get('abbreviation', '?')
                    name = team_info.get('displayName', '')
                    stat_dict = {}
                    for x in (e.get('stats', []) if isinstance(e.get('stats'), list) else []):
                        if isinstance(x, dict):
                            stat_dict[x.get('name', '')] = x.get('displayValue', '')
                    rows_std.append({
                        'Team': f"{abbr} — {name}",
                        'W': stat_dict.get('wins', ''),
                        'L': stat_dict.get('losses', ''),
                        'Pct': stat_dict.get('winPercent', ''),
                        'PF': stat_dict.get('pointsFor', ''),
                        'PA': stat_dict.get('pointsAgainst', ''),
                        'Overall': stat_dict.get('overall', ''),
                    })
                import pandas as _pdS
                if rows_std:
                    st.dataframe(_pdS.DataFrame(rows_std), use_container_width=True, hide_index=True)
            stds_link = standings.get('fullViewLink', {})
            if stds_link:
                href = stds_link if isinstance(stds_link, str) else stds_link.get('href', '')
                if href:
                    st.markdown(f"[Full standings on ESPN ↗]({href})")

    # ── Game Info ─────────────────────────────────────────────
    with dt8:
        venue_name = gs.get('venue_name', '')
        venue_city = gs.get('venue_city', '')
        if venue_name:
            st.markdown(f"**🏟 Venue:** {venue_name}  ·  {venue_city}")
        if officials:
            st.markdown("**Officials:**")
            off_rows = [{'Name': o['name'], 'Role': o['role']} for o in officials]
            import pandas as _pdO
            st.dataframe(_pdO.DataFrame(off_rows), use_container_width=True, hide_index=True)
        st.caption(f"Data fetched: {gs.get('fetched_at', '')[:16]}")


def render_game_card(game: Any, db: Any = None, worker: Any = None, category: str = '', sport: str = ''):
    """
    Renders a rich game card showing:
    - Status badge (FINAL / LIVE with clock / Scheduled)
    - Special event note (Super Bowl, Play-In, etc.)
    - Team names with colors and per-period score grid
    - Top statistical leaders
    - Broadcast info and links (Box Score, Recap)
    """
    status = str(game.get('status', ''))
    is_final = 'FINAL' in status.upper()
    is_live = any(x in status.upper() for x in ('PROGRESS', 'HALF', 'LIVE'))

    home_score = int(game['home_score']) if game.get('home_score') else 0
    away_score = int(game['away_score']) if game.get('away_score') else 0
    home_win = bool(game.get('home_winner'))

    # Status badge — uses scoped .ts-card CSS classes so colours are !important-safe
    if is_final:
        status_html = '<span style="background:#28a745;color:white;padding:2px 8px;border-radius:4px;font-size:12px">FINAL</span>'
        status_html_cls = '<span class="ts-status-final">FINAL</span>'
    elif is_live:
        clock = game.get('clock', '')
        period = game.get('period', '')
        status_html = (f'<span style="background:#dc3545;color:white;padding:2px 8px;'
                       f'border-radius:4px;font-size:12px">🔴 LIVE {clock} P{period}</span>')
        status_html_cls = f'<span class="ts-status-live">🔴 LIVE {clock} P{period}</span>'
    else:
        detail = game.get('status_detail', 'Scheduled')
        status_html = (f'<span style="background:#6c757d;color:white;padding:2px 8px;'
                       f'border-radius:4px;font-size:12px">{detail}</span>')
        status_html_cls = f'<span class="ts-status-sched">{detail}</span>'

    # Special event note
    note_html = ''
    if game.get('note'):
        note_html = (f'<span style="background:#0d6efd;color:white;padding:2px 8px;'
                     f'border-radius:4px;font-size:11px;margin-left:6px">{game["note"]}</span>')

    # Team colors
    home_color = '#' + game['home_color'] if game.get('home_color') else '#333333'
    away_color = '#' + game['away_color'] if game.get('away_color') else '#333333'
    home_bold = 'font-weight:bold;' if home_win else ''
    away_bold = 'font-weight:bold;' if not home_win and is_final else ''

    # Win indicator
    home_arrow = ' ✓' if home_win and is_final else ''
    away_arrow = ' ✓' if not home_win and is_final else ''

    # Per-period score grid
    try:
        home_periods = json.loads(game['home_periods']) if game.get('home_periods') else []
        away_periods = json.loads(game['away_periods']) if game.get('away_periods') else []
    except Exception:
        home_periods, away_periods = [], []

    period_count = len(home_periods)
    if period_count == 4:
        period_headers = ['Q1', 'Q2', 'Q3', 'Q4']
    elif period_count == 3:
        period_headers = ['1st', '2nd', '3rd']
    elif period_count == 2:
        period_headers = ['1st', '2nd']
    elif period_count > 4:
        period_headers = ['Q1', 'Q2', 'Q3', 'Q4'] + [f'OT{i}' for i in range(1, period_count - 3)]
    else:
        period_headers = [f'P{i+1}' for i in range(period_count)]

    period_html = ''
    if home_periods and away_periods:
        header_cells = ''.join(
            f'<th style="padding:2px 8px;text-align:center;color:#555;font-size:11px;font-weight:600">{p}</th>'
            for p in period_headers
        )
        home_cells = ''.join(
            f'<td style="padding:2px 8px;text-align:center;font-size:12px;color:#111">{v}</td>'
            for v in home_periods
        )
        away_cells = ''.join(
            f'<td style="padding:2px 8px;text-align:center;font-size:12px;color:#111">{v}</td>'
            for v in away_periods
        )
        period_html = f'''
        <table style="border-collapse:collapse;margin-top:6px;font-family:monospace">
          <tr>
            <th style="padding:2px 10px;text-align:left;font-size:11px;color:#555;font-weight:600;min-width:60px">Team</th>
            {header_cells}
            <th style="padding:2px 10px;text-align:center;font-size:11px;font-weight:600">T</th>
          </tr>
          <tr>
            <td class="ts-away-name" style="padding:2px 10px;font-size:13px;{away_bold}">
              {game.get('away_abbr') or game.get('away_team','')}{away_arrow}
            </td>
            {away_cells}
            <td style="padding:2px 10px;text-align:center;font-size:14px;{away_bold}">{away_score}</td>
          </tr>
          <tr>
            <td class="ts-home-name" style="padding:2px 10px;font-size:13px;{home_bold}">
              {game.get('home_abbr') or game.get('home_team','')}{home_arrow}
            </td>
            {home_cells}
            <td style="padding:2px 10px;text-align:center;font-size:14px;{home_bold}">{home_score}</td>
          </tr>
        </table>'''
    else:
        # Fallback: simple line score
        period_html = f'''
        <div style="font-size:20px;margin:6px 0">
          <span class="ts-away-name" style="{away_bold}">{game.get('away_abbr','?')}</span>
          <span style="{away_bold}"> {away_score}</span>
          &nbsp;<span class="ts-dim">@</span>&nbsp;
          <span class="ts-home-name" style="{home_bold}">{game.get('home_abbr','?')}</span>
          <span style="{home_bold}"> {home_score}</span>
        </div>'''

    # Records
    home_rec = f"({game['home_record']})" if game.get('home_record') else ''
    away_rec = f"({game['away_record']})" if game.get('away_record') else ''
    records_html = (f'<div style="font-size:11px;color:#444;margin-top:2px">'
                    f'{game.get("away_team","")} {away_rec} @ {game.get("home_team","")} {home_rec}</div>')

    # Statistical leaders
    try:
        leaders = json.loads(game['leaders_json']) if game.get('leaders_json') else {}
    except Exception:
        leaders = {}

    # Odds (from schema-discovered scoreboard.competitions[0].odds[])
    try:
        odds = json.loads(game.get('odds_json') or '{}')
    except Exception:
        odds = {}
    odds_html = ''
    if odds.get('spread') or odds.get('over_under'):
        parts = []
        if odds.get('spread'):
            parts.append(f'<b>Spread:</b> {odds["spread"]}')
        if odds.get('over_under'):
            parts.append(f'<b>O/U:</b> {odds["over_under"]}')
        if odds.get('home_ml') or odds.get('away_ml'):
            parts.append(
                f'ML: {game.get("home_abbr","?")} {odds.get("home_ml","")} / '
                f'{game.get("away_abbr","?")} {odds.get("away_ml","")}'
            )
        prov = f' <span style="color:#bbb;font-size:10px">via {odds["provider"]}</span>' if odds.get('provider') else ''
        odds_html = (f'<div style="font-size:11px;color:#555;margin-top:4px">'
                     f'💰 {"  ·  ".join(parts)}{prov}</div>')

    # Weather (outdoor games)
    weather_html = ''
    if game.get('weather'):
        weather_html = (f'<span style="font-size:11px;color:#555;margin-right:12px">'
                        f'🌤 {game["weather"]}</span>')

    # Neutral site / conference badges
    extra_badges = ''
    if game.get('neutral_site'):
        extra_badges += ('<span style="background:#6f42c1;color:white;padding:1px 6px;'
                         'border-radius:4px;font-size:10px;margin-left:4px">Neutral</span>')
    if game.get('conference_game'):
        extra_badges += ('<span style="background:#fd7e14;color:white;padding:1px 6px;'
                         'border-radius:4px;font-size:10px;margin-left:4px">Conf</span>')

    leaders_html = ''
    for stat, info in list(leaders.items())[:4]:
        if isinstance(info, dict):
            pos = f" ({info.get('position','')})" if info.get('position') else ''
            leaders_html += (f'<span style="font-size:11px;color:#333;margin-right:14px">'
                             f'<b style="color:#111">{stat.upper()}</b>: {info.get("athlete","?")}{pos} '
                             f'<span style="color:#111;font-weight:600">{info.get("value","")}</span></span>')

    # Broadcast & links
    try:
        links = json.loads(game['links_json']) if game.get('links_json') else {}
    except Exception:
        links = {}

    links_html = ''
    if links.get('boxscore'):
        links_html += f'<a href="{links["boxscore"]}" target="_blank" style="font-size:11px;margin-right:10px">📊 Box Score</a>'
    if links.get('recap'):
        links_html += f'<a href="{links["recap"]}" target="_blank" style="font-size:11px;margin-right:10px">📝 Recap</a>'
    if links.get('pbp'):
        links_html += f'<a href="{links["pbp"]}" target="_blank" style="font-size:11px;margin-right:10px">▶ Play-by-Play</a>'

    broadcast_html = ''
    if game.get('broadcast'):
        broadcast_html = f'<span style="font-size:11px;color:#333">📺 {game["broadcast"]}</span>'

    venue_html = ''
    if game.get('venue'):
        city = game.get('venue_city', '')
        venue_html = f'{game["venue"]}{" · " + city if city else ""}'

    att_html = ''
    try:
        att = int(str(game.get('attendance', 0)))
        if att > 0:
            att_html = f' · {att:,} fans'
    except Exception:
        pass

    headline_html = ''
    if game.get('headline'):
        headline_html = f'<div style="font-size:12px;color:#333;font-style:italic;margin-top:4px">{game["headline"][:180]}</div>'

    card_html = f'''
    <style>
      .ts-card, .ts-card * {{
        color: #111 !important;
        -webkit-text-fill-color: #111 !important;
      }}
      .ts-card a, .ts-card a * {{
        color: #2563eb !important;
        -webkit-text-fill-color: #2563eb !important;
      }}
      .ts-card .ts-dim {{
        color: #555 !important;
        -webkit-text-fill-color: #555 !important;
      }}
      .ts-card .ts-status-final {{
        background:#28a745;color:#fff !important;
        -webkit-text-fill-color:#fff !important;
        padding:2px 8px;border-radius:4px;font-size:12px;
      }}
      .ts-card .ts-status-live {{
        background:#dc3545;color:#fff !important;
        -webkit-text-fill-color:#fff !important;
        padding:2px 8px;border-radius:4px;font-size:12px;
      }}
      .ts-card .ts-status-sched {{
        background:#6c757d;color:#fff !important;
        -webkit-text-fill-color:#fff !important;
        padding:2px 8px;border-radius:4px;font-size:12px;
      }}
      .ts-card table td, .ts-card table th {{
        color: #111 !important;
        -webkit-text-fill-color: #111 !important;
      }}
      .ts-card .ts-away-name {{ color: {away_color} !important; -webkit-text-fill-color:{away_color} !important; }}
      .ts-card .ts-home-name {{ color: {home_color} !important; -webkit-text-fill-color:{home_color} !important; }}
    </style>
    <div class="ts-card" style="border:1px solid #d0d5e0;border-radius:10px;padding:14px 16px;
                margin-bottom:14px;background:#fff;box-shadow:0 2px 6px rgba(0,0,0,0.08)">
      <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:4px">
        <div>{status_html_cls}{note_html}{extra_badges}</div>
        <div class="ts-dim" style="font-size:11px">{venue_html}{att_html}</div>
      </div>
      <div class="ts-dim" style="font-size:11px;margin-bottom:2px">{records_html if records_html else ""}</div>
      {period_html}
      {headline_html}
      {odds_html}
      <div style="margin-top:8px">{leaders_html}</div>
      <div style="margin-top:6px;display:flex;align-items:center;gap:8px">
        {links_html}{broadcast_html}{weather_html}
      </div>
    </div>
    '''
    st.html(card_html)

    # ── Game Detail + Play-by-Play expanders ───────────────────
    if db is None:
        return
    try:
        links_data = json.loads(game.get('links_json') or '{}')
    except Exception:
        links_data = {}

    event_id = str(game.get('event_id', ''))
    is_final  = 'FINAL' in str(game.get('status', '')).upper()
    is_live   = any(x in str(game.get('status', '')).upper() for x in ('PROGRESS', 'HALF', 'LIVE'))

    if not event_id or not (is_final or is_live):
        return

    home_abbr_game = str(game.get('home_abbr') or game.get('home_team', 'HOME'))
    away_abbr_game = str(game.get('away_abbr') or game.get('away_team', 'AWAY'))

    # ── Fetch Summary button (shows if no summary stored yet) ──
    has_summary = bool(db.get_game_summary(event_id))
    if not has_summary:
        col_fs, col_fi = st.columns([1, 4])
        with col_fs:
            if st.button("📥 Fetch Summary", key=f"gs_fetch_{event_id}"):
                if worker and category and sport:
                    with st.spinner("Fetching game summary…"):
                        worker.fetch_game_summary(category, sport, event_id)
                    st.rerun()
        with col_fi:
            st.caption("Loads full box score, player stats, injuries, betting data & more.")
    else:
        # Offer a re-fetch button (small, right-aligned via columns)
        _, col_refetch = st.columns([5, 1])
        with col_refetch:
            if st.button("🔄 Refresh", key=f"gs_refetch_{event_id}", help="Re-fetch game summary"):
                if worker and category and sport:
                    with st.spinner("Re-fetching…"):
                        worker.fetch_game_summary(category, sport, event_id)
                    st.rerun()

    # ── Game Detail expander ────────────────────────────────────
    with st.expander("📊 Game Detail  (Box Score · Players · Win Prob · Betting · Injuries)", expanded=False):
        if not has_summary:
            st.info("Click **Fetch Summary** above to load game detail.")
        else:
            render_game_detail(event_id, db, home_abbr_game, away_abbr_game)

    # ── Play-by-Play expander ─────────────────────────────────────
    has_pbp_link = bool(links_data.get('pbp'))
    is_football   = (category == 'football')
    # Show PBP section for: football (requires pbp link), or any non-football final/live game
    show_pbp_section = has_pbp_link or (not is_football and (is_final or is_live))
    if not show_pbp_section:
        return

    pbp_icon = "🏈" if is_football else {"basketball": "🏀", "baseball": "⚾", "hockey": "🏒", "soccer": "⚽"}.get(category, "▶")

    with st.expander(f"{pbp_icon} Play-by-Play", expanded=False):
        already_fetched = db.has_pbp(event_id)

        if not already_fetched:
            col_btn, col_info = st.columns([1, 3])
            with col_btn:
                if st.button("Fetch PBP", key=f"pbp_fetch_{event_id}"):
                    if worker and category and sport:
                        with st.spinner("Fetching play-by-play data…"):
                            worker.fetch_game_summary(category, sport, event_id)
                        st.rerun()
                    else:
                        st.error("Worker not available.")
            with col_info:
                if is_football:
                    st.caption("Pulls full drive-by-drive data from ESPN for this game.")
                else:
                    st.caption("Pulls play-by-play data from ESPN for this game.")
            return

        # ── Load stored plays ──────────────────────────────────
        df_all = db.get_play_by_play(event_id)
        if df_all.empty:
            st.info("No play data stored.")
            return

        if is_football:
            # ── Football: drive-by-drive breakdown ────────────
            st.markdown("**Drives**")
            for drive_num, drive_df in df_all.groupby('drive_num', sort=True):
                first = drive_df.iloc[0]
                score_icon = "🏈" if first['drive_is_score'] else ""
                header = (
                    f"{score_icon} **{first['team_abbr'] or '—'}** · "
                    f"{first['drive_desc']} · "
                    f"_{first['drive_result']}_"
                )
                with st.container(border=True):
                    st.markdown(header)
                    play_cols = ['period', 'clock', 'play_type', 'play_text',
                                 'down_dist_text', 'stat_yardage', 'away_score', 'home_score']
                    disp_p = drive_df[play_cols].copy()
                    disp_p.columns = ['Q', 'Clock', 'Type', 'Play', 'Situation', 'Yards', 'Away', 'Home']
                    scoring_idx = set(drive_df.index[drive_df['scoring_play'] == 1])
                    turnover_idx = set(drive_df.index[drive_df['is_turnover'] == 1])

                    def _row_style(row, _s=scoring_idx, _t=turnover_idx):
                        if row.name in _s:
                            return ['background-color:#fff3cd'] * len(row)
                        if row.name in _t:
                            return ['background-color:#f8d7da'] * len(row)
                        return [''] * len(row)

                    st.dataframe(
                        disp_p.style.apply(_row_style, axis=1),
                        use_container_width=True, hide_index=True,
                    )

        else:
            # ── Non-football: flat chronological play list ────
            _period_full  = {'basketball': 'Quarter', 'baseball': 'Inning',
                             'hockey': 'Period', 'soccer': 'Half'}
            _period_short = {'basketball': 'Q', 'baseball': 'Inn',
                             'hockey': 'P', 'soccer': 'H'}
            per_full  = _period_full.get(category, 'Period')
            per_short = _period_short.get(category, 'Per')

            all_periods = sorted(df_all['period'].dropna().unique().tolist())
            sel_per = st.selectbox(
                f"Filter by {per_full}",
                ['All'] + [str(int(p)) for p in all_periods],
                key=f"pbp_per_{event_id}"
            )
            df_show = df_all if sel_per == 'All' else df_all[df_all['period'] == int(sel_per)]

            n_scoring = int(df_show['scoring_play'].sum())
            legend = f"  ·  🟡 = Scoring play ({n_scoring})" if n_scoring else ""
            st.caption(f"{len(df_show)} plays{legend}")

            play_cols = ['period', 'clock', 'play_type', 'play_text', 'away_score', 'home_score']
            disp = df_show[play_cols].rename(columns={
                'period': per_short, 'clock': 'Clock', 'play_type': 'Type',
                'play_text': 'Play', 'away_score': 'Away', 'home_score': 'Home',
            })
            scoring_idx = set(df_show.index[df_show['scoring_play'] == 1])

            def _flat_style(row, _s=scoring_idx):
                return ['background-color:#fff3cd' if row.name in _s else ''] * len(row)

            st.dataframe(
                disp.style.apply(_flat_style, axis=1),
                use_container_width=True, hide_index=True,
            )


# ─────────────────────────────────────────────────────────────
# UI THEME HELPERS
# ─────────────────────────────────────────────────────────────

_SPORT_THEMES: dict = {
    'football': {
        'emoji': '🏈', 'color': '#2d5a1b', 'accent': '#4a8c2a',
        'bg': '#f0f4ec', 'gradient': 'linear-gradient(135deg,#f0f4ec,#e8f0e0)',
        'label': 'Football', 'field_lines': True,
    },
    'basketball': {
        'emoji': '🏀', 'color': '#b84a12', 'accent': '#e06b30',
        'bg': '#fdf3ed', 'gradient': 'linear-gradient(135deg,#fdf3ed,#fae6d8)',
        'label': 'Basketball', 'field_lines': False,
    },
    'baseball': {
        'emoji': '⚾', 'color': '#1a3a6b', 'accent': '#2a5fa0',
        'bg': '#edf2fa', 'gradient': 'linear-gradient(135deg,#edf2fa,#dde8f5)',
        'label': 'Baseball', 'field_lines': False,
    },
    'hockey': {
        'emoji': '🏒', 'color': '#0d3f6e', 'accent': '#1a6aad',
        'bg': '#edf6fb', 'gradient': 'linear-gradient(135deg,#edf6fb,#daeef9)',
        'label': 'Hockey', 'field_lines': False,
    },
    'soccer': {
        'emoji': '⚽', 'color': '#1a5c39', 'accent': '#28a060',
        'bg': '#edfaf3', 'gradient': 'linear-gradient(135deg,#edfaf3,#d9f3e5)',
        'label': 'Soccer', 'field_lines': True,
    },
    'golf': {
        'emoji': '⛳', 'color': '#2e5c1a', 'accent': '#4a8c2a',
        'bg': '#eef5e8', 'gradient': 'linear-gradient(135deg,#eef5e8,#e3f0d8)',
        'label': 'Golf', 'field_lines': False,
    },
    'tennis': {
        'emoji': '🎾', 'color': '#8c5a1a', 'accent': '#c87e30',
        'bg': '#faf4e8', 'gradient': 'linear-gradient(135deg,#faf4e8,#f5ecd0)',
        'label': 'Tennis', 'field_lines': False,
    },
    'default': {
        'emoji': '🏆', 'color': '#1e3a6e', 'accent': '#3a6abf',
        'bg': '#eef2fb', 'gradient': 'linear-gradient(135deg,#eef2fb,#dce5f5)',
        'label': 'Sports', 'field_lines': False,
    },
}


def _get_sport_theme(ep_key: str = '') -> dict:
    ep = ep_key.lower()
    for key, theme in _SPORT_THEMES.items():
        if key in ep:
            return theme
    return _SPORT_THEMES['default']


def _render_tab_banner(title: str, subtitle: str = '', ep_key: str = ''):
    """Render a sport-context banner at the top of a tab."""
    t = _get_sport_theme(ep_key)
    sub_html = (
        f'<p style="margin:3px 0 0;font-size:13px;color:{t["color"]}bb">{subtitle}</p>'
        if subtitle else ''
    )
    # Football gets subtle yard-line decoration
    deco = (
        'repeating-linear-gradient(90deg,transparent,transparent 48px,'
        'rgba(255,255,255,0.35) 48px,rgba(255,255,255,0.35) 50px)'
        if t.get('field_lines') else 'none'
    )
    st.html(f"""
    <div style="background:{t['gradient']};border-left:5px solid {t['accent']};
                border-radius:0 12px 12px 0;padding:14px 22px;margin-bottom:20px;
                position:relative;overflow:hidden">
      <div style="position:absolute;inset:0;background:{deco};pointer-events:none;
                  opacity:0.4"></div>
      <div style="display:flex;align-items:center;gap:12px;position:relative">
        <span style="font-size:32px;filter:drop-shadow(0 1px 2px rgba(0,0,0,0.15))">
          {t['emoji']}
        </span>
        <div>
          <h2 style="margin:0;font-size:20px;font-weight:800;color:{t['color']};
                     letter-spacing:-0.3px">{title}</h2>
          {sub_html}
        </div>
      </div>
    </div>
    """)


def _render_sport_badge(ep_key: str) -> str:
    """Return an inline HTML badge for the current sport."""
    t = _get_sport_theme(ep_key)
    return (f'<span style="display:inline-block;background:{t["accent"]}22;'
            f'color:{t["color"]};border:1px solid {t["accent"]}55;'
            f'border-radius:20px;padding:2px 10px;font-size:11px;font-weight:600">'
            f'{t["emoji"]} {t["label"]}</span>')


def _render_landing():
    """Full-screen landing page. Calls st.stop() at the end."""
    st.html("""
    <style>
    section[data-testid="stSidebar"] { display:none !important }
    #MainMenu { visibility:hidden }
    footer { visibility:hidden }
    .block-container { padding-top: 2rem !important; max-width: 960px !important; }
    </style>
    """)

    st.html("""
    <div style="text-align:center;padding:50px 20px 28px">
      <div style="font-size:72px;margin-bottom:6px;filter:drop-shadow(0 4px 12px rgba(0,0,0,0.15))">
        🏆
      </div>
      <h1 style="font-size:3.2rem;font-weight:900;margin:0 0 8px;
                 background:linear-gradient(135deg,#1e3a6e 0%,#b84a12 55%,#2d5a1b 100%);
                 -webkit-background-clip:text;-webkit-text-fill-color:transparent;
                 background-clip:text;line-height:1.1">
        TrulySporting
      </h1>
      <p style="font-size:1.15rem;color:#444;margin:0 auto;max-width:560px;line-height:1.6">
        Professional ESPN data analytics &mdash; live scores, team trends,
        rosters &amp; real-time sports intelligence, all in one place.
      </p>
      <p style="font-size:0.85rem;color:#999;margin-top:8px">
        🔴 Live data &nbsp;·&nbsp; 📦 SQLite-cached &nbsp;·&nbsp; ⚡ Multi-sport &nbsp;·&nbsp; 🛠 Fully configurable
      </p>
    </div>
    """)

    st.html("""
    <div style="display:grid;grid-template-columns:repeat(3,1fr);gap:14px;
                max-width:900px;margin:0 auto 36px;padding:0 16px">

      <div style="background:#fff;border:1px solid #e2e6f0;border-radius:14px;
                  padding:20px 18px;box-shadow:0 2px 10px rgba(0,0,0,0.05);
                  border-top:4px solid #28a745">
        <div style="font-size:30px">🏅</div>
        <h3 style="margin:10px 0 5px;font-size:15px;color:#1a1a2e;font-weight:700">Scoreboard</h3>
        <p style="font-size:12px;color:#666;margin:0;line-height:1.5">
          Live &amp; final scores with per-quarter breakdowns, player leaders, betting lines &amp; venue info
        </p>
      </div>

      <div style="background:#fff;border:1px solid #e2e6f0;border-radius:14px;
                  padding:20px 18px;box-shadow:0 2px 10px rgba(0,0,0,0.05);
                  border-top:4px solid #0d6efd">
        <div style="font-size:30px">📈</div>
        <h3 style="margin:10px 0 5px;font-size:15px;color:#1a1a2e;font-weight:700">Team Trends</h3>
        <p style="font-size:12px;color:#666;margin:0;line-height:1.5">
          Win/loss streaks, point-differential over time &amp; head-to-head performance charts
        </p>
      </div>

      <div style="background:#fff;border:1px solid #e2e6f0;border-radius:14px;
                  padding:20px 18px;box-shadow:0 2px 10px rgba(0,0,0,0.05);
                  border-top:4px solid #6f42c1">
        <div style="font-size:30px">🏟</div>
        <h3 style="margin:10px 0 5px;font-size:15px;color:#1a1a2e;font-weight:700">Teams</h3>
        <p style="font-size:12px;color:#666;margin:0;line-height:1.5">
          Full roster, venue details, standings, records &amp; rich per-team profiles
        </p>
      </div>

      <div style="background:#fff;border:1px solid #e2e6f0;border-radius:14px;
                  padding:20px 18px;box-shadow:0 2px 10px rgba(0,0,0,0.05);
                  border-top:4px solid #fd7e14">
        <div style="font-size:30px">📰</div>
        <h3 style="margin:10px 0 5px;font-size:15px;color:#1a1a2e;font-weight:700">News</h3>
        <p style="font-size:12px;color:#666;margin:0;line-height:1.5">
          ESPN headlines tagged by athlete &amp; team, with images, bylines &amp; full metadata
        </p>
      </div>

      <div style="background:#fff;border:1px solid #e2e6f0;border-radius:14px;
                  padding:20px 18px;box-shadow:0 2px 10px rgba(0,0,0,0.05);
                  border-top:4px solid #ffc107">
        <div style="font-size:30px">🏆</div>
        <h3 style="margin:10px 0 5px;font-size:15px;color:#1a1a2e;font-weight:700">Rankings</h3>
        <p style="font-size:12px;color:#666;margin:0;line-height:1.5">
          AP &amp; Coaches polls, rank-movement history charts &amp; standings tables
        </p>
      </div>

      <div style="background:#fff;border:1px solid #e2e6f0;border-radius:14px;
                  padding:20px 18px;box-shadow:0 2px 10px rgba(0,0,0,0.05);
                  border-top:4px solid #20c997">
        <div style="font-size:30px">📋</div>
        <h3 style="margin:10px 0 5px;font-size:15px;color:#1a1a2e;font-weight:700">Custom Views</h3>
        <p style="font-size:12px;color:#666;margin:0;line-height:1.5">
          Build, save &amp; share custom charts and data tables for any league
        </p>
      </div>

    </div>
    """)

    st.html("""
    <div style="text-align:center;padding:8px 0 4px">
      <p style="font-size:1rem;font-weight:700;color:#333;margin:0 0 4px">Choose your experience</p>
      <p style="font-size:0.78rem;color:#888;margin:0">You can switch at any time from inside the app</p>
    </div>
    """)

    _mode_l, _mode_r = st.columns(2)
    with _mode_l:
        st.html("""
        <div style="border:2px solid #1e3a6e;border-radius:16px;padding:20px 16px 14px;
                    background:#f0f4ff;text-align:center;margin-bottom:4px">
          <div style="font-size:38px;margin-bottom:6px">🖥️</div>
          <div style="font-size:16px;font-weight:800;color:#1e3a6e;margin-bottom:6px">Desktop</div>
          <div style="font-size:12px;color:#555;line-height:1.5">
            Full-width layout · sidebar navigation · dense data tables · all charts
          </div>
        </div>
        """)
        if st.button("Launch Desktop Mode", type="primary", use_container_width=True, key='land_desktop'):
            st.session_state['ui_mode'] = 'desktop'
            st.session_state['app_started'] = True
            st.session_state['tos_accepted'] = False
            st.rerun()
    with _mode_r:
        st.html("""
        <div style="border:2px solid #b84a12;border-radius:16px;padding:20px 16px 14px;
                    background:#fff7f0;text-align:center;margin-bottom:4px">
          <div style="font-size:38px;margin-bottom:6px">📱</div>
          <div style="font-size:16px;font-weight:800;color:#b84a12;margin-bottom:6px">Mobile</div>
          <div style="font-size:12px;color:#555;line-height:1.5">
            Single-column · large tap targets · compact cards · readable on small screens
          </div>
        </div>
        """)
        if st.button("Launch Mobile Mode", use_container_width=True, key='land_mobile'):
            st.session_state['ui_mode'] = 'mobile'
            st.session_state['app_started'] = True
            st.session_state['tos_accepted'] = False
            st.rerun()

    st.html("""
    <div style="text-align:center;padding:16px 0 40px">
      <p style="font-size:11px;color:#bbb;margin:0">
        Select your leagues in the sidebar after entering &nbsp;·&nbsp;
        Data is cached locally so it gets faster over time
      </p>
    </div>
    """)
    st.stop()


def _render_tos():
    """Terms of Service / disclaimer page shown once after the landing page."""
    st.html("""
    <style>
    section[data-testid="stSidebar"] { display:none !important }
    #MainMenu { visibility:hidden }
    footer { visibility:hidden }
    .block-container { padding-top: 2rem !important; max-width: 820px !important; }
    </style>
    """)

    st.html("""
    <div style="text-align:center;padding:32px 20px 20px">
      <div style="font-size:52px;margin-bottom:8px">📋</div>
      <h1 style="font-size:2rem;font-weight:900;color:#1a1a2e;margin:0 0 6px">
        Terms of Use &amp; Disclaimer
      </h1>
      <p style="color:#666;font-size:0.95rem;margin:0">
        Please read and accept the following before continuing.
      </p>
    </div>
    """)

    st.html("""
    <div style="background:#fff8e1;border-left:5px solid #f59e0b;border-radius:0 12px 12px 0;
                padding:18px 24px;margin:0 0 20px;max-width:780px">
      <p style="font-weight:700;color:#92400e;margin:0 0 6px;font-size:15px">
        ⚠️  Gambling &amp; Betting Disclaimer
      </p>
      <p style="color:#78350f;font-size:13px;line-height:1.7;margin:0">
        TrulySporting displays sports statistics, scores, news and betting-related figures
        (such as odds, lines and spreads) <strong>solely for informational and entertainment
        purposes</strong>.  None of the content on this platform constitutes financial advice,
        gambling advice or a solicitation to place any wager.  Betting and gambling carry
        significant financial risk.  You should never gamble more than you can afford to lose.
        Always gamble responsibly and in accordance with the laws of your jurisdiction.
        If you or someone you know has a gambling problem, contact the
        <strong>National Problem Gambling Helpline: 1-800-522-4700</strong>.
      </p>
    </div>
    """)

    st.html("""
    <div style="background:#f0f4ff;border-left:5px solid #6366f1;border-radius:0 12px 12px 0;
                padding:18px 24px;margin:0 0 20px;max-width:780px">
      <p style="font-weight:700;color:#312e81;margin:0 0 6px;font-size:15px">
        ℹ️  Data Accuracy Disclaimer
      </p>
      <p style="color:#3730a3;font-size:13px;line-height:1.7;margin:0">
        All data displayed by TrulySporting is sourced from third-party APIs (ESPN) and is
        provided <strong>"as is"</strong>, without warranty of any kind, express or implied.
        We make <strong>no guarantee of accuracy, completeness, timeliness or validity</strong>
        of any information presented.  Data may be delayed, incomplete or contain errors.
        TrulySporting and its contributors accept <strong>no liability</strong> for any decisions
        made based on information displayed here.  You use this platform entirely at your own risk.
      </p>
    </div>
    """)

    st.html("""
    <div style="background:#f0fdf4;border-left:5px solid #22c55e;border-radius:0 12px 12px 0;
                padding:18px 24px;margin:0 0 28px;max-width:780px">
      <p style="font-weight:700;color:#14532d;margin:0 0 6px;font-size:15px">
        📜  General Terms
      </p>
      <ul style="color:#166534;font-size:13px;line-height:1.9;margin:0;padding-left:18px">
        <li>This platform is intended for users aged <strong>18 years or older</strong>.</li>
        <li>Data is fetched from ESPN&#39;s public API and cached locally; it is not
            affiliated with or endorsed by ESPN or any sports league.</li>
        <li>Features may change, be unavailable or return incomplete data at any time.</li>
        <li>By clicking <strong>"I Agree &amp; Continue"</strong> below you confirm you have
            read, understood and accepted all of the above.</li>
      </ul>
    </div>
    """)

    _, btn_col, _ = st.columns([1, 2, 1])
    with btn_col:
        if st.button("✅  I Agree & Continue", type="primary", use_container_width=True):
            st.session_state['tos_accepted'] = True
            st.rerun()
        if st.button("← Back to Start", use_container_width=True):
            st.session_state['app_started'] = False
            st.rerun()

    st.stop()


def _render_donation_page():
    """Donation / support page rendered inside the Support tab."""

    # ── Hero ──────────────────────────────────────────────────
    st.html("""
    <div style="text-align:center;padding:40px 20px 12px">
      <div style="font-size:64px;margin-bottom:10px">💚</div>
      <h1 style="font-size:2.3rem;font-weight:900;color:#1a1a2e;margin:0 0 10px">
        Support TrulySporting
      </h1>
      <p style="color:#555;font-size:1.05rem;max-width:600px;margin:0 auto;line-height:1.75">
        A <strong>free, open-source</strong> sports analytics platform built by one developer —
        no VC funding, no paywalls, no data selling. Just code and passion.
      </p>
    </div>
    """)

    # ── Origin story ─────────────────────────────────────────
    st.html("""
    <div style="max-width:780px;margin:28px auto;background:#fafafa;
                border-left:4px solid #00d632;border-radius:0 12px 12px 0;
                padding:24px 28px">
      <h2 style="font-size:1.2rem;font-weight:800;color:#1a1a2e;margin:0 0 14px">
        🌱 How it started
      </h2>
      <p style="color:#444;line-height:1.8;margin:0 0 12px;font-size:0.97rem">
        TrulySporting began as the simplest possible idea: <em>collect sports data → display it →
        share it</em>. A handful of Python lines hitting ESPN's public API and printing scores
        in a terminal. That was it.
      </p>
      <p style="color:#444;line-height:1.8;margin:0 0 12px;font-size:0.97rem">
        The data kept coming. Game histories. Standings. Rankings. Rosters. Box scores.
        Play-by-play. Odds. Weather. Injuries. News. Each new source begged for a better
        display — so a Streamlit UI appeared. Then charts. Then filters. Then custom views.
      </p>
      <p style="color:#444;line-height:1.8;margin:0;font-size:0.97rem">
        Today TrulySporting is a <strong>full analytics platform</strong>: a live scoreboard,
        team &amp; player trend analysis, roster management, a news feed, league rankings,
        a network/admin layer, a field schema explorer that can interrogate every JSON path
        ESPN exposes, and a custom view builder that lets you chart any combination of that
        data — all running locally, all free, all yours.
        <br><br>
        It still started from three words: <strong>collect → display → share</strong>.
      </p>
    </div>
    """)

    # ── Donate button ─────────────────────────────────────────
    _dc, = st.columns(1)
    with _dc:
        col_l, col_c, col_r = st.columns([1, 2, 1])
        with col_c:
            st.html("""
            <a href="https://cash.app/$slightlysigh" target="_blank" rel="noopener noreferrer"
               style="display:block;text-decoration:none">
              <div style="background:linear-gradient(135deg,#00d632 0%,#00a825 100%);
                          border-radius:16px;padding:28px 24px;text-align:center;
                          box-shadow:0 6px 24px rgba(0,214,50,0.3);cursor:pointer">
                <div style="font-size:48px;margin-bottom:8px">$</div>
                <div style="font-size:22px;font-weight:900;color:#fff;margin-bottom:4px">
                  Donate via Cash App
                </div>
                <div style="font-size:15px;color:rgba(255,255,255,0.85);margin-bottom:16px">
                  $slightlysigh
                </div>
                <div style="background:rgba(255,255,255,0.95);color:#00a825;font-weight:800;
                            font-size:15px;border-radius:50px;padding:10px 32px;
                            display:inline-block;letter-spacing:0.3px">
                  Open Cash App &rarr;
                </div>
              </div>
            </a>
            """)

    # ── What donations do ─────────────────────────────────────
    st.html("""
    <div style="display:grid;grid-template-columns:repeat(3,1fr);gap:14px;
                max-width:700px;margin:28px auto 8px;padding:0 16px">
      <div style="background:#f0fdf4;border:1px solid #bbf7d0;border-radius:12px;
                  padding:18px 16px;text-align:center">
        <div style="font-size:26px;margin-bottom:6px">☕</div>
        <div style="font-weight:700;color:#166534;font-size:14px">Buy a coffee</div>
        <div style="font-size:12px;color:#4ade80;margin-top:4px">Any amount</div>
      </div>
      <div style="background:#f0f9ff;border:1px solid #bae6fd;border-radius:12px;
                  padding:18px 16px;text-align:center">
        <div style="font-size:26px;margin-bottom:6px">🚀</div>
        <div style="font-weight:700;color:#0c4a6e;font-size:14px">Fund new features</div>
        <div style="font-size:12px;color:#38bdf8;margin-top:4px">Help us grow</div>
      </div>
      <div style="background:#fdf4ff;border:1px solid #e9d5ff;border-radius:12px;
                  padding:18px 16px;text-align:center">
        <div style="font-size:26px;margin-bottom:6px">❤️</div>
        <div style="font-weight:700;color:#581c87;font-size:14px">Show appreciation</div>
        <div style="font-size:12px;color:#c084fc;margin-top:4px">It means a lot</div>
      </div>
    </div>
    """)

    # ── Future enhancements + price estimates ─────────────────
    st.html("""
    <div style="max-width:780px;margin:36px auto 0;padding:0 8px">
      <h2 style="font-size:1.2rem;font-weight:800;color:#1a1a2e;margin:0 0 6px;
                 text-align:center">
        🗺 What's on the roadmap
      </h2>
      <p style="text-align:center;color:#666;font-size:0.9rem;margin:0 0 18px">
        Estimated development cost (honest time × fair hourly rate).
        Donations help prioritise these — the more interest, the faster they ship.
      </p>
      <table style="width:100%;border-collapse:collapse;font-size:0.92rem">
        <thead>
          <tr style="background:#1a1a2e;color:#fff">
            <th style="padding:10px 14px;text-align:left;border-radius:8px 0 0 0">Feature</th>
            <th style="padding:10px 14px;text-align:left">What it means for you</th>
            <th style="padding:10px 14px;text-align:right;border-radius:0 8px 0 0;white-space:nowrap">Est. cost</th>
          </tr>
        </thead>
        <tbody>
          <tr style="background:#f0fdf4">
            <td style="padding:10px 14px;font-weight:700;color:#166534">🔔 Game alerts</td>
            <td style="padding:10px 14px;color:#333">Push / email / SMS when a tracked team scores or a game starts</td>
            <td style="padding:10px 14px;text-align:right;font-weight:700;color:#166534">~$40</td>
          </tr>
          <tr style="background:#fff">
            <td style="padding:10px 14px;font-weight:700;color:#0c4a6e">📊 Fantasy points engine</td>
            <td style="padding:10px 14px;color:#333">Auto-calculate fantasy scores from stored box scores for any scoring format</td>
            <td style="padding:10px 14px;text-align:right;font-weight:700;color:#0c4a6e">~$60</td>
          </tr>
          <tr style="background:#f0f9ff">
            <td style="padding:10px 14px;font-weight:700;color:#0c4a6e">🤖 AI game summaries</td>
            <td style="padding:10px 14px;color:#333">LLM-generated plain-English recap for every game using stored PBP + box score</td>
            <td style="padding:10px 14px;text-align:right;font-weight:700;color:#0c4a6e">~$50</td>
          </tr>
          <tr style="background:#f0fdf4">
            <td style="padding:10px 14px;font-weight:700;color:#166534">✅ 📱 Mobile-first layout</td>
            <td style="padding:10px 14px;color:#333">Responsive card-based UI that works well on phones and tablets &mdash;
              <strong style="color:#059669">funded &amp; shipped April 2026!</strong></td>
            <td style="padding:10px 14px;text-align:right;font-weight:700;color:#059669">DONE ✨</td>
          </tr>
          <tr style="background:#fff8f0">
            <td style="padding:10px 14px;font-weight:700;color:#92400e">📈 Betting edge tracker</td>
            <td style="padding:10px 14px;color:#333">Track line movement over time from crawled odds data, surface value spots</td>
            <td style="padding:10px 14px;text-align:right;font-weight:700;color:#92400e">~$70</td>
          </tr>
          <tr style="background:#f0fdf4">
            <td style="padding:10px 14px;font-weight:700;color:#166534">🌍 Multi-language support</td>
            <td style="padding:10px 14px;color:#333">UI strings in Spanish, French, Portuguese — most ESPN data already exists globally</td>
            <td style="padding:10px 14px;text-align:right;font-weight:700;color:#166534">~$45</td>
          </tr>
          <tr style="background:#f8f0ff">
            <td style="padding:10px 14px;font-weight:700;color:#581c87">🗄 Multi-user / shared DB</td>
            <td style="padding:10px 14px;color:#333">Optional cloud sync so a team can share one database and view each other's custom views</td>
            <td style="padding:10px 14px;text-align:right;font-weight:700;color:#581c87">~$120</td>
          </tr>
          <tr style="background:#fff">
            <td style="padding:10px 14px;font-weight:700;color:#0c4a6e">📦 One-click installer</td>
            <td style="padding:10px 14px;color:#333">Packaged .exe / .app so non-developers can run TrulySporting without touching the terminal</td>
            <td style="padding:10px 14px;text-align:right;font-weight:700;color:#0c4a6e">~$55</td>
          </tr>
        </tbody>
      </table>
      <p style="text-align:center;color:#888;font-size:0.8rem;margin:10px 0 0">
        Estimates are approximate. All funded features ship as open-source updates to everyone.
      </p>
    </div>
    """)

    # ── Open-source / contribute CTA ─────────────────────────
    st.html("""
    <div style="max-width:780px;margin:32px auto 8px;
                background:linear-gradient(135deg,#1a1a2e 0%,#16213e 100%);
                border-radius:16px;padding:30px 28px;text-align:center;
                box-shadow:0 4px 20px rgba(0,0,0,0.18)">
      <div style="font-size:40px;margin-bottom:10px">🛠</div>
      <h2 style="font-size:1.15rem;font-weight:800;color:#fff;margin:0 0 10px">
        Can't donate? Code instead.
      </h2>
      <p style="color:rgba(255,255,255,0.75);font-size:0.93rem;
                line-height:1.75;max-width:560px;margin:0 auto 18px">
        TrulySporting is <strong style="color:#00d632">fully open-source</strong>.
        Every feature on the roadmap above is a viable PR.
        Found a bug? Have a better idea for the schema explorer or custom views?
        Open an issue, fork the repo, push a branch — the codebase is well-commented
        and modular by design.
      </p>
      <a href="https://github.com/unaveragetech/trulysporting"
         target="_blank" rel="noopener noreferrer"
         style="display:inline-block;background:#00d632;color:#fff;font-weight:800;
                font-size:14px;border-radius:50px;padding:11px 36px;
                text-decoration:none;letter-spacing:0.3px">
        ⭐ View on GitHub &rarr;
      </a>
    </div>
    """)

    # ── Footer note ───────────────────────────────────────────
    st.html("""
    <p style="text-align:center;font-size:11px;color:#bbb;margin:20px 0 0;line-height:1.8">
      100% of donations go directly to the developer. No obligation whatsoever.<br>
      TrulySporting will always remain free and open-source.
    </p>
    """)


# ─────────────────────────────────────────────────────────────

# ─────────────────────────────────────────────────────────────
# GOOGLE ADSENSE — ALL 3 VERIFICATION METHODS
#
# METHOD 1 — <head> injection via inject_adsense() [BeautifulSoup]:
#   Parses Streamlit's static/index.html with BS4, checks for the
#   AdSense script tag via soup.find(), backs up the pristine file,
#   then injects meta + script directly into <head>.
#
# METHOD 2 — st.html() body-level sticky banner:
#   Renders <meta>, <script>, and a visible <ins> ad unit on
#   EVERY page state (landing, ToS, main app) via st.html().
#   Google's crawler executes JS and finds this on every load.
#
# METHOD 3 — ads.txt (GitHub Pages):
#   docs/ads.txt served at unaveragetech.github.io/trulysporting/ads.txt
#   Content: google.com, pub-8003312242019311, DIRECT, f08c47fec0942fa0
#   GitHub Pages (docs/ folder on main branch) = true root-level serving.
# ─────────────────────────────────────────────────────────────
ADSENSE_CLIENT  = "ca-pub-8003312242019311"
# Base URL used for both script src checks and injection
_ADSENSE_JS_URL = "https://pagead2.googlesyndication.com/pagead/js/adsbygoogle.js"

def inject_adsense() -> None:
    """METHOD 1 — BeautifulSoup-based injection into Streamlit's index.html <head>.

    Follows the approach from comparepriceacross.com/post/integrate_google_adsense_in_streamlit_apps:
      1. Parse index.html with BeautifulSoup
      2. Check for existing AdSense script via soup.find() — avoids double-injection
      3. Backup the pristine file (or restore from backup before re-patching)
      4. Insert meta tag + Auto Ads script after <head>
    """
    if not ADSENSE_CLIENT:
        return

    try:
        from bs4 import BeautifulSoup
    except ImportError:
        logging.warning("AdSense injection skipped: install beautifulsoup4")
        return

    adsense_script_src = f"{_ADSENSE_JS_URL}?client={ADSENSE_CLIENT}"

    # The full block injected into <head>
    GA_AdSense = (
        f'\n  <!-- Google AdSense — Method 1: head injection -->\n'
        f'  <meta name="google-adsense-account" content="{ADSENSE_CLIENT}">\n'
        f'  <script async src="{adsense_script_src}"'
        f' crossorigin="anonymous"></script>\n'
    )

    index_path = pathlib.Path(st.__file__).parent / "static" / "index.html"
    logging.info(f"AdSense: editing {index_path}")

    try:
        soup = BeautifulSoup(index_path.read_text(encoding="utf-8"), features="html.parser")
    except Exception as exc:
        logging.warning(f"AdSense injection: could not read index.html — {exc}")
        return

    # soup.find("script", src=...) — proper HTML parse check, not a string search
    if not soup.find("script", src=adsense_script_src):
        bck_index = index_path.with_suffix(".bck")
        try:
            if bck_index.exists():
                shutil.copy(bck_index, index_path)   # restore clean copy first
            else:
                shutil.copy(index_path, bck_index)   # backup pristine file once

            html = str(soup)
            new_html = html.replace("<head>", "<head>\n" + GA_AdSense)
            index_path.write_text(new_html, encoding="utf-8")
            logging.info(f"AdSense injected into index.html for {ADSENSE_CLIENT}")
        except OSError as exc:
            logging.debug(f"AdSense index.html write failed (read-only fs?): {exc}")


# ── Default admin credentials (SHA-256 hashed) ──────────────────────────────
# Default credentials are pre-hashed. The plaintext values are NOT stored here.
# Change credentials via Admin Panel after first login.
# To reset: clear 'admin_password' and 'admin_pin' rows from the config table.
_ADMIN_PW_HASH  = "5e884898da28047151d0e56f8dc6292773603d0d6aabbdd62a11ef721d1542d8"
_ADMIN_PIN_HASH = "ff7faf9dc56f2a51cc8c1e19c05e5f6609f01b89cb4e4e70e5a688d3a13d7cf9"


def main():
    inject_adsense()   # no-op until ADSENSE_CLIENT / ADSENSE_SLOT are filled in
    st.set_page_config(
        page_title="TrulySporting Analytics",
        layout="wide",
        page_icon="🏆",
        initial_sidebar_state="collapsed",
    )

    st.html("""
    <style>
    /* ── Global typography ── */
    html, body, [class*="css"] {
        font-family: 'Inter', 'Segoe UI', system-ui, Arial, sans-serif;
    }
    .block-container { padding-top: 1rem !important; max-width: 1400px; }

    /* ── Tab bar — pill style ── */
    .stTabs [data-baseweb="tab-list"] {
        gap: 4px; background: #f0f2f6; padding: 6px 8px;
        border-radius: 12px; margin-bottom: 6px; flex-wrap: wrap;
    }
    .stTabs [data-baseweb="tab"] {
        font-size: 13px; font-weight: 500; padding: 6px 14px;
        border-radius: 8px; color: #555;
        border: none !important; background: transparent !important;
    }
    .stTabs [aria-selected="true"] {
        background: #ffffff !important; color: #1a1a2e !important;
        font-weight: 700 !important; box-shadow: 0 1px 5px rgba(0,0,0,0.13) !important;
    }

    /* ── Metric cards ── */
    [data-testid="stMetric"] {
        background: #fff; border: 1px solid #e4e8f0; border-radius: 12px;
        padding: 14px 18px; box-shadow: 0 2px 6px rgba(0,0,0,0.05);
    }
    [data-testid="stMetricValue"] { font-size: 28px !important; font-weight: 800 !important; }
    [data-testid="stMetricLabel"] {
        font-size: 12px !important; font-weight: 600 !important;
        text-transform: uppercase; letter-spacing: 0.6px; color: #777 !important;
    }

    /* ── Buttons ── */
    .stButton > button {
        border-radius: 9px !important; font-weight: 600 !important;
        transition: all 0.15s ease !important; letter-spacing: 0.2px;
    }
    .stButton > button:hover {
        transform: translateY(-1px);
        box-shadow: 0 4px 12px rgba(0,0,0,0.13) !important;
    }
    .stButton > button[kind="primary"] {
        background: linear-gradient(135deg,#1e3a6e,#3a6abf) !important;
        border: none !important;
    }

    /* ── Dataframes ── */
    [data-testid="stDataFrame"] {
        border-radius: 10px; overflow: hidden; border: 1px solid #e4e8f0;
    }
    [data-testid="stDataFrame"] *,
    [data-testid="stDataFrameResizable"] * { color: #111 !important; }

    /* ── Expanders ── */
    [data-testid="stExpander"] {
        border: 1px solid #e4e8f0 !important; border-radius: 12px !important;
        overflow: hidden; box-shadow: 0 1px 4px rgba(0,0,0,0.04);
    }
    [data-testid="stExpander"] summary p,
    [data-testid="stExpander"] summary span,
    [data-testid="stExpander"] p,
    [data-testid="stExpander"] span,
    [data-testid="stExpander"] li { color: #1a1a2e !important; }

    /* ── Alert boxes — ensure text is always dark & readable ── */
    [data-testid="stAlert"] p,
    [data-testid="stAlert"] span,
    [data-testid="stAlert"] li,
    [data-baseweb="notification"] p,
    [data-baseweb="notification"] span { color: #1a1a2e !important; }

    /* ── st.info blue box ── */
    [data-testid="stAlert"][kind="info"],
    div[data-testid="stAlert"] { background: #eff6ff !important; }

    /* ── Captions / small text ── */
    [data-testid="stCaptionContainer"] p { color: #444 !important; }

    /* ── Markdown rendered text ── */
    .stMarkdown p, .stMarkdown li, .stMarkdown td, .stMarkdown th { color: #1a1a2e !important; }
    .stMarkdown h1, .stMarkdown h2, .stMarkdown h3,
    .stMarkdown h4, .stMarkdown h5 { color: #111827 !important; }

    /* ── Radio / checkbox labels ── */
    [data-testid="stRadio"] label span,
    [data-testid="stCheckbox"] label span { color: #1a1a2e !important; }

    /* ── Selectbox label & number input label ── */
    label[data-testid="stWidgetLabel"] p { color: #1a1a2e !important; }

    /* ── Toggle text ── */
    [data-testid="stToggle"] label span { color: #1a1a2e !important; }

    /* ── Sidebar (dark navy) ── */
    section[data-testid="stSidebar"] { background: #111827 !important; }
    section[data-testid="stSidebar"] .stMarkdown,
    section[data-testid="stSidebar"] label,
    section[data-testid="stSidebar"] p,
    section[data-testid="stSidebar"] span { color: #d1d5db !important; }
    section[data-testid="stSidebar"] h1,
    section[data-testid="stSidebar"] h2,
    section[data-testid="stSidebar"] h3 { color: #f9fafb !important; }
    section[data-testid="stSidebar"] .stButton > button {
        background: #1f2d4a !important; color: #e5e7eb !important;
        border: 1px solid #2d4070 !important;
    }

    /* ── Links ── */
    a { color: #2563eb !important; text-decoration: none !important; }
    a:hover { text-decoration: underline !important; }

    /* ── Inputs / textareas / selects — ensure readable dark text ── */
    [data-testid="stTextInput"] input,
    [data-testid="stNumberInput"] input,
    [data-testid="stTextArea"] textarea {
        background: #ffffff !important;
        color: #1a1a2e !important;
        border: 1px solid #d0d5e0 !important;
    }
    [data-testid="stTextInput"] input::placeholder,
    [data-testid="stTextArea"] textarea::placeholder {
        color: #9ca3af !important;
    }
    /* Select / multiselect boxes */
    [data-baseweb="select"] [data-testid="stMarkdownContainer"],
    [data-baseweb="select"] div,
    [data-baseweb="select"] span,
    [data-baseweb="select"] input {
        color: #1a1a2e !important;
    }
    [data-baseweb="select"] > div {
        background: #ffffff !important;
        border-color: #d0d5e0 !important;
    }
    /* Multiselect tags */
    [data-baseweb="tag"] { background: #e8edf8 !important; }
    [data-baseweb="tag"] span { color: #1a1a2e !important; }
    /* Sidebar inputs stay readable on dark bg */
    section[data-testid="stSidebar"] [data-testid="stTextInput"] input,
    section[data-testid="stSidebar"] [data-testid="stNumberInput"] input,
    section[data-testid="stSidebar"] [data-testid="stTextArea"] textarea {
        background: #1f2d4a !important;
        color: #f3f4f6 !important;
        border-color: #2d4070 !important;
    }
    section[data-testid="stSidebar"] [data-baseweb="select"] > div {
        background: #1f2d4a !important;
        border-color: #2d4070 !important;
    }
    section[data-testid="stSidebar"] [data-baseweb="select"] div,
    section[data-testid="stSidebar"] [data-baseweb="select"] span {
        color: #f3f4f6 !important;
    }
    /* ── Scrollbars ── */
    ::-webkit-scrollbar { width: 6px; height: 6px; }
    ::-webkit-scrollbar-track { background: #f1f3f8; border-radius: 3px; }
    ::-webkit-scrollbar-thumb { background: #c1c6d4; border-radius: 3px; }
    </style>
    """)

    # ── MOBILE MODE CSS OVERRIDES ─────────────────────────────
    if st.session_state.get('ui_mode', 'desktop') == 'mobile':
        st.html("""
        <style>
        /* ── Mobile: wider content, no wasted side margin ── */
        .block-container {
            padding-top: 0.5rem !important;
            padding-left: 0.5rem !important;
            padding-right: 0.5rem !important;
            max-width: 100% !important;
        }

        /* ── Mobile: collapse sidebar by default ── */
        section[data-testid="stSidebar"] {
            min-width: 0 !important;
            width: 0 !important;
            transform: translateX(-100%) !important;
        }
        [data-testid="stSidebarCollapseButton"] { display: flex !important; }

        /* ── Mobile: larger readable font ── */
        html, body, [class*="css"] { font-size: 16px !important; }
        .stMarkdown p, .stMarkdown li { font-size: 15px !important; line-height: 1.7 !important; }
        [data-testid="stCaptionContainer"] p { font-size: 13px !important; }

        /* ── Mobile: larger tab labels for tap targets ── */
        .stTabs [data-baseweb="tab"] {
            font-size: 15px !important;
            padding: 10px 12px !important;
            min-height: 44px !important;
        }
        .stTabs [data-baseweb="tab-list"] {
            gap: 2px !important;
            padding: 4px 4px !important;
            flex-wrap: wrap !important;
        }

        /* ── Mobile: larger buttons ── */
        .stButton > button {
            min-height: 48px !important;
            font-size: 15px !important;
            padding: 10px 18px !important;
        }

        /* ── Mobile: bigger metric values ── */
        [data-testid="stMetricValue"] { font-size: 22px !important; }
        [data-testid="stMetric"] { padding: 12px 10px !important; }

        /* ── Mobile: inputs taller for easy tap ── */
        [data-testid="stTextInput"] input,
        [data-testid="stNumberInput"] input {
            min-height: 44px !important;
            font-size: 16px !important;
        }
        [data-baseweb="select"] > div {
            min-height: 44px !important;
            font-size: 15px !important;
        }

        /* ── Mobile: dataframe font legible ── */
        [data-testid="stDataFrame"] * { font-size: 13px !important; }

        /* ── Mobile: columns stack to single column ── */
        [data-testid="stHorizontalBlock"] {
            flex-direction: column !important;
        }
        [data-testid="stHorizontalBlock"] > [data-testid="stColumn"] {
            width: 100% !important;
            flex: 1 1 100% !important;
            min-width: 0 !important;
        }

        /* ── Mobile: expanders — larger header ── */
        [data-testid="stExpander"] summary {
            min-height: 48px !important;
            font-size: 15px !important;
        }

        /* ── Mobile: selectbox label ── */
        label[data-testid="stWidgetLabel"] p { font-size: 14px !important; }
        </style>
        """)

    # ── ADSENSE METHOD 2 — body-level sticky banner ──────────
    # Rendered on EVERY page state (landing, ToS, main app).
    # Includes: <meta name="google-adsense-account">, Auto Ads
    # <script>, and a visible <ins> ad unit. Google's headless
    # crawler executes JS and finds all three tags on every load.
    if ADSENSE_CLIENT:
        _adsense_src = f"{_ADSENSE_JS_URL}?client={ADSENSE_CLIENT}"
        st.html(f"""
<!-- Google AdSense — Method 2: body injection -->
<meta name="google-adsense-account" content="{ADSENSE_CLIENT}">
<script async src="{_adsense_src}" crossorigin="anonymous"></script>
<style>
  #ts-ad-bar {{
    position: fixed;
    bottom: 0; left: 0; right: 0;
    z-index: 99999;
    background: #fff;
    border-top: 1px solid #d0d5e0;
    padding: 4px 12px;
    display: flex;
    align-items: center;
    justify-content: center;
    min-height: 60px;
    box-shadow: 0 -2px 8px rgba(0,0,0,0.08);
  }}
  #ts-ad-bar ins {{ display: block; width: 100%; max-width: 728px; }}
</style>
<div id="ts-ad-bar">
  <ins class="adsbygoogle"
       style="display:block;width:100%;max-width:728px;height:90px;"
       data-ad-client="{ADSENSE_CLIENT}"
       data-ad-format="auto"
       data-full-width-responsive="true"></ins>
  <script>(adsbygoogle = window.adsbygoogle || []).push({{}});</script>
</div>
""")

    # ── INITIALISE ────────────────────────────────────────────
    # Use a schema/API version stamp so stale cached objects are always replaced
    # on deploy. Bump _APP_VER whenever new methods are added to SportsDB or ESPNWorker.
    _APP_VER = 8  # bump each time new DB/worker methods are added

    def _fresh_init():
        st.session_state.db = SportsDB()
        st.session_state.worker = ESPNWorker(st.session_state.db)
        st.session_state.worker.start()
        st.session_state._app_ver = _APP_VER

    if ('db' not in st.session_state
            or st.session_state.get('_app_ver', 0) < _APP_VER
            or not hasattr(st.session_state.get('db'), 'get_season_games_df')
            or not hasattr(st.session_state.get('worker'), 'fetch_league_leaders')):
        try:
            if hasattr(st.session_state.get('worker'), 'running'):
                st.session_state.worker.running = False
        except Exception:
            pass
        _fresh_init()

    db: SportsDB = st.session_state.db
    worker: ESPNWorker = st.session_state.worker

    # ── Seed default admin credentials (hashed) on first run ──────────────
    if not db.get_config('admin_password', ''):
        db.update_config('admin_password', _ADMIN_PW_HASH)
    if not db.get_config('admin_pin', ''):
        db.update_config('admin_pin', _ADMIN_PIN_HASH)

    # ── LANDING PAGE GATE ─────────────────────────────────
    if not st.session_state.get('app_started', False):
        _render_landing()
        return

    # ── TERMS OF SERVICE GATE ─────────────────────────────────
    if not st.session_state.get('tos_accepted', False):
        _render_tos()
        return

    # ── HOURLY DONATION NUDGE ─────────────────────────────────
    _now_ts = time.time()
    _last_nudge = st.session_state.get('_donation_nudge_at', 0)
    if _now_ts - _last_nudge >= 3600:
        st.session_state['_donation_nudge_at'] = _now_ts
        st.toast(
            "Enjoying TrulySporting? Consider [supporting us](https://cash.app/$slightlysigh) "
            "\u2014 even $1 helps keep the lights on! 💚",
            icon="💸",
        )

    # ── APP HEADER ───────────────────────────────────────────
    _active_eps_hdr = json.loads(db.get_config('active_endpoints', '[]'))
    _ep_hdr = _active_eps_hdr[0] if _active_eps_hdr else ''
    _t_hdr  = _get_sport_theme(_ep_hdr)
    _nl     = len(_active_eps_hdr)
    _ltxt   = str(_nl) + (' leagues' if _nl != 1 else ' league') + ' active'
    _ui_mode_now = st.session_state.get('ui_mode', 'desktop')
    _hdr_left, _hdr_right = st.columns([5, 1])
    with _hdr_left:
        st.html(
            '<div style="display:flex;align-items:center;gap:10px;'
            'padding:8px 4px 14px;border-bottom:2px solid #e8edf5;margin-bottom:4px">'
            '<span style="font-size:26px">' + _t_hdr['emoji'] + '</span>'
            '<div>'
            '<div style="font-size:21px;font-weight:800;color:#1a1a2e;letter-spacing:-0.3px">'
            'TrulySporting Analytics</div>'
            '<div style="font-size:11px;color:#888">Live ESPN data · ' + _ltxt + ' · Information Triage</div>'
            '</div></div>'
        )
    with _hdr_right:
        st.write('')
        _mode_label = '📱 Mobile' if _ui_mode_now == 'desktop' else '🖥️ Desktop'
        _mode_tip   = 'Switch to Mobile layout' if _ui_mode_now == 'desktop' else 'Switch to Desktop layout'
        if st.button(_mode_label, key='hdr_mode_toggle', help=_mode_tip, use_container_width=True):
            st.session_state['ui_mode'] = 'mobile' if _ui_mode_now == 'desktop' else 'desktop'
            st.rerun()


    # ── SIDEBAR ───────────────────────────────────────────────
    with st.sidebar:
        st.html('<div style="padding:4px 0 10px;font-size:17px;font-weight:800;color:#f9fafb">⚙️ Configuration</div>')

        all_eps = EndpointRegistry.get_all_keys()
        current_active = json.loads(db.get_config('active_endpoints', '[]'))

        # Quick-select buttons
        _sb_col1, _sb_col2 = st.columns(2)
        if _sb_col1.button("✅ All", use_container_width=True, help="Select all leagues"):
            current_active = all_eps
            db.update_config('active_endpoints', json.dumps(current_active))
            st.rerun()
        if _sb_col2.button("🗑 Clear", use_container_width=True, help="Deselect all leagues"):
            current_active = []
            db.update_config('active_endpoints', json.dumps(current_active))
            st.rerun()

        new_active = st.multiselect("Active Leagues", all_eps, default=current_active)

        if st.button("💾 Save Config"):
            db.update_config('active_endpoints', json.dumps(new_active))
            st.success("Saved!")

        refresh_secs = st.number_input(
            "Refresh Interval (s)",
            value=int(db.get_config('default_refresh_interval', 3600)),
            min_value=60, step=60
        )
        if st.button("Update Interval"):
            db.update_config('default_refresh_interval', str(refresh_secs))
            st.success("Updated!")

        st.divider()
        worker_status = "🟢 Running" if worker.running else "🔴 Stopped"
        st.info(f"Worker: {worker_status}")
        if worker.last_error:
            st.warning(f"Last error: {worker.last_error[:100]}")

        if st.button("🔄 Force Sync All"):
            sync_errors = []
            with st.spinner("Syncing all active leagues…"):
                for ep in new_active:
                    cat, sport = ep.split('/')
                    for etype in ['scoreboard', 'teams', 'news', 'rankings']:
                        if not EndpointRegistry.get_url(cat, sport, etype):
                            continue
                        try:
                            worker.fetch_and_process(cat, sport, etype, force_refresh=True)
                        except Exception as _e:
                            sync_errors.append(f"{ep}/{etype}: {_e}")
            if sync_errors:
                st.warning('Some fetches failed:\n' + '\n'.join(sync_errors[:5]))
            else:
                st.success("Sync complete!")


        st.divider()
        st.html(
            '<a href="https://cash.app/$slightlysigh" target="_blank" rel="noopener noreferrer" '
            'style="display:block;background:linear-gradient(135deg,#00d632,#00a825);'
            'border-radius:10px;padding:10px 14px;text-align:center;color:#fff;'
            'font-weight:700;font-size:13px;text-decoration:none;margin-bottom:8px">'
            '💸 Support the Project</a>'
        )
        if st.button('🏠 Back to Home', help='Return to landing page'):
            st.session_state['app_started'] = False
            st.rerun()

    # ── How-It-Works expander placed at the top of every tab ──────────────────
    _HOW_IT_WORKS = {
        'scoreboard': {
            'icon': '🏅',
            'summary': 'Browse and stream game results for any league you have added.',
            'steps': [
                ('1 — Add a league', 'Open the **sidebar** (▶ left edge) → "Manage Leagues" → '
                 'click **+ Add** next to any league. Active leagues appear across all tabs.'),
                ('2 — Sync scores',  'Select the league & date, then click **🔄 Sync Scoreboard**. '
                 'Results are stored locally so they load instantly on repeat visits.'),
                ('3 — Fetch full detail', 'Click any game row to expand it, then click '
                 '**📊 Fetch Summary**. This stores box scores, PBP, injuries, betting odds, '
                 'and win probability — all used by the Players & Schema tabs.'),
                ('Why is my date blank?', 'The date picker defaults to today. If your league '
                 'is in off-season, pick a date when games were played and sync again.'),
            ],
        },
        'team_trends': {
            'icon': '📈',
            'summary': 'Analyse a team\'s season-over-season form, scoring patterns, and head-to-head records.',
            'steps': [
                ('1 — Prerequisite', 'Sync the **Scoreboard** tab for this league first. '
                 'Team Trends reads from the stored game history table — no live API call needed.'),
                ('2 — Select league & team', 'Use the dropdowns at the top. If a team is missing, '
                 'go to the **Teams** tab → Load Teams first.'),
                ('3 — Pick season', 'Season year follows ESPN convention: football = year the '
                 'season *starts*; basketball/hockey = year it *ends*.'),
                ('Why is the chart empty?', 'Sync more scoreboard dates. The chart plots every '
                 'game in the stored history — the more dates you sync, the richer the view.'),
            ],
        },
        'player_trends': {
            'icon': '👤',
            'summary': 'Drill into per-player boxscore stats, game logs, and play-by-play mentions.',
            'steps': [
                ('1 — Load Teams', 'Go to the **Teams** tab → select league → **Load Teams**. '
                 'This fills the team dropdown here.'),
                ('2 — Load Roster', 'Select a team, then click **🔄 Load Roster**. '
                 'Players will appear in the dropdown.'),
                ('3 — Fetch game summaries', 'Go to **Scoreboard** → expand any game → '
                 '**📊 Fetch Summary**. Do this for multiple games.'),
                ('4 — Sync Player Stats', 'Click **🔄 Sync Player Stats** (top of this tab) '
                 'to process all stored summaries into the player boxscore table.'),
                ('5 — Build Profile', 'Select a player and click **⚙ Build Profile** to '
                 'aggregate bio, game log, and PBP data into a single cached view.'),
                ('PBP fallback', 'If no boxscore stats exist, the app auto-derives estimates '
                 'from play-by-play text (abbreviated names like *S.Darnold*).'),
            ],
        },
        'teams': {
            'icon': '🏟',
            'summary': 'Browse full team rosters, records, venues, and coaching staff.',
            'steps': [
                ('1 — Add a league', 'Add leagues via the sidebar first.'),
                ('2 — Load Teams', 'Select a league and click **Load Teams**. '
                 'This fetches all teams in the league from ESPN and caches them locally.'),
                ('3 — Load Detail',  'Click any team row to expand it, then **Load Detail** '
                 'for venue, coaching staff, and season record.'),
                ('Why are no teams listed?', 'You must click Load Teams at least once per '
                 'league. Teams are not auto-fetched to avoid unnecessary API calls.'),
            ],
        },
        'news': {
            'icon': '📰',
            'summary': 'Latest headlines and full article previews from ESPN\'s news feed.',
            'steps': [
                ('1 — Add leagues', 'Add leagues in the sidebar.'),
                ('2 — Auto-sync', 'News is fetched automatically each time the Scoreboard '
                 'tab syncs. You can also force a refresh from the sidebar.'),
                ('3 — Click to read', 'Each headline card links to the full ESPN article.'),
                ('Missing sport?', 'Not all ESPN endpoints include a news feed '
                 '(e.g. some international soccer leagues). If the feed is empty, '
                 'that league\'s ESPN API does not expose a news endpoint.'),
            ],
        },
        'rankings': {
            'icon': '🏆',
            'summary': 'Poll rankings (AP, Coaches Poll) and division/conference standings.',
            'steps': [
                ('1 — Sync Scoreboard', 'Standings and rankings are fetched as part of the '
                 'normal scoreboard sync — just sync any date for your league.'),
                ('2 — Select league', 'Use the league selector at the top of this tab.'),
                ('Standings vs Rankings', 'Standings (wins/losses) are available for all '
                 'leagues. Poll Rankings (AP 25 etc.) are only available for college sports.'),
                ('Why empty?', 'If standings are missing, the league may not be in-season '
                 'or the standings endpoint may not be available for that sport.'),
            ],
        },
        'network': {
            'icon': '🌐',
            'summary': 'Monitor the distributed job queue — worker nodes, pending jobs, and errors.',
            'steps': [
                ('What is this?', 'TrulySporting can run multiple data-fetching workers '
                 'across machines. This tab shows the health of that network.'),
                ('Local mode', 'If you\'re running a single machine, you\'ll '
                 'see one local node and a queue that clears quickly.'),
                ('Stuck jobs?', 'If jobs stay "pending" for a long time, the worker '
                 'process may have restarted. Click the local sync buttons on other '
                 'tabs to re-process them.'),
            ],
        },
        'schema': {
            'icon': '🔬',
            'summary': 'Discover every JSON field ESPN returns and build custom data views from them.',
            'steps': [
                ('1 — Crawl endpoints', 'Click **🕷 Crawl Endpoints** to fetch every ESPN '
                 'API endpoint once and record ALL JSON field paths, types, and example values. '
                 'This takes ~30 seconds and only needs to be done once (or after ESPN updates their API).'),
                ('2 — Browse fields', 'Use the Field Explorer to search by field name. '
                 'Find hidden ESPN data your parsers don\'t extract yet.'),
                ('3 — Build a View', 'Scroll to **Custom View Builder**. Pick a league, '
                 'a *data source* (any stored DB table), columns, chart type, and optional '
                 'filter. Preview updates live. Save to disk or session.'),
                ('Data Sources', 'The view builder reads **directly from your local DB** — '
                 'not from ESPN live. Sources: Game History, Standings, Rankings, Teams, '
                 'Roster, Player Boxscore Stats, Play-by-Play, News, Team Detail.'),
                ('Why are columns empty?', 'A data source shows "(0 rows)" if that table '
                 'has no data for the selected league yet. Sync or load the relevant tab first.'),
                ('Saved views', 'Views saved to disk appear on the **📋 Custom Views** tab '
                 'and persist across app restarts.'),
            ],
        },
    }

    def _render_how_it_works(key: str):
        """Render a collapsible ℹ️ How this tab works expander using _HOW_IT_WORKS dict."""
        info = _HOW_IT_WORKS.get(key)
        if not info:
            return
        with st.expander(
            f"{info['icon']} **How this tab works** — click to expand",
            expanded=False
        ):
            st.markdown(f"**{info['summary']}**")
            st.markdown("")
            for heading, body in info['steps']:
                st.markdown(f"**{heading}**")
                st.markdown(f"> {body}")
                st.markdown("")

    def _render_admin_gate(gate_key: str) -> bool:
        """Two-step admin auth (password → PIN). Returns True when fully authenticated."""
        if st.session_state.get('admin_authed', False):
            return True
        st.subheader("🔒 Admin Access Required")
        _now_g = time.time()
        _locked_until_g = st.session_state.get('_pin_locked_until', 0.0)
        _attempts_g = st.session_state.get('_pin_attempts', 0)
        if _now_g < _locked_until_g:
            _wait_g = int(_locked_until_g - _now_g)
            st.error(f"🔒 Too many failed attempts. Try again in {_wait_g}s.")
            return False
        _pw_ok_g = st.session_state.get('_admin_pw_ok', False)
        _gc, _ = st.columns([2, 3])
        if not _pw_ok_g:
            st.caption("Step 1 of 2 — enter the admin password")
            with _gc:
                _pw_in = st.text_input(
                    "Admin Password", type='password', key=f'{gate_key}_pw')
                if _attempts_g > 0:
                    st.caption(f"⚠️ {5 - _attempts_g} attempt(s) remaining before lockout.")
                if st.button("▶ Continue", key=f'{gate_key}_pw_btn'):
                    _stored_pw = db.get_config('admin_password', _ADMIN_PW_HASH)
                    if hmac.compare_digest(
                            hashlib.sha256(_pw_in.encode()).hexdigest(), _stored_pw):
                        st.session_state['_admin_pw_ok'] = True
                        st.session_state['_pin_attempts'] = 0
                        st.rerun()
                    else:
                        _attempts_g += 1
                        st.session_state['_pin_attempts'] = _attempts_g
                        if _attempts_g >= 5:
                            st.session_state['_pin_locked_until'] = time.time() + 300
                            st.session_state['_pin_attempts'] = 0
                            st.error("🔒 Too many failed attempts. Locked for 5 minutes.")
                        else:
                            st.error(
                                f"Incorrect password. {5 - _attempts_g} attempt(s) remaining.")
        else:
            st.caption("Step 2 of 2 — enter the admin PIN")
            with _gc:
                _pin_in = st.text_input(
                    "Admin PIN", type='password', key=f'{gate_key}_pin')
                if _attempts_g > 0:
                    st.caption(f"⚠️ {5 - _attempts_g} attempt(s) remaining before lockout.")
                if st.button("🔓 Unlock", key=f'{gate_key}_pin_btn'):
                    _stored_pin = db.get_config('admin_pin', _ADMIN_PIN_HASH)
                    if hmac.compare_digest(
                            hashlib.sha256(_pin_in.encode()).hexdigest(), _stored_pin):
                        st.session_state['admin_authed'] = True
                        st.session_state['_admin_pw_ok'] = False
                        st.session_state['_pin_attempts'] = 0
                        st.rerun()
                    else:
                        _attempts_g += 1
                        st.session_state['_pin_attempts'] = _attempts_g
                        if _attempts_g >= 5:
                            st.session_state['_pin_locked_until'] = time.time() + 300
                            st.session_state['_pin_attempts'] = 0
                            st.error("🔒 Too many failed attempts. Locked for 5 minutes.")
                        else:
                            st.error(
                                f"Incorrect PIN. {5 - _attempts_g} attempt(s) remaining.")
        return False

    # ── TABS ──────────────────────────────────────────────────
    tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8, tab9, tab10, tab11, tab12 = st.tabs([
        "🏅 Scoreboard",
        "📈 Team Trends",
        "👤 Player Trends",
        "🏟 Teams",
        "📰 News",
        "🏆 Rankings",
        "🌐 Network",
        "🔬 Schema Explorer",
        "🔍 Raw Inspector",
        "📋 Custom Views",
        "🛠 Admin Panel",
        "💚 Support",
    ])

    # ── TAB 1: SCOREBOARD ─────────────────────────────────────
    with tab1:
        import datetime as _dt1
        active_eps = json.loads(db.get_config('active_endpoints', '[]'))
        _ep1 = active_eps[0] if active_eps else ''
        _render_tab_banner("Scoreboard",
                           "Full-season game browser · Live scores · Box scores · PBP",
                           _ep1)
        _render_how_it_works('scoreboard')

        if not active_eps:
            st.info("Select leagues in the sidebar to get started.")
        else:
            # ── Control bar ─────────────────────────────────────
            _sb_c1, _sb_c2, _sb_c3 = st.columns([3, 2, 3])
            with _sb_c1:
                sel_ep = st.selectbox("League", active_eps, key="sb_ep")
            cat, sport = sel_ep.split('/')

            with _sb_c2:
                _sb_def_yr  = ESPNWorker._espn_season_year(cat)
                # Always ensure the default year is reachable in the list
                _sb_base_yr = max(_dt1.datetime.now().year, _sb_def_yr)
                _sb_yr_list = list(range(_sb_base_yr, _sb_base_yr - 9, -1))
                _sb_ssn_key = f'sb_season_{cat}'
                if _sb_ssn_key not in st.session_state:
                    st.session_state[_sb_ssn_key] = _sb_def_yr

                def _sb_fmt(yr_val, _cat=cat):
                    """Human-readable season range label for the year integer."""
                    if _cat == 'football':
                        return f"{yr_val}\u2013{yr_val + 1}"  # 2025 → 2025–2026
                    elif _cat == 'baseball':
                        return str(yr_val)                     # 2026 → 2026
                    else:
                        return f"{yr_val - 1}\u2013{yr_val}"  # 2026 → 2025–2026

                sb_season = st.selectbox("Season", _sb_yr_list, key=_sb_ssn_key,
                                         format_func=_sb_fmt)
                _sb_season_lbl = _sb_fmt(sb_season)

            with _sb_c3:
                _sb_status_filter = st.radio(
                    "Show",
                    ["All", "🔴 Live", "✅ Final", "🗓 Scheduled"],
                    horizontal=True, key="sb_status_filter",
                    label_visibility="collapsed"
                )

            # ── Auto-fetch on first visit to this league/season ─
            _sb_auto_key = f'sb_auto_{cat}_{sport}_{sb_season}'
            if not st.session_state.get(_sb_auto_key):
                st.session_state[_sb_auto_key] = True
                with st.spinner("Loading current schedule from ESPN…"):
                    worker.fetch_and_process(cat, sport, 'scoreboard', force_refresh=True)
                    _today8 = _dt1.datetime.now().strftime('%Y%m%d')
                    worker.fetch_date_scoreboard(cat, sport, _today8)

            # ── Load full season expander ────────────────────────
            with st.expander("📅 Load / Refresh Season Data", expanded=False):
                _lfs_c1, _lfs_c2 = st.columns([2, 1])
                with _lfs_c1:
                    st.caption(
                        f"Fetches every week / month of the **{_sb_season_lbl}** {sel_ep} season "
                        f"from ESPN in one pass. This may take 20–60 seconds depending on "
                        f"sport. Run once — results are cached."
                    )
                with _lfs_c2:
                    _sb_full_btn = st.button(f"📥 Load Full {_sb_season_lbl} Season",
                                             key="sb_full_season", type="primary")

                _sb_date_c1, _sb_date_c2 = st.columns([2, 1])
                with _sb_date_c1:
                    _sb_jump_date = st.date_input(
                        "Fetch a specific date", value=_dt1.datetime.now().date(),
                        key="sb_date_jump")
                with _sb_date_c2:
                    st.write("")
                    _sb_date_btn = st.button("📡 Fetch Date", key="sb_fetch_date")

                if _sb_date_btn:
                    with st.spinner(f"Fetching {_sb_jump_date}…"):
                        worker.fetch_date_scoreboard(cat, sport,
                                                     _sb_jump_date.strftime('%Y%m%d'))
                    st.rerun()

                if _sb_full_btn:
                    _chunks = ESPNWorker._season_date_ranges(cat, sport, sb_season)
                    _prog   = st.progress(0, text="Starting…")
                    for _ci, (_lbl, _prms) in enumerate(_chunks):
                        _prog.progress((_ci + 1) / len(_chunks),
                                       text=f"Fetching {_lbl} ({_ci+1}/{len(_chunks)})…")
                        worker.fetch_and_process(cat, sport, 'scoreboard',
                                                 force_refresh=True, params=_prms)
                    _prog.progress(1.0, text="✅ Season loaded!")
                    st.rerun()

            # ── Query DB for all season games ────────────────────
            df_games = db.get_season_games_df(cat, sport, sb_season)

            if df_games.empty:
                st.info(
                    f"No games stored for **{sel_ep}** — **{_sb_season_lbl} season** yet. "
                    f"Expand **📅 Load / Refresh Season Data** above and click "
                    f"**📥 Load Full {_sb_season_lbl} Season** to pull all games from ESPN."
                )
            else:
                # ── Apply status filter ────────────────────────
                if _sb_status_filter == "🔴 Live":
                    df_games = df_games[df_games['status'].str.contains(
                        'PROGRESS|HALF|LIVE', na=False, case=False)]
                elif _sb_status_filter == "✅ Final":
                    df_games = df_games[df_games['status'].str.contains(
                        'FINAL', na=False, case=False)]
                elif _sb_status_filter == "🗓 Scheduled":
                    df_games = df_games[~df_games['status'].str.contains(
                        'FINAL|PROGRESS|HALF|LIVE', na=False, case=False)]

                # ── Optional team search ───────────────────────
                _sb_search = st.text_input(
                    "🔍 Filter by team", placeholder="e.g. Chiefs, Lakers, Yankees…",
                    key="sb_team_filter", label_visibility="collapsed"
                )
                if _sb_search:
                    _mask = (
                        df_games['home_team'].str.contains(_sb_search, case=False, na=False) |
                        df_games['away_team'].str.contains(_sb_search, case=False, na=False) |
                        df_games.get('name', pd.Series(dtype=str)).str.contains(
                            _sb_search, case=False, na=False)
                    )
                    df_games = df_games[_mask]

                # ── Summary metrics ────────────────────────────
                _sb_all   = len(df_games)
                _sb_final = df_games['status'].str.contains('FINAL', na=False).sum()
                _sb_live  = df_games['status'].str.contains('PROGRESS|HALF|LIVE',
                                                             na=False, case=False).sum()
                _sb_sched = _sb_all - _sb_final - _sb_live

                _sm1, _sm2, _sm3, _sm4, _sm5 = st.columns([1, 1, 1, 1, 2])
                _sm1.metric("Games", _sb_all)
                _sm2.metric("Final", int(_sb_final))
                _sm3.metric("Live",  int(_sb_live))
                _sm4.metric("Scheduled", int(_sb_sched))
                with _sm5:
                    _sb_raw = st.toggle("📋 Raw Table", key="sb_raw_toggle")

                if _sb_raw:
                    _raw_cols = ['event_date', 'name', 'away_team', 'away_score',
                                 'home_score', 'home_team', 'status', 'venue',
                                 'broadcast', 'attendance', 'note']
                    _show = [c for c in _raw_cols if c in df_games.columns]
                    st.dataframe(
                        df_games[_show].rename(columns={
                            'event_date': 'Date', 'name': 'Game',
                            'away_team': 'Away', 'away_score': 'A',
                            'home_score': 'H', 'home_team': 'Home',
                            'status': 'Status', 'venue': 'Venue',
                            'broadcast': 'TV', 'attendance': 'Att', 'note': 'Note',
                        }),
                        use_container_width=True, hide_index=True,
                    )
                else:
                    # ── Render live games at the top (no grouping) ─
                    _df_live = df_games[df_games['status'].str.contains(
                        'PROGRESS|HALF|LIVE', na=False, case=False)]
                    if not _df_live.empty:
                        st.markdown("#### 🔴 In Progress")
                        for _, _g in _df_live.iterrows():
                            render_game_card(_g, db=db, worker=worker,
                                             category=cat, sport=sport)

                    # ── Group remaining games by date ──────────────
                    _df_rest = df_games[~df_games['status'].str.contains(
                        'PROGRESS|HALF|LIVE', na=False, case=False)].copy()

                    if not _df_rest.empty:
                        # Ensure event_date is string for grouping
                        _df_rest['event_date'] = _df_rest['event_date'].astype(str)
                        _dates_sorted = sorted(_df_rest['event_date'].unique(), reverse=True)
                        _today_str    = _dt1.datetime.now().strftime('%Y-%m-%d')

                        for _d in _dates_sorted:
                            _d_games = _df_rest[_df_rest['event_date'] == _d]
                            _n       = len(_d_games)
                            _fin     = int(_d_games['status'].str.contains('FINAL', na=False).sum())
                            _scd     = _n - _fin

                            _statbadge = (f"✅ {_fin} final" if _fin == _n
                                          else f"🗓 {_scd} scheduled" if _fin == 0
                                          else f"✅ {_fin}  🗓 {_scd}")

                            # Use a toggle button to collapse/expand each date group.
                            # st.expander cannot be used here because render_game_card
                            # itself contains st.expander (Streamlit forbids nesting).
                            _tog_key   = f'sb_date_open_{_d}'
                            _auto_open = (_d == _today_str or _d == _dates_sorted[0])
                            if _tog_key not in st.session_state:
                                st.session_state[_tog_key] = _auto_open

                            _hdr_col, _btn_col = st.columns([8, 1])
                            with _hdr_col:
                                st.markdown(
                                    f"**{_d}** &nbsp; · &nbsp; {_n} game{'s' if _n > 1 else ''}"
                                    f" &nbsp; · &nbsp; {_statbadge}"
                                )
                            with _btn_col:
                                _lbl_btn = "▲ Hide" if st.session_state[_tog_key] else "▼ Show"
                                if st.button(_lbl_btn, key=f'sb_tog_{_d}',
                                             use_container_width=True):
                                    st.session_state[_tog_key] = not st.session_state[_tog_key]
                                    st.rerun()

                            if st.session_state[_tog_key]:
                                for _, _g in _d_games.iterrows():
                                    render_game_card(_g, db=db, worker=worker,
                                                     category=cat, sport=sport)

                            st.divider()

    # ── TAB 2: TEAM TRENDS ────────────────────────────────────
    with tab2:
        st.subheader("📈 Team Trend Analyzer")
        _render_how_it_works('team_trends')
        _t2_active_eps = json.loads(db.get_config('active_endpoints', '[]'))

        if not _t2_active_eps:
            st.info("Add leagues in the sidebar first.")
        else:
            # ── Controls bar ───────────────────────────────────
            _t2c1, _t2c2, _t2c3, _t2c4 = st.columns([3, 2, 1, 1])
            with _t2c1:
                _t2_ep = st.selectbox("League", _t2_active_eps, key="trend_ep")
            _t2_cat, _t2_spt = _t2_ep.split('/')
            _t2_teams_df = db.get_teams_df(_t2_ep)

            with _t2c2:
                if _t2_teams_df.empty:
                    st.caption("No teams — Load Teams first.")
                    _t2_sel_tid = None
                else:
                    # Pre-select whatever is chosen in the Teams tab
                    _t2_default_id = st.session_state.get('teams3_sel', '')
                    _t2_team_options = {
                        str(r['team_id']): f"{r['team_abbr']}  —  {r['team_name']}"
                        for _, r in _t2_teams_df.iterrows()
                    }
                    _t2_ids_list = list(_t2_team_options.keys())
                    _t2_default_idx = (_t2_ids_list.index(_t2_default_id)
                                       if _t2_default_id in _t2_ids_list else 0)
                    _t2_sel_tid = st.selectbox(
                        "Team",
                        _t2_ids_list,
                        index=_t2_default_idx,
                        format_func=lambda x: _t2_team_options.get(x, x),
                        key="trend_team_id",
                    )

            _t2_season = None
            with _t2c3:
                import datetime as _dt
                _cur_yr = _dt.datetime.now().year
                _t2_def_yr  = ESPNWorker._espn_season_year(_t2_cat)
                _t2_base_yr = max(_cur_yr, _t2_def_yr)
                _t2_yr_list = list(range(_t2_base_yr, _t2_base_yr - 6, -1))
                # Pre-seed session state so Streamlit uses the correct default
                # (index= is ignored when the key is already in session_state)
                _t2_ssn_key = f'trend_season_{_t2_cat}'
                if _t2_ssn_key not in st.session_state:
                    st.session_state[_t2_ssn_key] = _t2_def_yr
                _t2_season = st.selectbox(
                    "Season", _t2_yr_list,
                    key=_t2_ssn_key,
                    format_func=lambda y, _c=_t2_cat: ESPNWorker._season_label(_c, y)
                )
                _t2_season_lbl = ESPNWorker._season_label(_t2_cat, _t2_season)

            with _t2c4:
                st.write("")
                _t2_fetch = st.button("🔄 Load", key="trend_load",
                                      help="Fetch team season schedule from ESPN")

            if _t2_sel_tid and _t2_fetch:
                with st.spinner("Fetching schedule…"):
                    worker.fetch_team_schedule(_t2_cat, _t2_spt,
                                               _t2_sel_tid, _t2_season)

            # ── Auto-load schedule on first team+season visit ───
            if _t2_sel_tid:
                _t2_auto_key = f'sched_auto_{_t2_sel_tid}_{_t2_season}'
                if not st.session_state.get(_t2_auto_key):
                    st.session_state[_t2_auto_key] = True
                    _t2_precheck = db.get_team_schedule_games(
                        _t2_cat, _t2_spt, _t2_sel_tid, _t2_season)
                    if _t2_precheck.empty:
                        with st.spinner("Loading schedule…"):
                            worker.fetch_team_schedule(_t2_cat, _t2_spt,
                                                       _t2_sel_tid, _t2_season)

            # ── Load and parse schedule ─────────────────────────
            if _t2_sel_tid:
                _t2_sched = db.get_team_schedule_games(
                    _t2_cat, _t2_spt, _t2_sel_tid, _t2_season)

                # Also get team details for colour + name
                _t2_det_df = db.get_team_detail_df(_t2_ep)
                _t2_row = _t2_teams_df[
                    _t2_teams_df['team_id'].astype(str) == str(_t2_sel_tid)]
                _t2_abbr  = _t2_row.iloc[0]['team_abbr']  if not _t2_row.empty else ''
                _t2_name  = _t2_row.iloc[0]['team_name']  if not _t2_row.empty else _t2_sel_tid
                _t2_logo  = _t2_row.iloc[0].get('logo_url', '') if not _t2_row.empty else ''
                _t2_color = '#' + str(_t2_row.iloc[0].get('color', '') or '1a73e8') \
                            if not _t2_row.empty else '#1a73e8'

                # Team header
                _h1, _h2 = st.columns([1, 6])
                with _h1:
                    if _t2_logo:
                        st.image(_t2_logo, width=70)
                with _h2:
                    st.html(f"<h3 style='margin:0;color:{_t2_color}'>"
                            f"{_t2_name} &nbsp;<span style='font-size:14px;color:#888'>"
                            f"{_t2_abbr}  ·  {_t2_season_lbl} Season</span></h3>")

                if _t2_sched.empty:
                    st.info("No schedule data available for this team / season. Try clicking **🔄 Load** to refresh from ESPN.")
                else:
                    _t2_done = _t2_sched[_t2_sched['completed'] == True].copy()

                    if _t2_done.empty:
                        st.warning("No completed games found for this season yet.")
                    else:
                        # ── Summary metrics ─────────────────────
                        _t2_wins   = int(_t2_done['won'].sum())
                        _t2_losses = int((~_t2_done['won']).sum())
                        _t2_gp     = len(_t2_done)
                        _t2_home   = _t2_done[_t2_done['home_away'] == 'H']
                        _t2_away   = _t2_done[_t2_done['home_away'] == 'A']
                        _t2_avgpts = _t2_done['my_score'].mean()
                        _t2_avgopp = _t2_done['opp_score'].mean()
                        _t2_streak = 0
                        _t2_streak_type = ''
                        for _w in _t2_done['won'].iloc[::-1]:
                            if _t2_streak == 0:
                                _t2_streak_type = 'W' if _w else 'L'
                                _t2_streak = 1
                            elif (_w and _t2_streak_type == 'W') or \
                                 (not _w and _t2_streak_type == 'L'):
                                _t2_streak += 1
                            else:
                                break
                        _t2_streak_label = f"{_t2_streak_type}{_t2_streak}"

                        _sm1, _sm2, _sm3, _sm4, _sm5, _sm6 = st.columns(6)
                        _sm1.metric("Record", f"{_t2_wins}-{_t2_losses}")
                        _sm2.metric("Win %", f"{_t2_wins / _t2_gp * 100:.1f}%")
                        _sm3.metric("PPG", f"{_t2_avgpts:.1f}")
                        _sm4.metric("OPP PPG", f"{_t2_avgopp:.1f}")
                        _sm5.metric("Point Diff", f"{(_t2_avgpts - _t2_avgopp):+.1f}")
                        _sm6.metric("Streak", _t2_streak_label)

                        st.divider()

                        # ── Chart row 1: Point Diff bar + Rolling PPG ──
                        _ch1a, _ch1b = st.columns(2)

                        with _ch1a:
                            _fig1 = go.Figure()
                            _fig1.add_trace(go.Bar(
                                x=_t2_done['date'],
                                y=_t2_done['diff'],
                                marker_color=[
                                    _t2_color if w else '#dc3545'
                                    for w in _t2_done['won']
                                ],
                                name='Point Diff',
                                hovertemplate=(
                                    '%{x|%b %d}  vs %{customdata}<br>'
                                    'Diff: %{y:+d}<extra></extra>'
                                ),
                                customdata=_t2_done['opponent'],
                            ))
                            _fig1.add_hline(y=0, line_dash='dash', line_color='#999')
                            _fig1.update_layout(
                                title='Game-by-Game Point Differential',
                                height=320, showlegend=False,
                                plot_bgcolor='#f9f9f9',
                                margin=dict(t=40, b=30, l=30, r=10),
                            )
                            st.plotly_chart(_fig1, use_container_width=True)

                        with _ch1b:
                            _roll = _t2_done.copy()
                            _roll['rolling_pts']  = _roll['my_score'].rolling(5, min_periods=1).mean()
                            _roll['rolling_opp']  = _roll['opp_score'].rolling(5, min_periods=1).mean()
                            _fig2 = go.Figure()
                            _fig2.add_trace(go.Scatter(
                                x=_roll['date'], y=_roll['rolling_pts'],
                                mode='lines', name='PPG (5-game avg)',
                                line=dict(color=_t2_color, width=2),
                            ))
                            _fig2.add_trace(go.Scatter(
                                x=_roll['date'], y=_roll['rolling_opp'],
                                mode='lines', name='OPP PPG (5-game avg)',
                                line=dict(color='#dc3545', width=2, dash='dot'),
                            ))
                            _fig2.update_layout(
                                title='Rolling 5-Game Scoring Average',
                                height=320,
                                plot_bgcolor='#f9f9f9',
                                legend=dict(orientation='h', y=-0.2),
                                margin=dict(t=40, b=30, l=30, r=10),
                            )
                            st.plotly_chart(_fig2, use_container_width=True)

                        # ── Chart row 2: Home vs Away + Win streak ─────
                        _ch2a, _ch2b = st.columns(2)

                        with _ch2a:
                            _home_w = int(_t2_home['won'].sum())
                            _home_l = int((~_t2_home['won']).sum())
                            _away_w = int(_t2_away['won'].sum())
                            _away_l = int((~_t2_away['won']).sum())
                            _fig3 = go.Figure(data=[
                                go.Bar(name='Wins',
                                       x=['Home', 'Away'],
                                       y=[_home_w, _away_w],
                                       marker_color=_t2_color),
                                go.Bar(name='Losses',
                                       x=['Home', 'Away'],
                                       y=[_home_l, _away_l],
                                       marker_color='#dc3545'),
                            ])
                            _fig3.update_layout(
                                title='Home vs Away Record',
                                barmode='group',
                                height=300,
                                plot_bgcolor='#f9f9f9',
                                legend=dict(orientation='h', y=-0.2),
                                margin=dict(t=40, b=30, l=30, r=10),
                            )
                            st.plotly_chart(_fig3, use_container_width=True)

                        with _ch2b:
                            # Running win % over season
                            _t2_done2 = _t2_done.copy().reset_index(drop=True)
                            _t2_done2['cum_wins'] = _t2_done2['won'].cumsum()
                            _t2_done2['game_num'] = _t2_done2.index + 1
                            _t2_done2['cum_win_pct'] = _t2_done2['cum_wins'] / _t2_done2['game_num'] * 100
                            _fig4 = go.Figure()
                            _fig4.add_trace(go.Scatter(
                                x=_t2_done2['game_num'],
                                y=_t2_done2['cum_win_pct'],
                                mode='lines+markers',
                                name='Win %',
                                line=dict(color=_t2_color, width=2),
                                marker=dict(size=4),
                                hovertemplate=(
                                    'Game %{x}<br>Win %%: %{y:.1f}%%<extra></extra>'
                                ),
                            ))
                            _fig4.add_hline(y=50, line_dash='dash', line_color='#999',
                                            annotation_text='.500')
                            _fig4.update_layout(
                                title='Cumulative Win % Over Season',
                                yaxis_title='Win %',
                                xaxis_title='Game #',
                                height=300,
                                plot_bgcolor='#f9f9f9',
                                margin=dict(t=40, b=30, l=30, r=10),
                            )
                            st.plotly_chart(_fig4, use_container_width=True)

                        # ── Chart row 3: Monthly scoring avg heatmap + Score distribution ─
                        _ch3a, _ch3b = st.columns(2)

                        with _ch3a:
                            _mo = _t2_done.copy()
                            _mo['month'] = _mo['date'].dt.strftime('%b')
                            _mo['month_num'] = _mo['date'].dt.month
                            _mo_grp = (_mo.groupby(['month_num', 'month'])
                                          .agg(ppg=('my_score', 'mean'),
                                               opp=('opp_score', 'mean'),
                                               gp=('my_score', 'count'))
                                          .reset_index()
                                          .sort_values('month_num'))
                            _fig5 = go.Figure()
                            _fig5.add_trace(go.Bar(
                                x=_mo_grp['month'], y=_mo_grp['ppg'],
                                name='PPG', marker_color=_t2_color,
                                text=_mo_grp['ppg'].round(1),
                                textposition='outside',
                            ))
                            _fig5.add_trace(go.Bar(
                                x=_mo_grp['month'], y=_mo_grp['opp'],
                                name='OPP PPG', marker_color='#dc3545',
                                text=_mo_grp['opp'].round(1),
                                textposition='outside',
                            ))
                            _fig5.update_layout(
                                title='Monthly Scoring Average',
                                barmode='group', height=300,
                                plot_bgcolor='#f9f9f9',
                                legend=dict(orientation='h', y=-0.25),
                                margin=dict(t=40, b=40, l=30, r=10),
                            )
                            st.plotly_chart(_fig5, use_container_width=True)

                        with _ch3b:
                            _fig6 = go.Figure()
                            _fig6.add_trace(go.Histogram(
                                x=_t2_done['my_score'],
                                name=_t2_abbr,
                                marker_color=_t2_color,
                                opacity=0.75,
                                nbinsx=20,
                            ))
                            _fig6.add_trace(go.Histogram(
                                x=_t2_done['opp_score'],
                                name='Opponent',
                                marker_color='#dc3545',
                                opacity=0.6,
                                nbinsx=20,
                            ))
                            _fig6.update_layout(
                                title='Score Distribution',
                                barmode='overlay', height=300,
                                xaxis_title='Points',
                                yaxis_title='Games',
                                plot_bgcolor='#f9f9f9',
                                legend=dict(orientation='h', y=-0.2),
                                margin=dict(t=40, b=30, l=30, r=10),
                            )
                            st.plotly_chart(_fig6, use_container_width=True)

                        # ── Results table ──────────────────────────────
                        with st.expander("📋 Full Season Results", expanded=False):
                            _res_disp = _t2_done[['date', 'home_away', 'opponent',
                                                   'my_score', 'opp_score',
                                                   'diff', 'won']].copy()
                            _res_disp.columns = ['Date', 'H/A', 'Opponent',
                                                  _t2_abbr, 'OPP', 'Diff', 'W']
                            _res_disp['Date'] = _res_disp['Date'].dt.strftime('%Y-%m-%d')
                            _res_disp['W'] = _res_disp['W'].map({True: '✓', False: '✗'})
                            _res_disp['Diff'] = _res_disp['Diff'].apply(
                                lambda v: f"{v:+.0f}")
                            st.dataframe(
                                _res_disp.sort_values('Date', ascending=False),
                                use_container_width=True, hide_index=True,
                            )

    # ── TAB 3: PLAYER TRENDS ──────────────────────────────────
    with tab3:
        import datetime as _dt3
        import json as _jpt
        _pt_cur_yr = _dt3.datetime.now().year

        _pt_active_eps = json.loads(db.get_config('active_endpoints', '[]'))
        _pt_hdr_ep = _pt_active_eps[0] if _pt_active_eps else ''
        _render_tab_banner("Player Trends",
                           "Team roster · Player profile · Season stats · Game log · PBP",
                           _pt_hdr_ep)
        _render_how_it_works('player_trends')

        if not _pt_active_eps:
            st.info("Add leagues in the sidebar first.")
        else:
            # ── Repopulate player stats from existing game summaries ──
            _pt_repop_key = 'pt_repop_done'
            _pt_repop_col1, _pt_repop_col2 = st.columns([6, 2])
            with _pt_repop_col2:
                if st.button(
                    "🔄 Sync Player Stats", key="pt_repopulate",
                    help=(
                        "Re-processes all stored game summaries to populate "
                        "per-player boxscore data. Run this once after fetching "
                        "game Summaries from the Scoreboard tab."
                    )
                ):
                    with st.spinner("Syncing player stats from stored summaries…"):
                        _n_repop = db.repopulate_player_game_stats()
                    st.success(f"Synced {_n_repop} game(s). Reload the page to see data.")
                    st.rerun()
            with _pt_repop_col1:
                _pt_pgs_conn = db.get_connection()
                _pt_pgs_count = _pt_pgs_conn.execute(
                    "SELECT COUNT(*) FROM player_game_stats"
                ).fetchone()[0]
                _pt_pgs_conn.close()
                if _pt_pgs_count == 0:
                    st.warning(
                        "No player boxscore data yet — click **🔄 Sync Player Stats** "
                        "after fetching game Summaries from the Scoreboard tab."
                    )
                else:
                    st.caption(f"📦 {_pt_pgs_count:,} boxscore stat rows stored across all leagues.")
            # ── Control row ──────────────────────────────────────
            _pt_r1c1, _pt_r1c2, _pt_r1c3 = st.columns([3, 2, 3])

            with _pt_r1c1:
                _pt_ep = st.selectbox("League", _pt_active_eps, key="pt_ep")
            _pt_cat, _pt_spt = _pt_ep.split('/')
            _pt_sport_key = _pt_ep

            with _pt_r1c2:
                _pt_def_yr  = ESPNWorker._espn_season_year(_pt_cat)
                _pt_base_yr = max(_pt_cur_yr, _pt_def_yr)
                _pt_yr_list = list(range(_pt_base_yr, _pt_base_yr - 6, -1))
                _pt_ssn_key = f'pt_season_{_pt_cat}'
                if _pt_ssn_key not in st.session_state:
                    st.session_state[_pt_ssn_key] = _pt_def_yr
                _pt_season = st.selectbox(
                    "Season", _pt_yr_list, key=_pt_ssn_key,
                    format_func=lambda y, _c=_pt_cat: ESPNWorker._season_label(_c, y)
                )
                _pt_season_lbl = ESPNWorker._season_label(_pt_cat, _pt_season)

            # ── Team selector — all teams from league first, fall back to roster-only ─
            _pt_teams_df     = db.get_teams_df(_pt_sport_key)
            _pt_roster_teams = db.get_roster_teams_df(_pt_sport_key)

            with _pt_r1c3:
                # Prefer the full teams_registry (all teams in this league).
                # Only fall back to teams-with-rosters if teams_registry is empty
                # (i.e. the user hasn't clicked Load Teams on the Teams tab yet).
                if not _pt_teams_df.empty:
                    _pt_team_opts = {
                        str(r['team_id']): f"{r['team_name']} ({r['team_abbr']})"
                        for _, r in _pt_teams_df.iterrows()
                    }
                elif not _pt_roster_teams.empty:
                    _pt_team_opts = {
                        str(r['team_id']): (
                            f"{r['team_name']} ({r['team_abbr']})"
                            if 'team_name' in r and r['team_name']
                            else f"{r['team_abbr']}"
                        )
                        for _, r in _pt_roster_teams.iterrows()
                    }
                else:
                    _pt_team_opts = {}

                if _pt_team_opts:
                    _pt_team_key = f'pt_team_{_pt_sport_key}'
                    if _pt_team_key not in st.session_state:
                        st.session_state[_pt_team_key] = list(_pt_team_opts.keys())[0]
                    _pt_sel_team_id = st.selectbox(
                        "Team", list(_pt_team_opts.keys()),
                        format_func=lambda x: _pt_team_opts.get(x, x),
                        key=_pt_team_key
                    )
                else:
                    st.caption("No teams loaded — go to 🏟 Teams tab and click Load Teams.")
                    _pt_sel_team_id = None

            # ── Load Roster button ────────────────────────────────
            if _pt_sel_team_id:
                _pt_team_abbr = ''
                if not _pt_teams_df.empty:
                    _pt_tr = _pt_teams_df[_pt_teams_df['team_id'].astype(str) == str(_pt_sel_team_id)]
                    _pt_team_abbr = _pt_tr.iloc[0]['team_abbr'] if not _pt_tr.empty else ''

                _pt_roster_df = db.get_team_roster_players(_pt_sport_key, _pt_sel_team_id)

                _pt_ra, _pt_rb = st.columns([5, 1])
                with _pt_rb:
                    _pt_load_roster = st.button(
                        "🔄 Load Roster", key="pt_load_roster",
                        help="Fetch this team's current roster from ESPN"
                    )
                if _pt_load_roster:
                    with st.spinner(f"Fetching roster for {_pt_team_abbr}…"):
                        worker.fetch_team_roster(_pt_cat, _pt_spt,
                                                 _pt_sel_team_id, _pt_team_abbr)
                    st.rerun()

                # ── Player selector ──────────────────────────────
                if _pt_roster_df.empty:
                    st.info(
                        f"No roster loaded for this team yet. "
                        f"Click **🔄 Load Roster** above to pull players from ESPN."
                    )
                    _pt_sel_player = None
                    _pt_player_id  = None
                else:
                    # Sort by position group, show jersey + name
                    _pt_player_opts = {
                        str(r['player_id']): (
                            f"#{r['jersey']}  {r['display_name']}"
                            f"  — {r['position']}"
                            + (f"  ⚠ {r['injury_status']}" if r.get('injury_status') else '')
                        )
                        for _, r in _pt_roster_df.iterrows()
                        if r['display_name']
                    }
                    _pt_player_key = f'pt_player_{_pt_sport_key}_{_pt_sel_team_id}'
                    if _pt_player_key not in st.session_state or \
                            st.session_state[_pt_player_key] not in _pt_player_opts:
                        st.session_state[_pt_player_key] = list(_pt_player_opts.keys())[0]

                    _pt_player_col1, _pt_player_col2 = st.columns([4, 1])
                    with _pt_player_col1:
                        _pt_player_id = st.selectbox(
                            "Player", list(_pt_player_opts.keys()),
                            format_func=lambda x: _pt_player_opts.get(x, x),
                            key=_pt_player_key
                        )
                    _pt_player_row = _pt_roster_df[
                        _pt_roster_df['player_id'].astype(str) == str(_pt_player_id)
                    ]
                    _pt_sel_player = _pt_player_row.iloc[0]['display_name'] \
                        if not _pt_player_row.empty else ''

                    with _pt_player_col2:
                        st.write("")
                        _pt_build_btn = st.button(
                            "⚙ Build Profile", key="pt_build_profile",
                            type="primary",
                            help="Aggregate all ESPN + boxscore + PBP data for this player"
                        )

                    # ── Load local DB data immediately — no ESPN API needed ─
                    _pgs_live  = db.get_player_game_log(
                        _pt_sport_key, _pt_sel_player, str(_pt_player_id)
                    )
                    _pbp_live  = db.get_player_pbp_mentions(_pt_sport_key, _pt_sel_player)
                    _roster_bio = _pt_player_row.iloc[0].to_dict() if not _pt_player_row.empty else {}

                    # Build profile (DB-only, no ESPN calls) only on explicit button click
                    _pt_profile_cached = db.get_player_profile(
                        _pt_sport_key, str(_pt_player_id), _pt_season
                    )
                    if _pt_build_btn:
                        with st.spinner(f"Caching profile for **{_pt_sel_player}**…"):
                            worker.build_and_cache_player_profile(
                                _pt_cat, _pt_spt,
                                _pt_player_id, _pt_sel_player,
                                _pt_sel_team_id, _pt_team_abbr,
                                _pt_season
                            )
                        _pt_profile_cached = db.get_player_profile(
                            _pt_sport_key, str(_pt_player_id), _pt_season
                        )
                        st.rerun()

                    # ── Player header card — sources: roster table ──
                    _hs_url   = _roster_bio.get('headshot_url', '')
                    _pos_lbl  = _roster_bio.get('position', '') or _roster_bio.get('position_name', '')
                    _inj_lbl  = _roster_bio.get('injury_status', '')
                    _stat_lbl = _roster_bio.get('status_name', 'Active') or 'Active'
                    _status_badge  = f'⚠ {_inj_lbl}' if _inj_lbl else _stat_lbl
                    _status_color  = '#ef4444' if _inj_lbl else '#22c55e'
                    _display_name  = _roster_bio.get('display_name', _pt_sel_player)
                    _jersey_lbl    = _roster_bio.get('jersey', '')

                    _ph1, _ph2 = st.columns([1, 5])
                    with _ph1:
                        if _hs_url:
                            st.image(_hs_url, width=90)
                    with _ph2:
                        st.markdown(
                            f"### {_display_name}"
                            f"   <span style='font-size:0.8rem;color:#888'>"
                            + (f'#{_jersey_lbl}  ·  ' if _jersey_lbl else '')
                            + f"{_pos_lbl}  ·  {_pt_team_abbr}"
                            f"  ·  <span style='color:{_status_color}'>{_status_badge}</span></span>",
                            unsafe_allow_html=True
                        )
                        _bio_parts2 = []
                        if _roster_bio.get('display_height'): _bio_parts2.append(_roster_bio['display_height'])
                        if _roster_bio.get('display_weight'): _bio_parts2.append(_roster_bio['display_weight'])
                        if _roster_bio.get('age'):            _bio_parts2.append(f"Age {_roster_bio['age']}")
                        if _roster_bio.get('college'):        _bio_parts2.append(_roster_bio['college'])
                        if _roster_bio.get('experience'):     _bio_parts2.append(f"Yr {_roster_bio['experience']}")
                        if _bio_parts2:
                            st.caption('  ·  '.join(str(x) for x in _bio_parts2 if x))
                        _data_hint = (
                            f"📦 {len(_pgs_live)} boxscore rows"
                            + (f"  ·  🎯 {len(_pbp_live)} PBP plays" if not _pbp_live.empty else '')
                            + (f"  ·  Profile cached {_pt_profile_cached.get('built_at','')[:10]}"
                               if _pt_profile_cached else "  ·  *Click ⚙ Build Profile to cache*")
                        )
                        st.caption(_data_hint)

                    st.divider()

                    # ── Sub-tabs — all data sourced from local DB ──
                    _ptsub1, _ptsub2, _ptsub3, _ptsub4 = st.tabs([
                        "📊 Stats",
                        "📅 Game Log",
                        "📈 Charts",
                        "🎯 PBP",
                    ])

                    # ══ SUB-TAB 1: STATS ═══════════════════════════
                    with _ptsub1:
                        import json as _jpt_s
                        if _pgs_live.empty:
                            st.info(
                                "No boxscore data for this player yet. "
                                "Fetch game **Summaries** from the Scoreboard tab first, "
                                "then come back here."
                            )
                        else:
                            _cats_avail = sorted(_pgs_live['category'].unique())
                            _cat_tabs_s = (
                                st.tabs([f'**{c}**' for c in _cats_avail])
                                if len(_cats_avail) > 1 else [st.container()]
                            )
                            for _ci, _cn in enumerate(_cats_avail):
                                with _cat_tabs_s[_ci]:
                                    _cf = _pgs_live[_pgs_live['category'] == _cn].copy()
                                    try:
                                        _lbl0 = _jpt_s.loads(_cf.iloc[0]['stat_labels'])
                                    except Exception:
                                        _lbl0 = []
                                    if _lbl0:
                                        _cf['_vals'] = _cf['stat_values'].apply(
                                            lambda x: _jpt_s.loads(x) if x else [])
                                        for _si, _sl in enumerate(_lbl0):
                                            _cf[_sl] = _cf['_vals'].apply(
                                                lambda v, i=_si: v[i] if i < len(v) else '')
                                        _show_cols = (
                                            ['game_date', 'team_abbr'] + _lbl0[:12]
                                        )
                                        _show_cols = [c for c in _show_cols if c in _cf.columns]
                                        _cf_disp = (
                                            _cf[_show_cols]
                                            .rename(columns={'game_date': 'Date', 'team_abbr': 'Team'})
                                            .sort_values('Date', ascending=False)
                                        )
                                        st.dataframe(_cf_disp, use_container_width=True, hide_index=True)
                                        # Season averages row
                                        _num_lbls = [
                                            l for l in _lbl0
                                            if _cf[l].apply(
                                                lambda v: str(v).replace('.', '').lstrip('-').isdigit()
                                            ).any()
                                        ]
                                        if _num_lbls:
                                            _avgs = {}
                                            for _nl in _num_lbls[:12]:
                                                try:
                                                    _avgs[_nl] = round(
                                                        _cf[_nl].apply(
                                                            lambda v: float(str(v).replace(',', ''))
                                                            if str(v).replace('.', '').lstrip('-').isdigit()
                                                            else None
                                                        ).dropna().mean(), 2
                                                    )
                                                except Exception:
                                                    pass
                                            if _avgs:
                                                st.caption(f"Season averages over {len(_cf)} games:")
                                                st.dataframe([_avgs], use_container_width=True,
                                                             hide_index=True)
                                    else:
                                        st.dataframe(
                                            _cf[['game_date', 'team_abbr',
                                                   'stat_labels', 'stat_values']],
                                            use_container_width=True, hide_index=True
                                        )

                    # ══ SUB-TAB 2: GAME LOG ════════════════════════
                    with _ptsub2:
                        import json as _jpt_g
                        if _pgs_live.empty:
                            st.info("No game log data. Fetch Summaries from the Scoreboard tab.")
                        else:
                            try:
                                _glbl0 = _jpt_g.loads(_pgs_live.iloc[0]['stat_labels'])
                            except Exception:
                                _glbl0 = []
                            _glog_df = _pgs_live.copy()
                            if _glbl0:
                                _glog_df['_vals'] = _glog_df['stat_values'].apply(
                                    lambda x: _jpt_g.loads(x) if x else [])
                                for _li, _ll in enumerate(_glbl0[:10]):
                                    _glog_df[_ll] = _glog_df['_vals'].apply(
                                        lambda v, i=_li: v[i] if i < len(v) else '')
                            _gcols = (
                                ['game_date', 'category', 'team_abbr',
                                 'home_team', 'away_team'] + (_glbl0[:10] if _glbl0 else [])
                            )
                            _gcols = [c for c in _gcols if c in _glog_df.columns]
                            _glog_disp = (
                                _glog_df[_gcols]
                                .rename(columns={
                                    'game_date': 'Date', 'category': 'Cat',
                                    'team_abbr': 'Team', 'home_team': 'Home', 'away_team': 'Away'
                                })
                                .sort_values('Date', ascending=False)
                            )
                            st.dataframe(_glog_disp, use_container_width=True, hide_index=True)
                            st.caption(f"{len(_glog_disp)} game entries")

                    # ══ SUB-TAB 3: CHARTS ══════════════════════════
                    with _ptsub3:
                        import plotly.graph_objects as _go_pt
                        import json as _jpt_c
                        if _pgs_live.empty:
                            st.info("No data to chart. Fetch Summaries from the Scoreboard tab.")
                        else:
                            _ch_cats = sorted(_pgs_live['category'].unique())
                            _ch_cat_sel = st.selectbox("Category", _ch_cats, key="pt_chart_cat")
                            _chf = _pgs_live[_pgs_live['category'] == _ch_cat_sel].copy()
                            try:
                                _ch_lbls = _jpt_c.loads(_chf.iloc[0]['stat_labels'])
                            except Exception:
                                _ch_lbls = []
                            if _ch_lbls:
                                _chf['_vals'] = _chf['stat_values'].apply(
                                    lambda x: _jpt_c.loads(x) if x else [])
                                for _li2, _ll2 in enumerate(_ch_lbls):
                                    _chf[_ll2] = _chf['_vals'].apply(
                                        lambda v, i=_li2: (
                                            float(str(v[i]).replace(',', ''))
                                            if i < len(v)
                                            and str(v[i]).replace('.', '').lstrip('-').isdigit()
                                            else None
                                        )
                                    )
                                _num_cols2 = [l for l in _ch_lbls if _chf[l].notna().any()]
                                if _num_cols2:
                                    _ch_stat2 = st.selectbox("Stat", _num_cols2, key="pt_chart_stat")
                                    _chf2 = _chf.dropna(subset=[_ch_stat2]).sort_values('game_date')
                                    _ch_mean2 = float(_chf2[_ch_stat2].mean())
                                    _fig2 = _go_pt.Figure()
                                    _fig2.add_trace(_go_pt.Bar(
                                        x=_chf2['game_date'].astype(str),
                                        y=_chf2[_ch_stat2],
                                        name=_ch_stat2,
                                        marker_color='#3b82f6', opacity=0.8,
                                    ))
                                    if len(_chf2) >= 3:
                                        _fig2.add_trace(_go_pt.Scatter(
                                            x=_chf2['game_date'].astype(str),
                                            y=_chf2[_ch_stat2].rolling(5, min_periods=1).mean(),
                                            mode='lines', name='5-game avg',
                                            line=dict(color='#f59e0b', width=2, dash='dot'),
                                        ))
                                    _fig2.add_hline(
                                        y=_ch_mean2, line_dash='dash',
                                        line_color='rgba(100,100,100,0.4)',
                                        annotation_text=f'Avg {_ch_mean2:.1f}',
                                    )
                                    _fig2.update_layout(
                                        title=f"{_display_name} — {_ch_stat2} per game",
                                        height=380, plot_bgcolor='#f9f9f9',
                                        margin=dict(t=50, b=40, l=40, r=10),
                                        legend=dict(orientation='h', y=-0.25),
                                        xaxis=dict(tickangle=-45),
                                    )
                                    st.plotly_chart(_fig2, use_container_width=True)
                                    _fig_h2 = _go_pt.Figure(_go_pt.Histogram(
                                        x=_chf2[_ch_stat2], nbinsx=20,
                                        marker_color='#6366f1', opacity=0.8,
                                    ))
                                    _fig_h2.add_vline(
                                        x=_ch_mean2, line_dash='dash', line_color='#f59e0b',
                                        annotation_text=f'Mean {_ch_mean2:.1f}',
                                    )
                                    _fig_h2.update_layout(
                                        title=f"{_ch_stat2} distribution",
                                        height=240, plot_bgcolor='#f9f9f9',
                                        margin=dict(t=40, b=30, l=40, r=10),
                                    )
                                    st.plotly_chart(_fig_h2, use_container_width=True)
                                else:
                                    st.info("No numeric stat columns found for this category.")
                            else:
                                st.info("Could not parse stat labels.")

                    # ══ SUB-TAB 4: PBP ═════════════════════════════
                    with _ptsub4:
                        if _pbp_live.empty:
                            st.info(
                                "No play-by-play data mentioning this player. "
                                "PBP is populated when game **Summaries** are fetched "
                                "from the Scoreboard tab."
                            )
                        else:
                            st.caption(
                                f"**{len(_pbp_live)} plays** mentioning *{_display_name}*"
                            )
                            _pbp_sc_only = st.checkbox("Scoring plays only", key="pbp_sc_only")
                            _pbp_show = (
                                _pbp_live[_pbp_live['scoring_play'].astype(bool)]
                                if _pbp_sc_only else _pbp_live
                            )
                            _pbp_id_cols = [c for c in
                                            ['event_id', 'event_date', 'home_team', 'away_team']
                                            if c in _pbp_show.columns]
                            _pbp_game_ids = (
                                _pbp_show[_pbp_id_cols]
                                .drop_duplicates('event_id')
                                .sort_values('event_date', ascending=False)
                                if 'event_date' in _pbp_id_cols
                                else _pbp_show[['event_id']].drop_duplicates()
                            )
                            for _, _pgr in _pbp_game_ids.iterrows():
                                _pg_lbl = (
                                    f"{str(_pgr.get('event_date', ''))[:10]}  "
                                    f"{_pgr.get('away_team', '')} @ {_pgr.get('home_team', '')}"
                                )
                                _pg_pl = _pbp_show[
                                    _pbp_show['event_id'] == _pgr['event_id']
                                ]
                                if 'period' in _pg_pl.columns:
                                    _pg_pl = _pg_pl.sort_values('period')
                                with st.expander(f"🏟 {_pg_lbl} — {len(_pg_pl)} plays"):
                                    for _, _ply in _pg_pl.iterrows():
                                        _si2 = '🏆 ' if _ply.get('scoring_play') else ''
                                        _qtr2 = f"Q{_ply.get('period', '?')} {_ply.get('clock', '')}"
                                        _sc2 = (
                                            f"{_ply.get('away_score', 0)}–"
                                            f"{_ply.get('home_score', 0)}"
                                        )
                                        st.markdown(
                                            f"{_si2}**{_qtr2}** ({_sc2})  "
                                            f"{_ply.get('play_text', '')}"
                                        )
            else:
                # No teams loaded at all
                st.info(
                    "No teams found for this league. "
                    "Go to the **🏟 Teams** tab, select the league, "
                    "click **🔄 Load Teams**, then return here."
                )

    # ── TAB 4: TEAMS ──────────────────────────────────────────
    with tab4:
        st.subheader("Teams")
        _render_how_it_works('teams')
        active_eps = json.loads(db.get_config('active_endpoints', '[]'))

        if not active_eps:
            st.info("Add leagues in the sidebar.")
        else:
            # ── Top action bar ─────────────────────────────────
            t3_c1, t3_c2, t3_c3, t3_c4 = st.columns([3, 1, 1, 1])
            with t3_c1:
                sel_ep3 = st.selectbox("League", active_eps, key="teams_ep")
            with t3_c2:
                st.write("")
                if st.button("🔄 Load Teams"):
                    cat3, spt3 = sel_ep3.split('/')
                    with st.spinner("Fetching teams…"):
                        worker.fetch_and_process(cat3, spt3, 'teams', force_refresh=True)
                    st.rerun()
            with t3_c3:
                st.write("")
                if st.button("📋 All Rosters", help="Fetch rosters for every team in this league"):
                    cat3, spt3 = sel_ep3.split('/')
                    df_t_bulk = db.get_teams_df(sel_ep3)
                    if not df_t_bulk.empty:
                        prog3 = st.progress(0, text="Fetching rosters…")
                        total3 = len(df_t_bulk)
                        for idx3, (_, tr3) in enumerate(df_t_bulk.iterrows()):
                            prog3.progress(idx3 / total3,
                                           text=f"Fetching {tr3['team_abbr']} ({idx3+1}/{total3})…")
                            worker.fetch_team_roster(cat3, spt3,
                                                     str(tr3['team_id']), tr3['team_abbr'])
                        prog3.progress(1.0, text=f"Done — {total3} rosters fetched!")
                    st.rerun()
            with t3_c4:
                st.write("")
                if st.button("📑 All Details", help="Fetch detail for every team in this league"):
                    cat3, spt3 = sel_ep3.split('/')
                    df_t_bulk2 = db.get_teams_df(sel_ep3)
                    if not df_t_bulk2.empty:
                        prog3b = st.progress(0, text="Fetching details…")
                        total3b = len(df_t_bulk2)
                        for idx3b, (_, tr3b) in enumerate(df_t_bulk2.iterrows()):
                            prog3b.progress(idx3b / total3b,
                                            text=f"Fetching {tr3b['team_abbr']} ({idx3b+1}/{total3b})…")
                            worker.fetch_team_detail(cat3, spt3,
                                                     str(tr3b['team_id']),
                                                     tr3b.get('team_slug', ''))
                        prog3b.progress(1.0, text=f"Done — {total3b} details fetched!")
                    st.rerun()

            cat3, spt3 = sel_ep3.split('/')
            df_teams   = db.get_teams_df(sel_ep3)
            df_detail3 = db.get_team_detail_df(sel_ep3)

            # ── Auto-load team list on first visit ─────────────
            _teams_auto_key = f'teams_auto_{sel_ep3}'
            if df_teams.empty and not st.session_state.get(_teams_auto_key):
                st.session_state[_teams_auto_key] = True
                with st.spinner(f"Loading {sel_ep3} teams…"):
                    worker.fetch_and_process(cat3, spt3, 'teams', force_refresh=True)
                df_teams   = db.get_teams_df(sel_ep3)
                df_detail3 = db.get_team_detail_df(sel_ep3)

            if df_teams.empty:
                st.info("No teams loaded yet — click **🔄 Load Teams** above.")
            else:
                # ── Two-column layout: list | detail ──────────────
                left3, right3 = st.columns([1, 3], gap="medium")

                # Build combined label list for the radio/selectbox
                detail_map3 = {}     # team_id → detail row
                if not df_detail3.empty:
                    for _, dr in df_detail3.iterrows():
                        # match by team_slug
                        matches = df_teams[df_teams['team_slug'] == dr['team_slug']]
                        if not matches.empty:
                            detail_map3[str(matches.iloc[0]['team_id'])] = dr

                team_ids3   = df_teams['team_id'].astype(str).tolist()
                label_map3  = {}
                for _, tr in df_teams.iterrows():
                    tid = str(tr['team_id'])
                    rec = ''
                    if tid in detail_map3:
                        rec = '  ' + str(detail_map3[tid].get('standing_summary', ''))
                    label_map3[tid] = f"{tr['team_abbr']}  —  {tr['team_name']}{rec}"

                with left3:
                    st.caption(f"{len(df_teams)} teams in {sel_ep3}")
                    t3_search = st.text_input("🔍 Filter", placeholder="Search teams…",
                                              key="t3_search", label_visibility="collapsed")
                    filtered_ids = [tid for tid in team_ids3
                                    if t3_search.lower() in label_map3[tid].lower()]

                    if not filtered_ids:
                        st.caption("No teams match your filter.")
                    else:
                        # Persist selected team across reruns via session_state
                        if 'teams3_sel' not in st.session_state or \
                                st.session_state['teams3_sel'] not in filtered_ids:
                            st.session_state['teams3_sel'] = filtered_ids[0]

                        for tid in filtered_ids:
                            is_sel = (st.session_state.get('teams3_sel') == tid)
                            tr_row = df_teams[df_teams['team_id'].astype(str) == tid].iloc[0]
                            color3  = '#' + str(tr_row.get('color', '') or '1a1a1a')
                            bg3     = f"border-left:4px solid #{tr_row.get('color','ccc')};" \
                                      f"background:{'#eef3ff' if is_sel else '#fafafa'};" \
                                      f"padding:6px 10px;border-radius:4px;margin:2px 0;" \
                                      f"cursor:pointer"
                            logo_t  = tr_row.get('logo_url', '')
                            logo_img = (f"<img src='{logo_t}' "
                                        f"style='height:28px;float:right;object-fit:contain'>") \
                                       if logo_t else ''
                            standing3 = detail_map3.get(tid, {}).get('standing_summary', '') \
                                        if tid in detail_map3 else ''
                            st.html(f"""
                            <div style="{bg3}">
                              {logo_img}
                              <div style="font-weight:{'bold' if is_sel else 'normal'};
                                          color:{color3};font-size:13px">
                                {tr_row['team_abbr']}
                              </div>
                              <div style="font-size:11px;color:#444">{tr_row['team_name']}</div>
                              {f'<div style="font-size:10px;color:#888">{standing3}</div>'
                               if standing3 else ''}
                            </div>""")
                            if st.button("Select", key=f"t3_sel_{tid}",
                                         use_container_width=True,
                                         type="primary" if is_sel else "secondary"):
                                st.session_state['teams3_sel'] = tid
                                st.rerun()

                # ── Right panel ────────────────────────────────────
                with right3:
                    sel_tid3 = st.session_state.get('teams3_sel', '')
                    if not sel_tid3:
                        st.info("Select a team on the left.")
                    else:
                        sel_row3 = df_teams[df_teams['team_id'].astype(str) == sel_tid3]
                        if sel_row3.empty:
                            st.info("Select a team on the left.")
                        else:
                            sel_row3 = sel_row3.iloc[0]
                            team_slug3  = sel_row3['team_slug']
                            team_abbr3  = sel_row3['team_abbr']
                            team_name3  = sel_row3['team_name']
                            team_color3 = '#' + str(sel_row3.get('color', '') or '1a1a1a')

                            # ── Auto-fetch detail + roster on first selection ──
                            _det_auto_key = f'det_auto_{sel_tid3}'
                            _ros_auto_key = f'ros_auto_{sel_tid3}'
                            _needs_detail = sel_tid3 not in detail_map3
                            _needs_roster = db.get_roster_df(sel_ep3, sel_tid3).empty

                            if _needs_detail and not st.session_state.get(_det_auto_key):
                                st.session_state[_det_auto_key] = True
                                with st.spinner(f"Loading {team_abbr3} details…"):
                                    worker.fetch_team_detail(cat3, spt3,
                                                             sel_tid3, team_slug3)
                                df_detail3 = db.get_team_detail_df(sel_ep3)
                                # Rebuild detail_map3 with the freshly fetched data
                                detail_map3 = {}
                                if not df_detail3.empty:
                                    for _, dr in df_detail3.iterrows():
                                        matches = df_teams[
                                            df_teams['team_slug'] == dr['team_slug']]
                                        if not matches.empty:
                                            detail_map3[
                                                str(matches.iloc[0]['team_id'])] = dr

                            if _needs_roster and not st.session_state.get(_ros_auto_key):
                                st.session_state[_ros_auto_key] = True
                                with st.spinner(f"Loading {team_abbr3} roster…"):
                                    worker.fetch_team_roster(cat3, spt3,
                                                             sel_tid3, team_abbr3)

                            # ── Action buttons row ─────────────────
                            ra1, ra2, ra3 = st.columns([1, 1, 3])
                            with ra1:
                                if st.button("🔄 Refresh Detail", key="t3_load_det"):
                                    with st.spinner(f"Fetching {team_abbr3} detail…"):
                                        worker.fetch_team_detail(cat3, spt3,
                                                                  sel_tid3, team_slug3)
                                    df_detail3 = db.get_team_detail_df(sel_ep3)
                                    st.session_state[_det_auto_key] = True
                                    st.rerun()
                            with ra2:
                                if st.button("🔄 Refresh Roster", key="t3_load_ros"):
                                    with st.spinner(f"Fetching {team_abbr3} roster…"):
                                        worker.fetch_team_roster(cat3, spt3,
                                                                  sel_tid3, team_abbr3)
                                    st.session_state[_ros_auto_key] = True
                                    st.rerun()

                            # ── Detail panel ───────────────────────
                            det3 = detail_map3.get(sel_tid3)

                            if det3 is None:
                                # No detail yet — show basic info from teams_registry
                                logo3 = sel_row3.get('logo_url', '')
                                hc1, hc2 = st.columns([1, 4])
                                with hc1:
                                    if logo3:
                                        st.image(logo3, width=80)
                                with hc2:
                                    st.markdown(f"### {team_name3}")
                                    st.caption(f"**{team_abbr3}**  ·  Detail is loading…")
                            else:
                                # ── Team header ────────────────────
                                logo3 = det3.get('logo_url') or sel_row3.get('logo_url', '')
                                hc1, hc2 = st.columns([1, 4])
                                with hc1:
                                    if logo3:
                                        st.image(logo3, width=90)
                                with hc2:
                                    st.html(f"<h3 style='color:{team_color3};margin:0'>"
                                            f"{det3.get('team_name', team_name3)}</h3>")
                                    if det3.get('standing_summary'):
                                        st.caption(f"📍 {det3['standing_summary']}")
                                    if det3.get('venue_name'):
                                        surface3 = ('🏟 Indoor' if det3.get('venue_indoor')
                                                     else '🌿 Grass' if det3.get('venue_grass')
                                                     else '🏟')
                                        st.caption(
                                            f"{surface3}  {det3['venue_name']}  ·  "
                                            f"{det3.get('venue_city','')} "
                                            f"{det3.get('venue_state','')}"
                                        )
                                    st.caption(f"Fetched: {str(det3.get('fetched_at',''))[:16]}")

                            # ── Sub-tabs: Overview | Roster ────────
                            ov_tab, ros_tab = st.tabs(["📊 Overview", "👥 Roster"])

                            with ov_tab:
                                if det3 is None:
                                    st.info("Click **📥 Load Detail** to see records, venue & upcoming games.")
                                else:
                                    # Records
                                    try:
                                        records3 = json.loads(det3.get('records_json', '{}') or '{}')
                                        if records3:
                                            st.markdown("**Season Record**")
                                            rec_cols3 = st.columns(min(len(records3), 4))
                                            for ri, (rtype, rstats) in enumerate(records3.items()):
                                                with rec_cols3[ri % 4]:
                                                    rlabel = (rtype.title()
                                                              if rtype != 'vsconf' else 'Conf')
                                                    st.metric(rlabel,
                                                              rstats.get('summary', ''))
                                                    lines3 = []
                                                    if rstats.get('winPercent'):
                                                        lines3.append(
                                                            f"Win%: {float(rstats['winPercent']):.3f}")
                                                    if rstats.get('avgPointsFor'):
                                                        lines3.append(
                                                            f"Pts/G: {float(rstats['avgPointsFor']):.1f}")
                                                    if rstats.get('avgPointsAgainst'):
                                                        lines3.append(
                                                            f"Opp/G: {float(rstats['avgPointsAgainst']):.1f}")
                                                    if lines3:
                                                        st.caption('  ·  '.join(lines3))
                                    except Exception:
                                        pass

                                    # Upcoming games
                                    try:
                                        nxt3 = json.loads(det3.get('next_event_json', '[]') or '[]')
                                        if nxt3:
                                            st.markdown("**Upcoming Games**")
                                            for ev3 in nxt3[:5]:
                                                comps3 = ev3.get('competitions', [])
                                                if comps3:
                                                    c3      = comps3[0]
                                                    dstr    = ev3.get('date', '')[:10]
                                                    nstr    = ev3.get('name', '')
                                                    sttxt   = (c3.get('status', {})
                                                                 .get('type', {})
                                                                 .get('detail', ''))
                                                    bcast3  = ' · '.join(
                                                        b.get('media', {}).get('shortName', '')
                                                        for b in c3.get('broadcasts', [])
                                                    )
                                                    st.caption(
                                                        f"📅 {dstr}  {nstr}  {sttxt}"
                                                        + (f"  📺 {bcast3}" if bcast3 else "")
                                                    )
                                    except Exception:
                                        pass

                            with ros_tab:
                                df_roster3 = db.get_roster_df(sel_ep3, sel_tid3)
                                if df_roster3.empty:
                                    st.info("Roster is loading… if it doesn't appear, click **🔄 Refresh Roster** above.")
                                else:
                                    st.caption(f"{len(df_roster3)} players  ·  "
                                               f"fetched {str(df_roster3['fetched_at'].iloc[0])[:16]}")

                                    _GRP_LBL = {
                                        'offense':              '⚔️ Offense',
                                        'defense':              '🛡 Defense',
                                        'specialTeam':          '⚡ Special Teams',
                                        'injuredReserveOrOut':  '🩺 IR / Out',
                                        'suspended':            '🚫 Suspended',
                                        'practiceSquad':        '📋 Practice Squad',
                                    }

                                    def _render_roster_group(gdf_in):
                                        gdf_in = gdf_in.copy()
                                        gdf_in['_j'] = pd.to_numeric(
                                            gdf_in['jersey'], errors='coerce').fillna(999)
                                        gdf_in = gdf_in.sort_values('_j').drop(columns=['_j'])

                                        pick = ['jersey', 'display_name']
                                        if 'position_name' in gdf_in and \
                                                gdf_in['position_name'].fillna('').str.strip().any():
                                            pick.append('position_name')
                                        pick.append('position')
                                        pick += ['display_height', 'display_weight', 'age', 'college']
                                        if 'status_name' in gdf_in:
                                            pick.append('status_name')
                                        pick.append('injury_status')
                                        pick.append('experience')
                                        if 'headshot_url' in gdf_in:
                                            pick.append('headshot_url')

                                        disp3 = gdf_in[
                                            [c for c in pick if c in gdf_in.columns]
                                        ].copy()
                                        disp3 = disp3.rename(columns={
                                            'jersey': '#', 'display_name': 'Name',
                                            'position': 'Pos', 'position_name': 'Position',
                                            'display_height': 'Ht', 'display_weight': 'Wt',
                                            'age': 'Age', 'college': 'College',
                                            'status_name': 'Status',
                                            'injury_status': 'Injury',
                                            'experience': 'Exp',
                                            'headshot_url': 'Photo',
                                        })

                                        ccfg3 = {}
                                        if 'Photo' in disp3.columns:
                                            ccfg3['Photo'] = st.column_config.ImageColumn(
                                                'Photo', width='small')

                                        def _inj_color(v):
                                            return {
                                                'Out':          'color:#dc3545;font-weight:bold',
                                                'Doubtful':     'color:#fd7e14',
                                                'Questionable': 'color:#ffc107',
                                                'IR':           'color:#6c757d',
                                                'PUP':          'color:#6c757d',
                                            }.get(str(v), '')

                                        if 'Injury' in disp3.columns:
                                            styled3 = disp3.style.map(
                                                _inj_color, subset=['Injury'])
                                        else:
                                            styled3 = disp3

                                        st.dataframe(styled3, use_container_width=True,
                                                     hide_index=True, column_config=ccfg3)

                                    active_grps3 = [
                                        g for g in df_roster3['position_group'].unique()
                                        if not df_roster3[
                                            df_roster3['position_group'] == g].empty
                                    ]
                                    grp_tab_lbls3 = [_GRP_LBL.get(g, g.title())
                                                     for g in active_grps3]

                                    if len(active_grps3) > 1:
                                        ros_grp_tabs = st.tabs(grp_tab_lbls3)
                                        for gi3, grp3 in enumerate(active_grps3):
                                            with ros_grp_tabs[gi3]:
                                                _render_roster_group(
                                                    df_roster3[
                                                        df_roster3['position_group'] == grp3])
                                    elif active_grps3:
                                        _render_roster_group(
                                            df_roster3[
                                                df_roster3['position_group'] == active_grps3[0]])

    # ── TAB 5: NEWS ───────────────────────────────────────────
    with tab5:
        st.subheader("Latest News")
        _render_how_it_works('news')
        active_eps = json.loads(db.get_config('active_endpoints', '[]'))

        if not active_eps:
            st.info("Add leagues in the sidebar.")
        else:
            col_ep4, col_lim, col_btn4 = st.columns([3, 1, 1])
            with col_ep4:
                sel_ep4 = st.selectbox("League", active_eps, key="news_ep")
            with col_lim:
                news_limit = st.number_input("Articles", value=20, min_value=5, max_value=100, step=5)
            with col_btn4:
                st.write("")
                if st.button("Refresh News"):
                    cat, sport = sel_ep4.split('/')
                    with st.spinner("Fetching news…"):
                        worker.fetch_and_process(cat, sport, 'news', force_refresh=True)

            df_news = db.get_news_df(sel_ep4, limit=int(news_limit))

            if df_news.empty:
                st.info("No news yet. Click 'Refresh News'.")
            else:
                news_raw = st.toggle("📋 View Raw Table", key='news_raw_toggle')
                if news_raw:
                    disp_news = df_news[['published', 'headline', 'byline',
                                         'article_type', 'description', 'link']].copy()
                    disp_news['published'] = disp_news['published'].str[:16]
                    disp_news['description'] = disp_news['description'].str[:120]
                    st.dataframe(
                        disp_news.rename(columns={
                            'published': 'Date', 'headline': 'Headline',
                            'byline': 'By', 'article_type': 'Type',
                            'description': 'Summary', 'link': 'URL',
                        }),
                        use_container_width=True, hide_index=True,
                    )
                else:
                    for _, row in df_news.iterrows():
                        ncol1, ncol2 = st.columns([1, 3])
                        with ncol1:
                            if row.get('image_url'):
                                st.image(row['image_url'], use_container_width=True)
                        with ncol2:
                            link = row.get('link', '')
                            headline = row.get('headline', '')
                            if link:
                                st.markdown(f"**[{headline}]({link})**")
                            else:
                                st.markdown(f"**{headline}**")

                            meta = []
                            pub = row.get('published', '')
                            if pub:
                                try:
                                    dt = datetime.fromisoformat(pub.replace('Z', '+00:00'))
                                    meta.append(dt.strftime('%b %d, %Y %H:%M'))
                                except Exception:
                                    meta.append(pub[:10])
                            if row.get('byline'):
                                meta.append(f"By {row['byline']}")
                            if row.get('article_type'):
                                meta.append(row['article_type'])
                            if meta:
                                st.caption(' · '.join(meta))

                            desc = row.get('description', '')
                            if desc:
                                st.write(desc[:300] + ('…' if len(desc) > 300 else ''))

                            try:
                                athletes = json.loads(row.get('athletes', '[]'))
                                teams_tagged = json.loads(row.get('teams', '[]'))
                                tags = []
                                if athletes:
                                    tags.append('🏃 ' + ' · '.join(athletes[:5]))
                                if teams_tagged:
                                    tags.append('🏟 ' + ' · '.join(teams_tagged[:4]))
                                if tags:
                                    st.caption(' | '.join(tags))
                            except Exception:
                                pass
                        st.divider()

    # ── TAB 6: RANKINGS & STANDINGS ──────────────────────────
    with tab6:
        st.subheader("🏆 Rankings & Standings")
        _render_how_it_works('rankings')
        _r5_all_eps = json.loads(db.get_config('active_endpoints', '[]'))

        # ── Shared chart style constants ───────────────────────
        _R5_FONT  = dict(family="'Segoe UI', Arial, sans-serif", size=12, color='#333')
        _R5_HOVER = dict(bgcolor='rgba(17,17,34,0.92)', font_color='white',
                         font_size=12, bordercolor='rgba(255,255,255,0.2)')
        _R5_AXIS  = dict(showgrid=True, gridwidth=1, gridcolor='rgba(0,0,0,0.07)',
                         zeroline=True, zerolinecolor='rgba(0,0,0,0.18)',
                         zerolinewidth=1, showline=True,
                         linecolor='rgba(0,0,0,0.15)', linewidth=1)

        def _r5_base_layout(**kw):
            return dict(
                font=_R5_FONT,
                paper_bgcolor='rgba(0,0,0,0)',
                plot_bgcolor='rgba(246,248,252,1)',
                title_font=dict(size=14, color='#1a1a2e',
                                family="'Segoe UI', Arial, sans-serif"),
                hoverlabel=_R5_HOVER,
                **kw,
            )

        def _r5_safe_color(c, fb='#1a73e8'):
            if not c or str(c).strip() in ('', 'None', '#', '#None', 'nan'):
                return fb
            s = str(c).strip()
            return s if s.startswith('#') else fb

        if not _r5_all_eps:
            st.info("Add leagues in the sidebar.")
        else:
            # ── Friendly league names ──────────────────────────
            _R5_NAMES = {
                'football/nfl':                       'NFL',
                'football/college-football':          'College Football',
                'basketball/nba':                     'NBA',
                'basketball/wnba':                    'WNBA',
                'basketball/mens-college-basketball': "Men's College Basketball",
                'basketball/womens-college-basketball': "Women's College Basketball",
                'baseball/mlb':                       'MLB',
                'baseball/college-baseball':          'College Baseball',
                'hockey/nhl':                         'NHL',
                'soccer/eng.1':                       'Premier League',
                'soccer/usa.1':                       'MLS',
            }
            def _r5_label(ep):
                return _R5_NAMES.get(ep, ep.split('/', 1)[-1].replace(
                    '-', ' ').title())

            # ── Single unified league selector ─────────────────
            _r5_hdr1, _r5_hdr2, _r5_hdr3, _r5_hdr4 = st.columns([4, 1, 1, 1])
            with _r5_hdr1:
                _r5_ep = st.selectbox(
                    "League",
                    _r5_all_eps,
                    format_func=_r5_label,
                    key="r5_league",
                )
            _r5_cat, _r5_spt = _r5_ep.split('/', 1)
            _r5_has_polls = bool(EndpointRegistry.get_url(_r5_cat, _r5_spt, 'rankings'))

            with _r5_hdr2:
                st.write("")
                if _r5_has_polls:
                    if st.button("🔄 Rankings", key="r5_load_rank"):
                        with st.spinner("Fetching rankings…"):
                            worker.fetch_and_process(
                                _r5_cat, _r5_spt, 'rankings', force_refresh=True)
                        st.rerun()
            with _r5_hdr3:
                st.write("")
                if st.button("🔄 Standings", key="r5_load_stand"):
                    with st.spinner("Fetching standings…"):
                        worker.fetch_standings(_r5_cat, _r5_spt)
                    st.rerun()
            with _r5_hdr4:
                st.write("")
                if st.button("🔄 Both", key="r5_load_both"):
                    with st.spinner("Fetching all data…"):
                        if _r5_has_polls:
                            worker.fetch_and_process(
                                _r5_cat, _r5_spt, 'rankings', force_refresh=True)
                        worker.fetch_standings(_r5_cat, _r5_spt)
                    st.rerun()

            # ══════════════════════════════════════════════════
            # SECTION A — POLL RANKINGS  (college leagues only)
            # ══════════════════════════════════════════════════
            if _r5_has_polls:
                st.markdown("### 📊 Poll Rankings")
                _r5_df = db.get_rankings_df(_r5_ep)

                if _r5_df.empty:
                    st.info("No rankings — click **🔄 Rankings** or **🔄 Both**.")
                else:
                    _r5_polls = _r5_df['poll'].unique().tolist()
                    _r5_poll_tabs = st.tabs(_r5_polls)

                    for _r5_pi, _r5_poll in enumerate(_r5_polls):
                        with _r5_poll_tabs[_r5_pi]:
                            _r5_pdf = (_r5_df[_r5_df['poll'] == _r5_poll]
                                       .sort_values('rank').head(25).copy())

                            if _r5_pdf.empty:
                                st.info("No data for this poll.")
                                continue

                            # ── 4-column metrics ──────────────
                            _r5_top = _r5_pdf.iloc[0]
                            _m1, _m2, _m3, _m4 = st.columns(4)
                            _m1.metric("#1 Team", _r5_top['team'])
                            _m2.metric("Record", _r5_top.get('record', ''))
                            _m3.metric("1st-Place Votes", int(_r5_top.get('first_place_votes', 0)))
                            _m4.metric("Teams Ranked", len(_r5_pdf))
                            st.divider()

                            # ── Movement arrows ───────────────
                            def _r5_arrow(row):
                                prev = row.get('previous_rank', 0) or 0
                                cur  = row.get('rank', 0)
                                if not prev:  return '🔵 NEW'
                                d = int(prev) - int(cur)
                                if d > 0:     return f'🟢 ▲{d}'
                                if d < 0:     return f'🔴 ▼{abs(d)}'
                                return '⚪ –'

                            _r5_disp = _r5_pdf.copy()
                            _r5_disp['Move'] = _r5_disp.apply(_r5_arrow, axis=1)

                            _r5_filt = st.text_input(
                                "🔍 Filter teams",
                                key=f"r5_filt_{_r5_pi}_{_r5_ep}",
                                placeholder="Type team name…",
                            )
                            if _r5_filt:
                                _r5_disp = _r5_disp[
                                    _r5_disp['team'].str.contains(_r5_filt, case=False, na=False)]

                            st.dataframe(
                                _r5_disp[['rank', 'Move', 'team', 'record',
                                          'points', 'first_place_votes']].rename(columns={
                                    'rank': 'Rank', 'team': 'Team', 'record': 'Record',
                                    'points': 'Points', 'first_place_votes': '1st Votes',
                                }),
                                use_container_width=True, hide_index=True,
                            )

                            # ── Chart row: Voting-points gradient bar + 1st-votes bar ──
                            _r5_ch1, _r5_ch2 = st.columns(2)

                            with _r5_ch1:
                                n_teams = len(_r5_pdf)
                                def _fade(hex_c, factor):
                                    h = _r5_safe_color(hex_c).lstrip('#')
                                    r2, g2, b2 = (int(h[i:i+2], 16) for i in (0, 2, 4))
                                    r3 = int(r2 * factor + 255 * (1 - factor))
                                    g3 = int(g2 * factor + 255 * (1 - factor))
                                    b3 = int(b2 * factor + 255 * (1 - factor))
                                    return f'rgb({r3},{g3},{b3})'
                                _r5_bar_cols = [
                                    _fade(row.get('team_color', ''), 0.95 - 0.45 * i / max(n_teams - 1, 1))
                                    for i, (_, row) in enumerate(_r5_pdf.iterrows())
                                ]
                                _r5_pfig = go.Figure(go.Bar(
                                    x=_r5_pdf['team'], y=_r5_pdf['points'],
                                    marker=dict(color=_r5_bar_cols, line=dict(width=0)),
                                    text=('#' + _r5_pdf['rank'].astype(int).astype(str)),
                                    textposition='outside', textfont=dict(size=10, color='#444'),
                                    hovertemplate='<b>#%{text} %{x}</b><br>Voting Points: <b>%{y:,}</b><extra></extra>',
                                ))
                                _r5_pfig.update_layout(**_r5_base_layout(
                                    title=dict(text=f'📊 {_r5_poll} — Voting Points', font=dict(size=13)),
                                    height=370,
                                    xaxis=dict(tickangle=-38, tickfont=dict(size=10), **_R5_AXIS),
                                    yaxis=dict(**_R5_AXIS),
                                    margin=dict(t=50, b=90, l=30, r=10),
                                    showlegend=False,
                                ))
                                st.plotly_chart(_r5_pfig, use_container_width=True)

                            with _r5_ch2:
                                _r5_fpv = (_r5_pdf[_r5_pdf['first_place_votes'] > 0]
                                           .sort_values('first_place_votes'))
                                if not _r5_fpv.empty:
                                    _r5_fpv_cols = [_r5_safe_color(r.get('team_color', ''))
                                                   for _, r in _r5_fpv.iterrows()]
                                    _r5_ffig = go.Figure(go.Bar(
                                        x=_r5_fpv['first_place_votes'], y=_r5_fpv['team'],
                                        orientation='h',
                                        marker=dict(color=_r5_fpv_cols, line=dict(width=0)),
                                        text=_r5_fpv['first_place_votes'].astype(int),
                                        textposition='outside',
                                        hovertemplate='<b>%{y}</b><br>1st-Place Votes: <b>%{x}</b><extra></extra>',
                                    ))
                                    _r5_ffig.update_layout(**_r5_base_layout(
                                        title=dict(text='🥇 1st-Place Votes', font=dict(size=13)),
                                        height=370,
                                        xaxis=dict(**_R5_AXIS),
                                        yaxis=dict(autorange='reversed', tickfont=dict(size=10), **_R5_AXIS),
                                        margin=dict(t=50, b=20, l=160, r=40),
                                        showlegend=False,
                                    ))
                                    st.plotly_chart(_r5_ffig, use_container_width=True)
                                else:
                                    st.info("No 1st-place vote data.")

                            # ── Rank movement history ─────────
                            _r5_hist = db.get_rankings_history_df(_r5_ep, _r5_poll)
                            if not _r5_hist.empty and _r5_hist['snapshot_date'].nunique() > 1:
                                st.markdown("**📈 Top-10 Rank Movement Over Time**")
                                _r5_top10_ta = (_r5_hist[_r5_hist['rank'] <= 10]['team_abbr'].unique().tolist())
                                _r5_hfig = go.Figure()
                                for _r5_ta in _r5_top10_ta:
                                    _r5_tdf = (_r5_hist[_r5_hist['team_abbr'] == _r5_ta].sort_values('snapshot_date'))
                                    _c = _r5_safe_color(_r5_tdf['team_color'].iloc[0])
                                    _r5_hfig.add_trace(go.Scatter(
                                        x=_r5_tdf['snapshot_date'], y=_r5_tdf['rank'],
                                        mode='lines+markers', name=_r5_ta,
                                        line=dict(color=_c, width=3, shape='spline'),
                                        marker=dict(size=8, color=_c, line=dict(width=2, color='white')),
                                        hovertemplate=f'<b>{_r5_ta}</b><br>Date: %{{x}}<br>Rank: <b>#%{{y}}</b><extra></extra>',
                                    ))
                                _r5_hfig.update_layout(**_r5_base_layout(
                                    title=dict(text='📈 Rank Movement (Top-10)', font=dict(size=13)),
                                    height=430,
                                    yaxis=dict(autorange='reversed', title='Rank', dtick=1,
                                               range=[10.5, 0.5], **_R5_AXIS),
                                    xaxis=dict(**_R5_AXIS),
                                    legend=dict(orientation='h', y=-0.22, font=dict(size=11)),
                                    margin=dict(t=55, b=80, l=50, r=10),
                                ))
                                st.plotly_chart(_r5_hfig, use_container_width=True)
                                st.caption(f"{_r5_hist['snapshot_date'].nunique()} snapshots · Each 🔄 Rankings load adds a new data point.")
                            elif not _r5_hist.empty:
                                st.caption("📅 Load on multiple days to build the rank-movement chart.")

            # ══════════════════════════════════════════════════
            # SECTION B — STANDINGS (all leagues)
            # ══════════════════════════════════════════════════
            st.markdown("### 📋 Standings")
            _r5s_df = db.get_standings_df(_r5_cat, _r5_spt)

            if _r5s_df.empty:
                st.info("No standings yet — click **🔄 Standings** or **🔄 Both**.")
            else:
                _r5s_best  = _r5s_df.sort_values('win_pct', ascending=False).iloc[0]
                _r5s_most  = _r5s_df.sort_values('wins',    ascending=False).iloc[0]
                _r5s_diff  = _r5s_df.sort_values('diff',    ascending=False).iloc[0]
                _r5s_worst = _r5s_df.sort_values('win_pct', ascending=True).iloc[0]
                _s1, _s2, _s3, _s4 = st.columns(4)
                _s1.metric("Best Win %",   f"{_r5s_best['team_abbr']}  {_r5s_best['win_pct']*100:.1f}%")
                _s2.metric("Most Wins",    f"{_r5s_most['team_abbr']}  {int(_r5s_most['wins'])}W")
                _s3.metric("Best Pt Diff", f"{_r5s_diff['team_abbr']}  {_r5s_diff['diff']:+.1f}")
                _s4.metric("Worst Win %",  f"{_r5s_worst['team_abbr']}  {_r5s_worst['win_pct']*100:.1f}%")

                _r5s_search = st.text_input(
                    "🔍 Filter teams", key=f"r5s_search_{_r5_ep}",
                    placeholder="Team name or abbreviation…",
                )
                st.divider()

                for _conf, _cdf in _r5s_df.groupby('conference'):
                    _cdf = _cdf.sort_values('win_pct', ascending=False)
                    if _r5s_search:
                        _cdf = _cdf[
                            _cdf['team_name'].str.contains(_r5s_search, case=False, na=False) |
                            _cdf['team_abbr'].str.contains(_r5s_search, case=False, na=False)
                        ]
                    if _cdf.empty:
                        continue
                    st.markdown(f"**{_conf}**")
                    _show = _cdf[['team_abbr', 'team_name', 'wins', 'losses']].copy()
                    _show['W%']  = (_cdf['win_pct'] * 100).round(1)
                    _show['GB']  = _cdf['gb']
                    if _cdf['ot_losses'].sum() > 0:
                        _show['OTL'] = _cdf['ot_losses'].astype(int)
                    if _cdf['ppg'].sum() > 0:
                        _show['PPG']  = _cdf['ppg'].round(1)
                        _show['OPP']  = _cdf['opp_ppg'].round(1)
                        _show['DIFF'] = _cdf['diff'].round(1)
                    if _cdf['pts'].sum() > 0:
                        _show['PTS']  = _cdf['pts'].astype(int)
                    if _cdf['streak'].apply(bool).any():
                        _show['Streak'] = _cdf['streak']
                    if _cdf['playoff_seed'].sum() > 0:
                        _show['Seed'] = _cdf['playoff_seed'].astype(int)
                    _show = _show.rename(columns={
                        'team_abbr': 'Abbr', 'team_name': 'Team',
                        'wins': 'W', 'losses': 'L',
                    })

                    def _r5s_hl(s):
                        if s.name == 'W%':
                            top = s.max()
                            return ['background-color:#d4edda;font-weight:bold'
                                    if v == top else '' for v in s]
                        if s.name == 'DIFF':
                            return ['color:#1a8a1a' if v > 0 else
                                    'color:#c0392b' if v < 0 else ''
                                    for v in s]
                        return ['' for _ in s]

                    st.dataframe(_show.style.apply(_r5s_hl),
                                 use_container_width=True, hide_index=True)

                st.divider()

                # ── Chart row 1: Wins + Win% ──────────────────
                _sc1, _sc2 = st.columns(2)
                with _sc1:
                    _srt = _r5s_df.sort_values('wins', ascending=False)
                    _cfig = go.Figure(go.Bar(
                        x=_srt['team_abbr'], y=_srt['wins'],
                        marker=dict(color=[_r5_safe_color(c) for c in _srt['team_color']], line=dict(width=0)),
                        text=_srt['wins'].astype(int), textposition='outside', textfont=dict(size=10),
                        hovertemplate='<b>%{x}</b><br>Wins: <b>%{y}</b><extra></extra>',
                    ))
                    _cfig.update_layout(**_r5_base_layout(
                        title=dict(text='🏆 Wins by Team', font=dict(size=13)),
                        height=380,
                        xaxis=dict(tickangle=-45, tickfont=dict(size=10), **_R5_AXIS),
                        yaxis=dict(**_R5_AXIS),
                        margin=dict(t=50, b=90, l=30, r=10), showlegend=False,
                    ))
                    st.plotly_chart(_cfig, use_container_width=True)

                with _sc2:
                    _wpct = _r5s_df.sort_values('win_pct', ascending=False)
                    _wfig = go.Figure(go.Bar(
                        x=_wpct['team_abbr'],
                        y=(_wpct['win_pct'] * 100).round(1),
                        marker=dict(color=[_r5_safe_color(c) for c in _wpct['team_color']], line=dict(width=0)),
                        text=(_wpct['win_pct'] * 100).round(1).astype(str) + '%',
                        textposition='outside', textfont=dict(size=10),
                        hovertemplate='<b>%{x}</b><br>Win%%: <b>%{y:.1f}%%</b><extra></extra>',
                    ))
                    _wfig.update_layout(**_r5_base_layout(
                        title=dict(text='📊 Win % by Team', font=dict(size=13)),
                        height=380,
                        xaxis=dict(tickangle=-45, tickfont=dict(size=10), **_R5_AXIS),
                        yaxis=dict(title='Win %', range=[0, 110], **_R5_AXIS),
                        margin=dict(t=50, b=90, l=30, r=10), showlegend=False,
                    ))
                    st.plotly_chart(_wfig, use_container_width=True)

                # ── Chart row 2: PPG scatter + Pt-diff bar ────
                _sc3, _sc4 = st.columns(2)
                if _r5s_df['ppg'].sum() > 0:
                    with _sc3:
                        _avg_ppg = _r5s_df['ppg'].mean()
                        _avg_opp = _r5s_df['opp_ppg'].mean()
                        _ppg_max = _r5s_df['ppg'].max()
                        _opp_min = _r5s_df['opp_ppg'].min()
                        _ppg_min = _r5s_df['ppg'].min()
                        _opp_max = _r5s_df['opp_ppg'].max()
                        _sfig = go.Figure(go.Scatter(
                            x=_r5s_df['opp_ppg'], y=_r5s_df['ppg'],
                            mode='markers+text',
                            marker=dict(
                                color=[_r5_safe_color(c) for c in _r5s_df['team_color']],
                                size=15, line=dict(width=1.5, color='rgba(0,0,0,0.25)'), opacity=0.88,
                            ),
                            text=_r5s_df['team_abbr'], textposition='top center',
                            textfont=dict(size=10, color='#222'),
                            hovertemplate='<b>%{text}</b><br>PPG: <b>%{y:.1f}</b><br>Opp PPG: <b>%{x:.1f}</b><extra></extra>',
                        ))
                        _sfig.add_hline(y=_avg_ppg, line_dash='dot',
                                        line_color='rgba(100,100,100,0.5)',
                                        annotation_text='Avg PPG', annotation_font_size=10)
                        _sfig.add_vline(x=_avg_opp, line_dash='dot',
                                        line_color='rgba(100,100,100,0.5)',
                                        annotation_text='Avg OPP', annotation_font_size=10)
                        _sfig.add_annotation(x=_opp_min + (_avg_opp - _opp_min)*0.5,
                                             y=_ppg_max, text='ELITE',
                                             font=dict(size=11, color='rgba(39,174,96,0.5)'), showarrow=False)
                        _sfig.add_annotation(x=_opp_max - (_opp_max - _avg_opp)*0.5,
                                             y=_ppg_min + 0.5, text='REBUILD',
                                             font=dict(size=11, color='rgba(231,76,60,0.5)'), showarrow=False)
                        _sfig.update_layout(**_r5_base_layout(
                            title=dict(text='🎯 Offense vs Defense', font=dict(size=13)),
                            height=420,
                            xaxis=dict(title='Opp PPG  ◀ better defense', **_R5_AXIS),
                            yaxis=dict(title='PPG  ▲ better offense', **_R5_AXIS),
                            margin=dict(t=50, b=55, l=60, r=10),
                        ))
                        st.plotly_chart(_sfig, use_container_width=True)

                    with _sc4:
                        _ddf = _r5s_df.sort_values('diff', ascending=False)
                        _dcols = ['#27ae60' if v >= 0 else '#e74c3c' for v in _ddf['diff']]
                        _dfig = go.Figure(go.Bar(
                            x=_ddf['team_abbr'], y=_ddf['diff'],
                            marker=dict(color=_dcols, line=dict(width=0)),
                            text=_ddf['diff'].round(1), textposition='outside',
                            textfont=dict(size=10),
                            hovertemplate='<b>%{x}</b><br>Pt Diff: <b>%{y:+.1f}</b><extra></extra>',
                        ))
                        _dfig.add_hline(y=0, line_color='rgba(0,0,0,0.3)', line_width=1.5)
                        _dfig.update_layout(**_r5_base_layout(
                            title=dict(text='📉 Point Differential', font=dict(size=13)),
                            height=420,
                            xaxis=dict(tickangle=-45, tickfont=dict(size=10), **_R5_AXIS),
                            yaxis=dict(**_R5_AXIS),
                            margin=dict(t=50, b=90, l=35, r=10), showlegend=False,
                        ))
                        st.plotly_chart(_dfig, use_container_width=True)

            # ══════════════════════════════════════════════════
            # SECTION C — ANIMATED SEASON REPLAY  🎬
            # ══════════════════════════════════════════════════
            st.markdown("### 🎬 Season Replay — Game by Game")
            st.caption(
                "Pick any team and watch their season unfold game-by-game "
                "with a live record tracker. Use the slider or Play button."
            )

            _r5c_teams_df = db.get_teams_df(_r5_ep)
            if _r5c_teams_df.empty:
                st.info(
                    "No team roster loaded for this league. "
                    "Go to the **🏟 Teams** tab, select this league, "
                    "click **🔄 Load Teams**, then return here."
                )
            else:
                _r5c_c1, _r5c_c2, _r5c_c3 = st.columns([4, 1, 1])
                with _r5c_c1:
                    _r5c_team_opts = {
                        str(r['team_id']): f"{r['team_abbr']}  —  {r['team_name']}"
                        for _, r in _r5c_teams_df.iterrows()
                    }
                    _r5c_ids = list(_r5c_team_opts.keys())
                    _r5c_sel_id = st.selectbox(
                        "Team", _r5c_ids,
                        format_func=lambda x: _r5c_team_opts.get(x, x),
                        key="r5c_team_id",
                    )
                import datetime as _dt2
                _r5c_cur_yr = _dt2.datetime.now().year
                _r5c_def_yr = ESPNWorker._espn_season_year(_r5_cat)
                _r5c_base_yr = max(_r5c_cur_yr, _r5c_def_yr)
                with _r5c_c2:
                    _r5c_season = st.selectbox(
                        "Season",
                        list(range(_r5c_base_yr, _r5c_base_yr - 6, -1)),
                        key="r5c_season",
                        format_func=lambda y, _c=_r5_cat: ESPNWorker._season_label(_c, y)
                    )
                _r5c_season_lbl = ESPNWorker._season_label(_r5_cat, _r5c_season)
                with _r5c_c3:
                    st.write("")
                    if st.button("🔄 Load Schedule", key="r5c_load"):
                        with st.spinner("Fetching schedule…"):
                            worker.fetch_team_schedule(
                                _r5_cat, _r5_spt, _r5c_sel_id, _r5c_season)
                        st.rerun()

                _r5c_row   = _r5c_teams_df[_r5c_teams_df['team_id'].astype(str) == str(_r5c_sel_id)]
                _r5c_abbr  = _r5c_row.iloc[0]['team_abbr']  if not _r5c_row.empty else _r5c_sel_id
                _r5c_name  = _r5c_row.iloc[0]['team_name']  if not _r5c_row.empty else _r5c_sel_id
                _r5c_color = _r5_safe_color(
                    '#' + str(_r5c_row.iloc[0].get('color', '') or '1a73e8')
                    if not _r5c_row.empty else '', '#1a73e8')

                _r5c_sched = db.get_team_schedule_games(
                    _r5_cat, _r5_spt, _r5c_sel_id, _r5c_season)
                _r5c_done = (
                    pd.DataFrame() if _r5c_sched.empty
                    else _r5c_sched[_r5c_sched['completed']]
                    .sort_values('date').reset_index(drop=True)
                )

                if _r5c_done.empty:
                    st.info(
                        f"No completed games found for **{_r5c_name}** "
                        f"({_r5c_season_lbl}). Click **🔄 Load Schedule** above."
                    )
                else:
                    _r5c_done = _r5c_done.copy()
                    _r5c_done['game_num']   = range(1, len(_r5c_done) + 1)
                    _r5c_done['col']        = _r5c_done['won'].map({True: '#27ae60', False: '#e74c3c'})
                    _r5c_done['result_str'] = _r5c_done['won'].map({True: 'WIN ✓', False: 'LOSS ✗'})
                    _r5c_done['ha_str']     = _r5c_done['home_away'].map({'H': 'Home', 'A': 'Away'})
                    _r5c_done['date_str']   = (
                        _r5c_done['date'].dt.strftime('%b %d')
                        if hasattr(_r5c_done['date'], 'dt')
                        else _r5c_done['date'].astype(str)
                    )
                    _r5c_n       = len(_r5c_done)
                    _r5c_max_abs = max(abs(_r5c_done['diff'].max()),
                                       abs(_r5c_done['diff'].min()), 1) * 1.35

                    # ── bar trace builder ─────────────────────
                    def _r5c_trace(sub):
                        _cd = sub[['opponent', 'my_score', 'opp_score',
                                   'result_str', 'ha_str', 'date_str']].values
                        # Bar text: score label on each bar e.g. "W 112‑108"
                        _txt = [
                            f"{'W' if row['won'] else 'L'} "
                            f"{int(row['my_score'])}‑{int(row['opp_score'])}"
                            for _, row in sub.iterrows()
                        ]
                        return go.Bar(
                            x=sub['game_num'].tolist(),
                            y=sub['diff'].tolist(),
                            marker=dict(
                                color=sub['col'].tolist(),
                                line=dict(width=0),
                                opacity=0.88,
                            ),
                            text=_txt,
                            textposition='outside',
                            textfont=dict(size=9, color='#333'),
                            customdata=_cd,
                            hovertemplate=(
                                '<b>Game %{x}</b>  ·  %{customdata[5]}<br>'
                                'vs <b>%{customdata[0]}</b>  (%{customdata[4]})<br>'
                                'Score: <b>%{customdata[1]:.0f} – %{customdata[2]:.0f}</b>'
                                '  (%{customdata[3]})<br>'
                                'Margin: <b>%{y:+.0f}</b>'
                                '<extra></extra>'
                            ),
                            showlegend=False,
                            name='',
                        )

                    # ── build one frame per game ───────────────
                    _r5c_frames = []
                    for _fi in range(1, _r5c_n + 1):
                        _sub = _r5c_done.iloc[:_fi]
                        _w   = int(_sub['won'].sum())
                        _l   = int((~_sub['won']).sum())
                        _pct = _w / (_w + _l) * 100 if (_w + _l) > 0 else 0
                        _r5c_frames.append(go.Frame(
                            data=[_r5c_trace(_sub)],
                            layout=go.Layout(
                                title_text=(
                                    f"🎬  {_r5c_name}  |  "
                                    f"Game {_fi} / {_r5c_n}  ·  "
                                    f"Record: {_w}W – {_l}L  ({_pct:.0f}%)"
                                ),
                            ),
                            name=str(_fi),
                        ))

                    # ── animated figure ────────────────────────
                    _r5c_fig = go.Figure(
                        data=[_r5c_trace(_r5c_done.iloc[:1])],
                        frames=_r5c_frames,
                    )
                    _r5c_fig.update_layout(
                        title=dict(
                            text=(f"🎬  {_r5c_name}  ·  Season {_r5c_season}  "
                                  f"|  Click ▶ Play to watch the season unfold"),
                            font=dict(size=14, color='#1a1a2e',
                                      family="'Segoe UI',Arial,sans-serif"),
                        ),
                        height=490,
                        paper_bgcolor='rgba(0,0,0,0)',
                        plot_bgcolor='rgba(246,248,252,1)',
                        font=_R5_FONT,
                        hoverlabel=_R5_HOVER,
                        xaxis=dict(
                            title='Game #',
                            dtick=max(1, _r5c_n // 16),
                            range=[0, _r5c_n + 2],
                            **_R5_AXIS,
                        ),
                        yaxis=dict(
                            title='Point Margin',
                            range=[-_r5c_max_abs, _r5c_max_abs],
                            **_R5_AXIS,
                        ),
                        shapes=[dict(
                            type='line', x0=0, x1=1, xref='paper',
                            y0=0, y1=0, yref='y',
                            line=dict(color='rgba(80,80,80,0.4)', width=1.5, dash='dot'),
                        )],
                        updatemenus=[dict(
                            type='buttons',
                            showactive=False,
                            y=1.16, x=0.62, xanchor='left',
                            direction='left',
                            pad=dict(t=0, r=8),
                            bgcolor='rgba(246,248,252,0.95)',
                            bordercolor='rgba(0,0,0,0.12)',
                            font=dict(size=13),
                            buttons=[
                                dict(
                                    label='  ▶  Play  ',
                                    method='animate',
                                    args=[None, dict(
                                        frame=dict(duration=450, redraw=True),
                                        fromcurrent=True,
                                        transition=dict(duration=200,
                                                        easing='cubic-in-out'),
                                    )],
                                ),
                                dict(
                                    label='  ⏸  Pause  ',
                                    method='animate',
                                    args=[[None], dict(
                                        frame=dict(duration=0, redraw=False),
                                        mode='immediate',
                                        transition=dict(duration=0),
                                    )],
                                ),
                            ],
                        )],
                        sliders=[dict(
                            active=0,
                            currentvalue=dict(
                                prefix='Game ',
                                visible=True,
                                xanchor='center',
                                font=dict(size=12, color='#444'),
                            ),
                            pad=dict(b=15, t=55),
                            bgcolor='rgba(240,240,240,0.7)',
                            bordercolor='rgba(0,0,0,0.1)',
                            tickcolor='rgba(0,0,0,0.2)',
                            font=dict(size=9, color='#666'),
                            steps=[
                                dict(
                                    method='animate',
                                    args=[[str(_si + 1)], dict(
                                        mode='immediate',
                                        frame=dict(duration=0, redraw=True),
                                        transition=dict(duration=0),
                                    )],
                                    label=str(_si + 1),
                                )
                                for _si in range(_r5c_n)
                            ],
                        )],
                        margin=dict(t=110, b=80, l=55, r=20),
                    )
                    st.plotly_chart(_r5c_fig, use_container_width=True)

                    # ── Points-per-game line chart (static, always visible) ──
                    _sc_fig = go.Figure()
                    _sc_fig.add_trace(go.Scatter(
                        x=_r5c_done['game_num'],
                        y=_r5c_done['my_score'],
                        name=f'{_r5c_abbr} Points',
                        mode='lines+markers',
                        line=dict(color=_r5c_color, width=2.5, shape='spline'),
                        marker=dict(
                            size=8, color=_r5c_done['col'].tolist(),
                            line=dict(width=1.5, color='white'),
                            symbol='circle',
                        ),
                        customdata=_r5c_done[['opponent', 'opp_score', 'result_str',
                                               'ha_str', 'date_str']].values,
                        hovertemplate=(
                            '<b>Game %{x}</b> · %{customdata[4]}<br>'
                            'vs <b>%{customdata[0]}</b> (%{customdata[3]})<br>'
                            f'{_r5c_abbr}: <b>%{{y}}</b>  |  Opp: <b>%{{customdata[1]:.0f}}</b><br>'
                            '<b>%{customdata[2]}</b><extra></extra>'
                        ),
                    ))
                    _sc_fig.add_trace(go.Scatter(
                        x=_r5c_done['game_num'],
                        y=_r5c_done['opp_score'],
                        name='Opponent Points',
                        mode='lines+markers',
                        line=dict(color='#e74c3c', width=2, shape='spline', dash='dot'),
                        marker=dict(size=6, color='#e74c3c',
                                    line=dict(width=1, color='white')),
                        customdata=_r5c_done[['opponent', 'my_score', 'result_str',
                                               'ha_str', 'date_str']].values,
                        hovertemplate=(
                            '<b>Game %{x}</b> · %{customdata[4]}<br>'
                            'vs <b>%{customdata[0]}</b> (%{customdata[3]})<br>'
                            f'{_r5c_abbr}: <b>%{{customdata[1]:.0f}}</b>  |  Opp: <b>%{{y}}</b><br>'
                            '<b>%{customdata[2]}</b><extra></extra>'
                        ),
                    ))
                    # Shaded win/loss regions
                    for _, _gr in _r5c_done.iterrows():
                        _sc_fig.add_vrect(
                            x0=_gr['game_num'] - 0.4,
                            x1=_gr['game_num'] + 0.4,
                            fillcolor='#27ae60' if _gr['won'] else '#e74c3c',
                            opacity=0.06, layer='below', line_width=0,
                        )
                    _sc_fig.update_layout(**_r5_base_layout(
                        title=dict(
                            text=f'📊 {_r5c_name} — Points Per Game  '
                                 f'(hover for details · green/red tint = W/L)',
                            font=dict(size=13)),
                        height=360,
                        xaxis=dict(title='Game #',
                                   dtick=max(1, _r5c_n // 16), **_R5_AXIS),
                        yaxis=dict(title='Points Scored', **_R5_AXIS),
                        legend=dict(orientation='h', y=1.12, font=dict(size=11)),
                        margin=dict(t=70, b=40, l=55, r=15),
                    ))
                    st.plotly_chart(_sc_fig, use_container_width=True)

                    # ── Game Detail Viewer ─────────────────────
                    with st.expander(
                        f"🔍 Game Detail Viewer — click to look up any game",
                        expanded=False,
                    ):
                        _gd_num = st.number_input(
                            "Select Game #",
                            min_value=1, max_value=_r5c_n, value=1,
                            step=1, key='r5c_game_detail_num',
                        )
                        _gd_row = _r5c_done[_r5c_done['game_num'] == _gd_num].iloc[0]
                        _gd_won     = bool(_gd_row['won'])
                        _gd_bg      = '#eafaf1' if _gd_won else '#fdf2f2'
                        _gd_border  = '#27ae60' if _gd_won else '#e74c3c'
                        _gd_badge   = '✅ WIN' if _gd_won else '❌ LOSS'
                        _gd_margin  = int(_gd_row['diff'])
                        _gd_g1, _gd_g2, _gd_g3 = st.columns(3)
                        _gd_g1.metric("Result", _gd_badge)
                        _gd_g2.metric(
                            f"{_r5c_abbr} Score",
                            int(_gd_row['my_score']),
                            delta=f"Margin: {_gd_margin:+d}",
                            delta_color='normal',
                        )
                        _gd_g3.metric("Opponent Score", int(_gd_row['opp_score']))
                        st.html(f"""
                        <div style="background:{_gd_bg};border-left:4px solid {_gd_border};
                             padding:12px 16px;border-radius:6px;font-family:'Segoe UI',sans-serif">
                          <div style="font-size:1.15rem;font-weight:700;margin-bottom:6px">
                            Game {int(_gd_num)}  ·  {_gd_badge}
                          </div>
                          <div><b>{_r5c_name}</b>
                               {'🏠 vs' if _gd_row['home_away'] == 'H' else '✈️ @'}
                               <b>{_gd_row['opponent']}</b></div>
                          <div style="margin-top:4px;color:#555">
                            📅 {_gd_row['date_str']}
                            {'  •  🏟 ' + str(_gd_row.get('venue','')) if _gd_row.get('venue') else ''}
                            {'  •  📺 ' + str(_gd_row.get('broadcast','')) if _gd_row.get('broadcast') else ''}
                          </div>
                          <div style="margin-top:8px;font-size:1.4rem;font-weight:700;color:{_gd_border}">
                            {int(_gd_row['my_score'])} – {int(_gd_row['opp_score'])}
                          </div>
                          <div style="margin-top:2px;color:#777;font-size:0.88rem">
                            Point margin: {_gd_margin:+d}
                          </div>
                        </div>""")


                    st.divider()
                    _r5c_wins_total = int(_r5c_done['won'].sum())
                    _r5c_loss_total = int((~_r5c_done['won']).sum())
                    _r5c_avg_diff   = _r5c_done['diff'].mean()
                    _r5c_biggest_w  = (
                        _r5c_done[_r5c_done['won']]['diff'].max()
                        if _r5c_done['won'].any() else float('nan')
                    )
                    _sm1, _sm2, _sm3, _sm4 = st.columns(4)
                    _sm1.metric("Final Record",
                                f"{_r5c_wins_total}W – {_r5c_loss_total}L")
                    _sm2.metric("Win %",
                                f"{_r5c_wins_total / _r5c_n * 100:.1f}%")
                    _sm3.metric("Avg Margin", f"{_r5c_avg_diff:+.1f}")
                    _sm4.metric("Biggest Win",
                                f"+{_r5c_biggest_w:.0f}"
                                if not pd.isna(_r5c_biggest_w) else "N/A")

                    # ── Static breakdown charts ────────────────
                    _r5c_bc1, _r5c_bc2 = st.columns(2)

                    with _r5c_bc1:
                        # W-L stacked bar vs each opponent
                        _opp_grp = (
                            _r5c_done.groupby('opponent')['won']
                            .agg(W='sum', L=lambda x: (~x).sum())
                            .reset_index()
                            .sort_values('W', ascending=True)
                        )
                        _opp_fig = go.Figure()
                        _opp_fig.add_trace(go.Bar(
                            x=_opp_grp['W'], y=_opp_grp['opponent'],
                            orientation='h', name='WIN',
                            marker=dict(color='#27ae60', line=dict(width=0)),
                            hovertemplate='<b>%{y}</b><br>Wins: <b>%{x}</b><extra></extra>',
                        ))
                        _opp_fig.add_trace(go.Bar(
                            x=_opp_grp['L'], y=_opp_grp['opponent'],
                            orientation='h', name='LOSS',
                            marker=dict(color='#e74c3c', line=dict(width=0)),
                            hovertemplate='<b>%{y}</b><br>Losses: <b>%{x}</b><extra></extra>',
                        ))
                        _opp_fig.update_layout(**_r5_base_layout(
                            title=dict(text='W-L vs Each Opponent', font=dict(size=13)),
                            barmode='stack',
                            height=max(300, len(_opp_grp) * 22 + 80),
                            xaxis=dict(title='Games', **_R5_AXIS),
                            yaxis=dict(autorange='reversed', tickfont=dict(size=10), **_R5_AXIS),
                            legend=dict(orientation='h', y=1.08, font=dict(size=11)),
                            margin=dict(t=55, b=30, l=90, r=10),
                        ))
                        st.plotly_chart(_opp_fig, use_container_width=True)

                    with _r5c_bc2:
                        # Home vs Away W/L grouped bar
                        _ha_grp = (_r5c_done.groupby(['home_away', 'won'])
                                   .size().reset_index(name='count'))
                        _ha_fig = go.Figure()
                        for _ha_loc, _ha_color, _ha_won in [
                            ('H', '#27ae60', True), ('H', '#a8e0b1', False),
                            ('A', '#3498db', True), ('A', '#f1a9a0', False),
                        ]:
                            _sub2 = _ha_grp[(_ha_grp['home_away'] == _ha_loc) &
                                            (_ha_grp['won'] == _ha_won)]
                            _cnt  = int(_sub2['count'].sum()) if not _sub2.empty else 0
                            _lbl  = ('Home' if _ha_loc == 'H' else 'Away') + (
                                ' WIN' if _ha_won else ' LOSS')
                            _ha_fig.add_trace(go.Bar(
                                x=[_lbl], y=[_cnt], name=_lbl,
                                marker=dict(color=_ha_color, line=dict(width=0)),
                                text=[_cnt], textposition='outside',
                                textfont=dict(size=12),
                                hovertemplate=(
                                    f'<b>{_lbl}</b><br>Games: {_cnt}<extra></extra>'
                                ),
                            ))
                        _ha_fig.update_layout(**_r5_base_layout(
                            title=dict(text='Home vs Away Performance',
                                       font=dict(size=13)),
                            barmode='group', height=360,
                            xaxis=dict(**_R5_AXIS),
                            yaxis=dict(title='Games', **_R5_AXIS),
                            legend=dict(orientation='h', y=-0.25,
                                        font=dict(size=10)),
                            margin=dict(t=55, b=80, l=40, r=10),
                            showlegend=True,
                        ))
                        st.plotly_chart(_ha_fig, use_container_width=True)

                    # ── Rolling 5-game scoring trend ──────────
                    _r5c_roll = _r5c_done.copy()
                    _r5c_roll['roll_pts'] = (
                        _r5c_roll['my_score'].rolling(5, min_periods=1).mean())
                    _r5c_roll['roll_opp'] = (
                        _r5c_roll['opp_score'].rolling(5, min_periods=1).mean())
                    _rl_fig = go.Figure()
                    _rl_fig.add_trace(go.Scatter(
                        x=_r5c_roll['game_num'], y=_r5c_roll['roll_pts'],
                        name=f'{_r5c_abbr} (rolling 5)',
                        mode='lines+markers',
                        line=dict(color=_r5c_color, width=2.5, shape='spline'),
                        marker=dict(size=6, color=_r5c_color,
                                    line=dict(width=1.5, color='white')),
                        hovertemplate=(
                            'Game %{x}<br>'
                            f'{_r5c_abbr} rolling PPG: <b>%{{y:.1f}}</b>'
                            '<extra></extra>'
                        ),
                    ))
                    _rl_fig.add_trace(go.Scatter(
                        x=_r5c_roll['game_num'], y=_r5c_roll['roll_opp'],
                        name='Opponent (rolling 5)',
                        mode='lines+markers',
                        line=dict(color='#e74c3c', width=2.5,
                                  shape='spline', dash='dot'),
                        marker=dict(size=6, color='#e74c3c',
                                    line=dict(width=1.5, color='white')),
                        hovertemplate=(
                            'Game %{x}<br>'
                            'Opp rolling PPG: <b>%{y:.1f}</b>'
                            '<extra></extra>'
                        ),
                    ))
                    _rl_fig.update_layout(**_r5_base_layout(
                        title=dict(
                            text=f'📈 {_r5c_name} — Rolling 5-Game Scoring Trend',
                            font=dict(size=13)),
                        height=340,
                        xaxis=dict(title='Game #', **_R5_AXIS),
                        yaxis=dict(title='Points (rolling avg)', **_R5_AXIS),
                        legend=dict(orientation='h', y=1.12, font=dict(size=11)),
                        margin=dict(t=65, b=40, l=55, r=10),
                    ))
                    st.plotly_chart(_rl_fig, use_container_width=True)

    # ── TAB 7: NETWORK / COORDINATOR ─────────────────────────
    with tab7:
        _render_how_it_works('network')
        if not _render_admin_gate('t6'):
            pass
        else:
            st.subheader("Distributed Fetch Network")
            st.caption(
                "This tab shows the state of the coordinator job queue and any connected fetch nodes. "
                "Start `coordinator.py` on this machine and run `fetch_node.py` on any PC to begin."
            )
            net_col1, net_col2 = st.columns([2, 1])
            with net_col1:
                coordinator_url = st.text_input(
                    "Coordinator URL",
                    value=db.get_config('coordinator_url', 'http://localhost:8765'),
                    placeholder='http://localhost:8765',
                    key='net_coord_url',
                )
            with net_col2:
                st.write("")
                if st.button("Check / Refresh", key='net_refresh'):
                    db.update_config('coordinator_url', coordinator_url)

            # Try to reach coordinator via requests
            import requests as _req
            health_data = None
            _coord_url_stripped = coordinator_url.strip()
            if not (_coord_url_stripped.startswith('http://') or _coord_url_stripped.startswith('https://')):
                st.error("⚠️ Coordinator URL must start with http:// or https://")
            else:
                try:
                    r = _req.get(f"{_coord_url_stripped.rstrip('/')}/health", timeout=3)
                    r.raise_for_status()
                    health_data = r.json()
                except Exception as e_net:
                    health_data = None

            if health_data:
                q = health_data.get('queue', {})
                nc1, nc2, nc3, nc4 = st.columns(4)
                nc1.metric("Pending",   q.get('pending',   0))
                nc2.metric("Claimed",   q.get('claimed',   0))
                nc3.metric("Done",      q.get('done',      0))
                nc4.metric("Failed",    q.get('failed',    0))

                nodes = health_data.get('nodes', [])
                if nodes:
                    st.markdown("#### Connected Nodes")
                    node_rows = []
                    for n in nodes:
                        node_rows.append({
                            'Node': n['node_id'], 'IP': n.get('ip', ''),
                            'Last Seen': n.get('last_seen', '')[:16],
                            'Done': n.get('jobs_completed', 0),
                            'Failed': n.get('jobs_failed', 0),
                        })
                    st.dataframe(pd.DataFrame(node_rows), use_container_width=True, hide_index=True)
                else:
                    st.info("No nodes connected yet. Run `fetch_node.py` on any PC.")

                btn_col1, btn_col2, btn_col3 = st.columns(3)
                with btn_col1:
                    if st.button("⚡ Dispatch All Jobs", key='net_dispatch_all'):
                        try:
                            r2 = _req.post(f"{_coord_url_stripped.rstrip('/')}/jobs/dispatch_all",
                                           json={'endpoints': json.loads(db.get_config('active_endpoints', '[]'))},
                                           timeout=5)
                            info = r2.json()
                            st.success(f"Queued {info.get('jobs_queued', '?')} jobs")
                        except Exception as err:
                            st.error(str(err))
                with btn_col2:
                    if st.button("🧹 Clear Done Jobs", key='net_clear_done'):
                        try:
                            r3 = _req.post(f"{_coord_url_stripped.rstrip('/')}/jobs/clear",
                                           json={'status': 'done'}, timeout=5)
                            info = r3.json()
                            st.success(f"Cleared {info.get('deleted', '?')} finished jobs")
                        except Exception as err:
                            st.error(str(err))
                with btn_col3:
                    if st.button("🗑 Clear Failed Jobs", key='net_clear_failed'):
                        try:
                            r4 = _req.post(f"{_coord_url_stripped.rstrip('/')}/jobs/clear",
                                           json={'status': 'failed'}, timeout=5)
                            info = r4.json()
                            st.success(f"Cleared {info.get('deleted', '?')} failed jobs")
                        except Exception as err:
                            st.error(str(err))

                # Recent jobs table
                st.markdown("#### Recent Jobs (last 30)")
                try:
                    r5 = _req.get(f"{_coord_url_stripped.rstrip('/')}/jobs/list?limit=30", timeout=3)
                    jobs_data = r5.json().get('jobs', [])
                    if jobs_data:
                        jdf = pd.DataFrame(jobs_data)
                        display_cols = [c for c in ['id','endpoint_key','status','node_id','created_at','completed_at','error'] if c in jdf.columns]
                        st.dataframe(jdf[display_cols], use_container_width=True, hide_index=True)
                except Exception:
                    pass
            else:
                st.warning(
                    f"Cannot reach coordinator at **{_coord_url_stripped}**.  "
                    "Make sure it is running:  `python coordinator.py`"
                )
                st.markdown("##### Quick Start")
                st.code(
                    "python coordinator.py\n"
                    "python fetch_node.py",
                    language='bash'
                )
                # Fallback: show local DB job stats
                job_stats = db.get_job_stats()
                if job_stats['queue']:
                    st.markdown("**Local DB job queue state:**")
                    st.json(job_stats)

    # ── Custom-view helpers (shared by TAB 8 builder & TAB 10 runner) ─────────

    # All data sources the Custom View Builder can draw from.  Keyed by the
    # string the user selects; value is a human label + description shown in the UI.
    _CVB_SOURCES = {
        'game_history':      ('Games / Scoreboard',
                              'All synced game results — scores, dates, teams, status.'),
        'standings':         ('Standings',
                              'Division / conference standings scraped from ESPN.'),
        'rankings':          ('Rankings',
                              'AP, Coaches Poll, etc. rankings for college sports.'),
        'teams':             ('Teams',
                              'Full team registry — names, abbreviations, logos, colours.'),
        'roster':            ('Roster / Players',
                              'Player bio rows loaded via Load Roster on Player Trends.'),
        'player_stats':      ('Player Boxscore Stats',
                              'Per-game per-player stats from game summaries (all categories).'),
        'play_by_play':      ('Play-by-Play',
                              'Every stored play — text, type, down, clock, score.'),
        'news':              ('News',
                              'Headlines and articles fetched from ESPN news feed.'),
        'team_detail':       ('Team Detail',
                              'Extended team info (record, venue, coaching staff) from /teams/:id.'),
        'player_profiles':   ('Player Profiles',
                              'Cached player profile summaries built on Player Trends tab.'),
    }

    def _cvb_load_df(sport_key: str, data_src: str) -> pd.DataFrame:
        """Pull stored data from DB for any supported source — no live ESPN fetch needed."""
        try:
            _cat, _spt = sport_key.split('/', 1) if '/' in sport_key else ('', sport_key)
            if data_src == 'game_history' or data_src == 'scoreboard':
                return db.get_games_df(_cat, _spt)
            elif data_src == 'standings':
                return db.get_standings_df(_cat, _spt)
            elif data_src == 'rankings':
                return db.get_rankings_df(sport_key)
            elif data_src == 'teams':
                return db.get_teams_df(sport_key)
            elif data_src == 'roster':
                # Flatten all teams' rosters into one DataFrame
                conn = db.get_connection()
                df = pd.read_sql_query(
                    """SELECT player_id, display_name, jersey, position,
                              position_name, position_group, age, college,
                              display_height, display_weight, experience,
                              injury_status, status_name, team_id, team_abbr
                       FROM roster WHERE sport_key=?
                       ORDER BY team_abbr, position_group, jersey""",
                    conn, params=(sport_key,))
                conn.close()
                return df
            elif data_src == 'player_stats':
                # Flat table: one row per (event, player, category)
                conn = db.get_connection()
                df = pd.read_sql_query(
                    """SELECT p.player_name, p.team_abbr, p.category,
                              p.stat_labels, p.stat_values, p.game_date,
                              p.event_id, h.home_team, h.away_team,
                              h.home_score, h.away_score, h.status
                       FROM player_game_stats p
                       LEFT JOIN game_history h ON h.event_id = p.event_id
                       WHERE p.sport_key=?
                       ORDER BY p.game_date DESC, p.player_name""",
                    conn, params=(sport_key,))
                conn.close()
                return df
            elif data_src == 'play_by_play':
                conn = db.get_connection()
                df = pd.read_sql_query(
                    """SELECT p.period, p.clock, p.play_type, p.play_text,
                              p.team_abbr, p.away_score, p.home_score,
                              p.scoring_play, p.is_turnover, p.stat_yardage,
                              p.down, p.distance, p.down_dist_text,
                              p.event_id,
                              h.event_date, h.home_team, h.away_team
                       FROM play_by_play p
                       LEFT JOIN game_history h ON h.event_id = p.event_id
                       WHERE p.sport_key=?
                       ORDER BY h.event_date DESC, p.drive_num, p.sequence_num""",
                    conn, params=(sport_key,))
                conn.close()
                return df
            elif data_src == 'news':
                return db.get_news_df(sport_key, limit=500)
            elif data_src == 'team_detail':
                return db.get_team_detail_df(sport_key)
            elif data_src == 'player_profiles':
                conn = db.get_connection()
                df = pd.read_sql_query(
                    """SELECT player_name, player_id, team_abbr,
                              season_year, sources, built_at
                       FROM player_profiles WHERE sport_key=?
                       ORDER BY built_at DESC""",
                    conn, params=(sport_key,))
                conn.close()
                return df
        except Exception:
            pass
        return pd.DataFrame()

    def _cvb_row_count(sport_key: str, data_src: str) -> int:
        """Quick row-count so the UI can show which sources have data."""
        try:
            df = _cvb_load_df(sport_key, data_src)
            return len(df)
        except Exception:
            return 0

    def _cv_run_view(cfg, parent=None):
        """Render a single custom view config. Pass parent=st for root, or a column."""
        _out = parent if parent is not None else st
        _sport = cfg.get('sport_key', '')
        _src   = cfg.get('data_source', '')
        _chart = cfg.get('chart_type', 'table')
        _fx    = cfg.get('filter_col', '')
        _fv    = cfg.get('filter_val', '')
        _cx    = cfg.get('chart_x', '')
        _cy    = cfg.get('chart_y', '')

        # ── schema_live / espn_live: re-fetch the ESPN endpoint ──────
        if _src in ('schema_live', 'espn_live'):
            _sl_url    = cfg.get('schema_url', '')
            _sl_params = cfg.get('schema_params', {})
            _sl_fields = cfg.get('schema_fields', [])
            _sl_keep   = cfg.get('keep_cols', [])
            if not (_sl_url and _sl_fields):
                _out.warning("This view has no stored ESPN URL or field list — cannot re-fetch.")
                return
            _df, _err = _schema_extract_to_df(_sl_url, _sl_params, _sl_fields)
            if _err:
                _out.error(f"Live fetch failed: {_err}")
                return
            if _sl_keep:
                _df = _df[[c for c in _sl_keep if c in _df.columns]]
        else:
            _df = _cvb_load_df(_sport, _src)

        if _df.empty:
            _out.info("No data available. Ensure this league has been synced first.")
            return

        if _fx and _fv and _fx in _df.columns:
            _df = _df[_df[_fx].astype(str).str.contains(_fv, case=False, na=False)]

        if _df.empty:
            _out.info(f"No rows matched filter `{_fx}` = `{_fv}`.")
            return

        if _chart == 'table':
            _out.dataframe(_df, use_container_width=True, hide_index=True)
        elif _chart in ('bar_chart', 'line_chart', 'scatter'):
            if not _cx or _cx not in _df.columns:
                _out.warning(f"X column `{_cx}` not found.  Available: {', '.join(_df.columns[:8])}")
                _out.dataframe(_df.head(10), use_container_width=True, hide_index=True)
                return
            if not _cy or _cy not in _df.columns:
                _out.warning(f"Y column `{_cy}` not found.  Available: {', '.join(_df.columns[:8])}")
                _out.dataframe(_df.head(10), use_container_width=True, hide_index=True)
                return
            _vfig = go.Figure()
            if _chart == 'bar_chart':
                _vfig.add_trace(go.Bar(
                    x=_df[_cx].tolist(), y=_df[_cy].tolist(),
                    marker=dict(line=dict(width=0), opacity=0.85),
                    hovertemplate=f'<b>%{{x}}</b><br>{_cy}: %{{y}}<extra></extra>',
                ))
            elif _chart == 'line_chart':
                _vfig.add_trace(go.Scatter(
                    x=_df[_cx].tolist(), y=_df[_cy].tolist(),
                    mode='lines+markers',
                    line=dict(width=2.5, shape='spline'),
                    hovertemplate=f'<b>%{{x}}</b><br>{_cy}: %{{y}}<extra></extra>',
                ))
            elif _chart == 'scatter':
                _vfig.add_trace(go.Scatter(
                    x=_df[_cx].tolist(), y=_df[_cy].tolist(),
                    mode='markers',
                    marker=dict(size=9, opacity=0.8),
                    hovertemplate=f'<b>%{{x}}</b><br>{_cy}: %{{y}}<extra></extra>',
                ))
            _vfig.update_layout(
                paper_bgcolor='rgba(0,0,0,0)',
                plot_bgcolor='rgba(246,248,252,1)',
                height=420,
                xaxis_title=_cx, yaxis_title=_cy,
                margin=dict(t=40, b=60, l=60, r=20),
                font=dict(family="'Segoe UI',Arial,sans-serif", size=12),
            )
            _out.plotly_chart(_vfig, use_container_width=True)
        elif _chart == 'metric_cards':
            if not _cx or _cx not in _df.columns:
                _out.warning(f"Label column `{_cx}` not found.")
                return
            _mc_n = min(len(_df), 5)
            _mc_cs = _out.columns(_mc_n)
            for _mci, (_, _mr) in enumerate(_df.head(_mc_n).iterrows()):
                _mv = _mr[_cy] if _cy and _cy in _mr else '—'
                _label = str(_mr[_cx]) if _mr[_cx] is not None else '—'
                _mc_cs[_mci].metric(_label, _mv)

    # ── TAB 8: SCHEMA EXPLORER ────────────────────────────────
    with tab8:
        _render_tab_banner(
            "Schema Explorer & View Builder",
            "Discover every ESPN JSON field · Build custom data views from any stored table",
        )
        _render_how_it_works('schema')

        # ════════════════════════════════════════════════════════════
        # SECTION 1 — Field Schema Crawler
        # ════════════════════════════════════════════════════════════
        st.markdown("### 🕷 Field Schema Crawler")
        st.caption(
            "Fetches every ESPN API endpoint and walks the full JSON response "
            "recursively — recording every field path, data type, and an example value. "
            "Crawl once; re-crawl only when ESPN updates their API."
        )

        crawler = SchemaCrawler(db)
        all_crawl_eps = crawler.build_endpoints()

        _sc_c1, _sc_c2, _sc_c3 = st.columns([3, 1, 1])
        with _sc_c1:
            _crawl_sport_filter = st.multiselect(
                "Limit crawl to sport(s) — leave blank for all",
                EndpointRegistry.get_all_keys(),
                default=[],
                placeholder="All endpoints",
                key='schema_sport_filter',
            )
        with _sc_c2:
            st.write("")
            _do_crawl = st.button("🕷 Crawl Endpoints", key='schema_crawl_btn',
                                  help="Fetch all ESPN endpoints and store field catalog")
        with _sc_c3:
            st.write("")
            if st.button("🗑 Clear Schema DB", key='schema_clear_btn'):
                db.clear_schema()
                st.success("Schema cleared.")
                st.rerun()

        if _do_crawl:
            _eps_to_crawl = [
                e for e in all_crawl_eps
                if not _crawl_sport_filter or e['sport_key'] in _crawl_sport_filter
            ]
            _sc_prog = st.progress(0.0, text="Initialising…")
            _sc_ph   = st.empty()
            _crawl_ok, _crawl_fail, _total_fields = 0, 0, 0
            for _sci, _ep in enumerate(_eps_to_crawl):
                _sc_prog.progress(
                    (_sci + 1) / len(_eps_to_crawl),
                    text=f"[{_sci+1}/{len(_eps_to_crawl)}] {_ep['key']}"
                )
                _sc_ph.caption(f"🌐 {_ep['url'][:90]}")
                try:
                    _scr = crawler.session.get(
                        _ep['url'], params=_ep['params'], timeout=20)
                    _scr.raise_for_status()
                    _scdata = _scr.json()
                    _scfields = _flatten_json(_scdata)
                    db.save_schema_fields(
                        _ep['sport_key'], _ep['endpoint_type'],
                        _ep['url'], _scfields)
                    _total_fields += len(_scfields)
                    _crawl_ok += 1
                except Exception:
                    _crawl_fail += 1
                time.sleep(0.35)
            _sc_prog.empty()
            _sc_ph.empty()
            st.success(
                f"✅ {_crawl_ok} endpoints crawled · "
                f"{_crawl_fail} errors · "
                f"{_total_fields:,} fields discovered"
            )

        # ── Coverage dashboard ─────────────────────────────────────
        _df_summary = db.get_schema_summary()
        if not _df_summary.empty:
            st.markdown("#### Coverage Dashboard")
            _ds_display = _df_summary.copy()
            _ds_display['last_crawled'] = _ds_display['last_crawled'].str[:16]
            st.dataframe(
                _ds_display.rename(columns={
                    'sport_key': 'Sport', 'endpoint_type': 'Endpoint',
                    'total_fields': 'Fields Discovered', 'last_crawled': 'Last Crawled',
                }),
                use_container_width=True, hide_index=True,
            )

            # ── Field Explorer ─────────────────────────────────────
            st.markdown("#### 🔎 Field Explorer")
            st.caption(
                "Browse every discovered JSON field. "
                "Filter by sport, endpoint type, or keyword, then use the "
                "**📡 Live Query Builder** below to pick any combination of fields "
                "and fetch real multi-row data straight from ESPN."
            )
            _fe1, _fe2, _fe3, _fe4 = st.columns([2, 2, 2, 1])
            with _fe1:
                _fe_sport_opts = ['(all)'] + sorted(
                    _df_summary['sport_key'].unique().tolist())
                _fe_sel_sk = st.selectbox("Sport", _fe_sport_opts, key='fe_sport')
            with _fe2:
                _fe_ep_opts = ['(all)'] + sorted(
                    _df_summary['endpoint_type'].unique().tolist())
                _fe_sel_et = st.selectbox("Endpoint", _fe_ep_opts, key='fe_ep')
            with _fe3:
                _fe_search = st.text_input(
                    "Search JSON path",
                    placeholder="e.g. odds, weather, venue, spread…",
                    key='fe_search',
                )
            with _fe4:
                st.write("")
                _fe_hv_only = st.checkbox(
                    "⭐ High-value only", key='fe_hv_only',
                    help="Only show fields likely to contain actionable data",
                )

            _df_fields = db.get_schema_df(
                sport_key=None if _fe_sel_sk == '(all)' else _fe_sel_sk,
                endpoint_type=None if _fe_sel_et == '(all)' else _fe_sel_et,
            )
            if _fe_search:
                _df_fields = _df_fields[
                    _df_fields['field_path'].str.contains(
                        _fe_search, case=False, na=False)
                ]

            _HIGH_VALUE_KW = [
                'odds', 'weather', 'neutral', 'conference', 'ticket', 'capacity',
                'playoff', 'seed', 'premium', 'story', 'keyword', 'franchise',
                'injury', 'returnDate', 'lastFiveGames', 'geoBroadcast',
                'pickcenter', 'standingSummary', 'nextEvent',
            ]
            if _fe_hv_only:
                _hv_mask_pre = _df_fields['field_path'].str.lower().str.contains(
                    '|'.join(_HIGH_VALUE_KW), na=False)
                _df_fields = _df_fields[_hv_mask_pre]

            _fe_show_cols = [
                'sport_key', 'endpoint_type', 'field_path',
                'value_type', 'example_value',
            ]
            _fe_col_rename = {
                'sport_key': 'Sport', 'endpoint_type': 'Endpoint',
                'field_path': 'JSON Path', 'value_type': 'Type',
                'example_value': 'Example Value',
            }

            if not _df_fields.empty:
                _fe_n = len(_df_fields)
                st.caption(
                    f"**{_fe_n:,} fields** visible — "
                    "click any column header to sort. "
                    "Scroll down to **📡 Live Query Builder** to select fields for fetching."
                )
                st.dataframe(
                    _df_fields[_fe_show_cols].rename(columns=_fe_col_rename),
                    use_container_width=True,
                    hide_index=True,
                    height=min(460, max(180, min(_fe_n, 14) * 35 + 38)),
                )

                # ── High-value expander ────────────────────────┐
                _mask_hv = _df_fields['field_path'].str.lower().str.contains(
                    '|'.join(_HIGH_VALUE_KW), na=False)
                if _mask_hv.any() and not _fe_hv_only:
                    with st.expander(
                        f"⭐ High-value / parser-worthy fields "
                        f"({_mask_hv.sum()} found)"
                    ):
                        st.caption(
                            "Fields matching: " +
                            ', '.join(f'`{k}`' for k in _HIGH_VALUE_KW)
                        )
                        st.dataframe(
                            _df_fields[_mask_hv][_fe_show_cols].rename(
                                columns=_fe_col_rename),
                            use_container_width=True, hide_index=True,
                        )

                # ── 📡 Live Query Builder ───────────────────────
                _lqb_key_sfx = f"{_fe_sel_sk}__{_fe_sel_et}".replace('/', '_')

                with st.expander(
                    "📡 **Live Query Builder** — pick fields → fetch real rows from ESPN",
                    expanded=bool(st.session_state.get('schema_live_result')),
                ):
                    st.caption(
                        "Select any fields from the catalog above "
                        "(all **{:,}** are available — type to search inside the picker). "
                        "The app hits the ESPN endpoint live and returns a proper "
                        "multi-row table — one row per game, team, or standing entry.".format(_fe_n)
                    )

                    # ── Quick-select by prefix group (tick a group → all its fields land in multiselect)
                    _all_paths = _df_fields['field_path'].tolist()
                    _prefix_map: Dict[str, List[str]] = {}
                    for _fp in _all_paths:
                        _segs = [s.rstrip(']') for s in re.split(r'[.\[]', _fp) if s]
                        _grp_parts = [s for s in _segs[:6] if not s.isdigit()][:3]
                        _grp = '.'.join(_grp_parts) or '(root)'
                        _prefix_map.setdefault(_grp, []).append(_fp)

                    _sorted_groups = sorted(
                        _prefix_map.items(),
                        key=lambda x: (-len(x[1]), x[0]),
                    )[:20]

                    if _sorted_groups:
                        st.markdown("**Quick-select entire field groups** (check → appends to picker below):")
                        _n_grp_cols = min(4, len(_sorted_groups))
                        _grp_col_widgets = st.columns(_n_grp_cols)
                        _preselected_from_groups: List[str] = []
                        for _gi, (_grp, _grp_paths) in enumerate(_sorted_groups):
                            with _grp_col_widgets[_gi % _n_grp_cols]:
                                if st.checkbox(
                                    f"{_grp} ({len(_grp_paths)})",
                                    key=f'lqb_grp_{_gi}_{_lqb_key_sfx}',
                                    help=f"Adds all {len(_grp_paths)} fields under `{_grp}` to the selection.",
                                ):
                                    _preselected_from_groups.extend(_grp_paths)

                        _preselected_from_groups = list(dict.fromkeys(_preselected_from_groups))
                    else:
                        _preselected_from_groups = []

                    st.markdown("**Select individual fields** (search inside the picker):")
                    _lqb_sel = st.multiselect(
                        f"Fields to extract ({_fe_n:,} available — start typing or tick groups above)",
                        options=_all_paths,
                        default=[p for p in _preselected_from_groups if p in _all_paths][:80],
                        key=f'lqb_fields_{_lqb_key_sfx}',
                        help=(
                            "Every selected path becomes one column in the output table. "
                            "Column names are shortened to the last 3 path segments automatically."
                        ),
                        placeholder="Type any part of a field name to search…",
                    )

                    # ── Resolve URL + params ──────────────────────
                    _lqb_url: Optional[str] = None
                    _lqb_params: Dict = {}
                    if 'url' in _df_fields.columns:
                        _lqb_url_series = _df_fields['url'].dropna()
                        if not _lqb_url_series.empty:
                            _lqb_url = _lqb_url_series.iloc[0]
                    if _lqb_url:
                        for _lqb_ep in crawler.build_endpoints():
                            if (
                                _lqb_ep['url'] == _lqb_url
                                and _lqb_ep['sport_key'] == _fe_sel_sk
                            ):
                                _lqb_params = _lqb_ep.get('params', {})
                                break
                        st.caption(
                            f"🌐 Source: `{_lqb_url}`"
                            + (f"  params: `{_lqb_params}`" if _lqb_params else "")
                        )
                    else:
                        st.warning(
                            "Select a specific **Sport** and **Endpoint** (not '(all)') "
                            "so the Live Query Builder knows which URL to hit.",
                            icon="⚠️",
                        )

                    _lqb_n_sel = len(_lqb_sel)
                    _lqb_btnc, _lqb_infoc = st.columns([2, 4])
                    with _lqb_btnc:
                        _do_lqb = st.button(
                            f"📡 Fetch Live Data ({_lqb_n_sel} fields)",
                            key=f'lqb_fetch_{_lqb_key_sfx}',
                            disabled=not (_lqb_sel and _lqb_url),
                            type='primary',
                            help="Fetches the ESPN endpoint now and extracts selected paths as rows.",
                        )
                    with _lqb_infoc:
                        if not _lqb_sel:
                            st.caption("Pick at least one field to enable fetch.")
                        elif not _lqb_url:
                            st.caption("Set Sport + Endpoint above to enable fetch.")
                        else:
                            st.caption(
                                f"Ready — will fetch `{_fe_sel_et}` for `{_fe_sel_sk}` "
                                f"and extract **{_lqb_n_sel}** columns."
                            )

                    if _do_lqb:
                        with st.spinner(f"Fetching {_lqb_url}…"):
                            _lqb_df, _lqb_err = _schema_extract_to_df(
                                _lqb_url, _lqb_params, _lqb_sel,
                            )
                        if _lqb_err:
                            st.error(f"Fetch failed: {_lqb_err}")
                        elif _lqb_df.empty:
                            st.warning(
                                "Fetch succeeded but produced 0 rows. "
                                "Check that the selected field paths share a common root array "
                                "(e.g. all under `events[0].*`)."
                            )
                        else:
                            st.session_state['schema_live_result'] = {
                                'df':          _lqb_df,
                                'fields':      _lqb_sel,
                                'source_info': f"{_fe_sel_sk} / {_fe_sel_et}",
                                'url':         _lqb_url,
                                'params':      _lqb_params,
                            }
                            st.success(
                                f"✅ {len(_lqb_df):,} rows × {len(_lqb_df.columns)} columns fetched. "
                                "Scroll down to the **📡 Use Schema Live Data** panel "
                                "in the Custom View Builder to chart and save it."
                            )
                            st.rerun()

                    # Preview any cached result inside the expander
                    _lqb_cached = st.session_state.get('schema_live_result')
                    if _lqb_cached:
                        st.markdown("---")
                        st.markdown(
                            f"**Cached result:** {_lqb_cached['source_info']} — "
                            f"{len(_lqb_cached['df']):,} rows × "
                            f"{len(_lqb_cached['df'].columns)} cols"
                        )
                        st.dataframe(
                            _lqb_cached['df'],
                            use_container_width=True,
                            hide_index=True,
                            height=260,
                        )
                        if st.button("🗑 Clear result", key=f'lqb_clear_{_lqb_key_sfx}'):
                            if 'schema_live_result' in st.session_state:
                                del st.session_state['schema_live_result']
                            st.rerun()
            else:
                st.info("No fields match your filter — try a shorter search term or a different endpoint.")
        else:
            st.info(
                "No schema data yet. Click **🕷 Crawl Endpoints** above "
                "to start field discovery."
            )

        # ════════════════════════════════════════════════════════════
        # SECTION 2 — Custom View Builder
        # ════════════════════════════════════════════════════════════
        st.divider()
        st.markdown("### 📋 Custom View Builder")
        st.caption(
            "Build charts and tables from **stored DB data** or from "
            "**live ESPN JSON** (fetched by the Live Query Builder above). "
            "Column pickers always show real fields — never placeholders."
        )

        _cv_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'custom_views')
        os.makedirs(_cv_dir, exist_ok=True)

        if 'cv_session_views' not in st.session_state:
            st.session_state['cv_session_views'] = []

        # ── Schema Live Data panel ─────────────────────────────────
        _slr = st.session_state.get('schema_live_result')
        if _slr:
            _slr_df   = _slr['df']
            _slr_cols = list(_slr_df.columns)
            _slr_ncols = [c for c in _slr_cols
                          if pd.api.types.is_numeric_dtype(_slr_df[c])]
            with st.expander(
                f"📡 Use Schema Live Data — {_slr['source_info']} "
                f"({len(_slr_df):,} rows × {len(_slr_cols)} cols)",
                expanded=True,
            ):
                st.caption(
                    "This data was fetched live from ESPN in the Field Explorer above. "
                    "Configure it as a view, download it as CSV, or save it to disk."
                )
                _sla1, _sla2, _sla3 = st.columns([3, 3, 2])
                with _sla1:
                    _sl_name = st.text_input(
                        "View Name *",
                        placeholder="e.g. EPL Match Odds",
                        key='sl_name',
                    )
                    _sl_desc = st.text_input(
                        "Description (optional)",
                        key='sl_desc',
                    )
                with _sla2:
                    _sl_chart = st.selectbox(
                        "Display As",
                        ['table', 'bar_chart', 'line_chart', 'scatter', 'metric_cards'],
                        key='sl_chart',
                    )
                    _sl_need_axes = _sl_chart in (
                        'bar_chart', 'line_chart', 'scatter', 'metric_cards')
                with _sla3:
                    _sl_fcol_raw = st.selectbox(
                        "Filter column (optional)",
                        ['(none)'] + _slr_cols,
                        key='sl_fcol',
                    )
                    _sl_filter_col = '' if _sl_fcol_raw == '(none)' else _sl_fcol_raw

                _slb1, _slb2 = st.columns(2)
                with _slb1:
                    if _sl_need_axes:
                        _sl_cx = st.selectbox("X axis / Label column", _slr_cols, key='sl_cx')
                    else:
                        _sl_cx = ''
                        st.caption("*X/Y not needed for table view*")
                with _slb2:
                    if _sl_need_axes:
                        _sl_cy = st.selectbox(
                            "Y axis / Value column",
                            _slr_ncols if _slr_ncols else _slr_cols,
                            key='sl_cy',
                        )
                    else:
                        _sl_cy = ''

                _sl_filter_val = ''
                if _sl_filter_col and _sl_filter_col in _slr_df.columns:
                    _sl_fv_opts = sorted(
                        _slr_df[_sl_filter_col].dropna().astype(str)
                        .unique().tolist()[:80]
                    )
                    if _sl_fv_opts:
                        _sl_fv_sel = st.selectbox(
                            f"Filter value for `{_sl_filter_col}`",
                            ['(all)'] + _sl_fv_opts,
                            key='sl_fval',
                        )
                        _sl_filter_val = '' if _sl_fv_sel == '(all)' else _sl_fv_sel

                # Column visibility picker
                _sl_keep = st.multiselect(
                    "Columns to keep in saved view (deselect to hide)",
                    options=_slr_cols,
                    default=_slr_cols,
                    key='sl_keep_cols',
                )

                # Preview
                st.markdown("##### 🔍 Preview")
                _sl_pv_df = _slr_df.copy()
                if _sl_filter_col and _sl_filter_val and _sl_filter_col in _sl_pv_df.columns:
                    _sl_pv_df = _sl_pv_df[
                        _sl_pv_df[_sl_filter_col].astype(str).str.contains(
                            _sl_filter_val, case=False, na=False)
                    ]
                if _sl_keep:
                    _sl_pv_df = _sl_pv_df[[c for c in _sl_keep if c in _sl_pv_df.columns]]

                if _sl_chart == 'table' or not _sl_need_axes:
                    st.dataframe(
                        _sl_pv_df,
                        use_container_width=True, hide_index=True, height=300,
                    )
                elif _sl_chart in ('bar_chart', 'line_chart', 'scatter'):
                    if _sl_cx in _sl_pv_df.columns and _sl_cy in _sl_pv_df.columns:
                        _sl_fig = go.Figure()
                        _sl_x = _sl_pv_df[_sl_cx].tolist()
                        _sl_y = _sl_pv_df[_sl_cy].tolist()
                        if _sl_chart == 'bar_chart':
                            _sl_fig.add_trace(go.Bar(x=_sl_x, y=_sl_y))
                        elif _sl_chart == 'line_chart':
                            _sl_fig.add_trace(go.Scatter(
                                x=_sl_x, y=_sl_y, mode='lines+markers'))
                        else:
                            _sl_fig.add_trace(go.Scatter(
                                x=_sl_x, y=_sl_y, mode='markers'))
                        _sl_fig.update_layout(
                            xaxis_title=_sl_cx, yaxis_title=_sl_cy,
                            height=400, margin=dict(l=40, r=20, t=30, b=60),
                        )
                        st.plotly_chart(_sl_fig, use_container_width=True)
                    else:
                        st.info("Select valid X and Y columns above.")
                elif _sl_chart == 'metric_cards':
                    if _sl_cx and _sl_cy:
                        _sl_mc = st.columns(min(5, max(1, len(_sl_pv_df))))
                        for _sl_i, (_, _sl_r) in enumerate(_sl_pv_df.head(5).iterrows()):
                            with _sl_mc[_sl_i]:
                                st.metric(
                                    str(_sl_r.get(_sl_cx, '—')),
                                    str(_sl_r.get(_sl_cy, '—')),
                                )

                st.markdown("---")
                _sl_c1, _sl_c2, _sl_c3 = st.columns(3)

                def _sl_build_cfg():
                    return dict(
                        name=(_sl_name or '').strip(),
                        description=(_sl_desc or '').strip(),
                        sport_key=_slr['source_info'],
                        data_source='schema_live',
                        chart_type=_sl_chart,
                        chart_x=_sl_cx if isinstance(_sl_cx, str) else '',
                        chart_y=_sl_cy if isinstance(_sl_cy, str) else '',
                        filter_col=_sl_filter_col,
                        filter_val=_sl_filter_val if isinstance(_sl_filter_val, str) else '',
                        schema_fields=_slr['fields'],
                        schema_url=_slr['url'],
                        schema_params=_slr.get('params', {}),
                        keep_cols=st.session_state.get('sl_keep_cols', _slr_cols),
                    )

                with _sl_c1:
                    if st.button("💾 Add to Session", key='sl_ses'):
                        if not (_sl_name or '').strip():
                            st.error("View Name is required.")
                        else:
                            st.session_state['cv_session_views'].append(_sl_build_cfg())
                            st.success(f"✅ \"{_sl_name}\" added to session.")
                            st.rerun()
                with _sl_c2:
                    if st.button("📁 Save to Disk", key='sl_disk'):
                        if not (_sl_name or '').strip():
                            st.error("View Name is required.")
                        else:
                            _sl_cfg = _sl_build_cfg()
                            _sl_safe = "".join(
                                c if c.isalnum() or c in '._- ' else '_'
                                for c in _sl_cfg['name']
                            ).replace(' ', '_')[:60]
                            _sl_path = os.path.join(_cv_dir, f"{_sl_safe}.json")
                            with open(_sl_path, 'w', encoding='utf-8') as _slf:
                                json.dump(_sl_cfg, _slf, indent=2)
                            st.session_state['cv_session_views'].append(_sl_cfg)
                            st.success(
                                f"✅ Saved to `{_sl_path}`. "
                                "Appears on the **📋 Custom Views** tab."
                            )
                            st.rerun()
                with _sl_c3:
                    _dl_df = _sl_pv_df
                    st.download_button(
                        "📥 Download CSV",
                        data=_dl_df.to_csv(index=False).encode('utf-8'),
                        file_name=f"{(_sl_name or 'schema_view').replace(' ', '_')}.csv",
                        mime='text/csv',
                        key='sl_csv',
                    )

        # ── Sub-section: DB snapshot — what data do we actually have? ──
        with st.expander("📦 What's in your local database?", expanded=False):
            st.caption(
                "Row counts per table per league. "
                "Sources with 0 rows need their respective tabs to be populated first."
            )
            _snap_sport = st.selectbox(
                "League to inspect",
                EndpointRegistry.get_all_keys(),
                key='cvb_snap_sport',
            )
            _snap_rows = []
            for _src_key, (_src_label, _src_desc) in _CVB_SOURCES.items():
                _cnt = _cvb_row_count(_snap_sport, _src_key)
                _status = "✅" if _cnt > 0 else "⬜"
                _snap_rows.append({
                    'Status':      _status,
                    'Data Source': _src_label,
                    'Rows':        _cnt,
                    'Description': _src_desc,
                    'How to populate': (
                        'Sync Scoreboard tab' if _src_key in ('game_history', 'scoreboard')
                        else 'Sync Scoreboard' if _src_key in ('standings', 'rankings', 'news')
                        else 'Teams tab → Load Teams' if _src_key == 'teams'
                        else 'Teams tab → Load Teams → Load Detail' if _src_key == 'team_detail'
                        else 'Player Trends → Load Roster' if _src_key == 'roster'
                        else 'Scoreboard → Fetch Summary → Sync Player Stats' if _src_key == 'player_stats'
                        else 'Scoreboard → Fetch Summary (PBP is saved automatically)' if _src_key == 'play_by_play'
                        else 'Player Trends → Build Profile' if _src_key == 'player_profiles'
                        else '—'
                    ),
                })
            st.dataframe(
                pd.DataFrame(_snap_rows),
                use_container_width=True, hide_index=True,
            )

        # ── Main builder expander ──────────────────────────────────
        with st.expander("➕ Create a New Custom View", expanded=False):

            # ── Name / sport row ──────────────────────────────────
            _cvb_r1, _cvb_r2 = st.columns([4, 3])
            with _cvb_r1:
                _cv_name = st.text_input(
                    "View Name *",
                    placeholder="e.g. EPL Match Odds",
                    key='cvb_name',
                )
                _cv_desc = st.text_input(
                    "Description (optional)",
                    placeholder="Short summary shown in the Custom Views tab",
                    key='cvb_desc',
                )
            with _cvb_r2:
                _cv_sport = st.selectbox(
                    "Sport / League",
                    EndpointRegistry.get_all_keys(),
                    key='cvb_sport',
                )
                _cv_src_type = st.radio(
                    "Data source type",
                    ["📦 Stored DB table", "📡 ESPN live (crawler)"],
                    horizontal=True,
                    key='cvb_src_type',
                    help=(
                        "**Stored DB** — uses rows already saved in your local database. "
                        "**ESPN live** — fetches the ESPN API now and uses every field the "
                        "crawler discovered, including ones our parsers don't yet store."
                    ),
                )

            # ════════════════════════════════════════════════════════
            # PATH A — Stored DB table
            # ════════════════════════════════════════════════════════
            if _cv_src_type == "📦 Stored DB table":
                _available_src_labels = {}
                for _sk, (_sl, _sd) in _CVB_SOURCES.items():
                    _rc = _cvb_row_count(_cv_sport, _sk)
                    _available_src_labels[_sk] = (
                        f"{_sl}  ({_rc:,} rows)"
                        if _rc > 0
                        else f"{_sl}  (0 rows — needs data)"
                    )
                _cv_data_src = st.selectbox(
                    "Table",
                    list(_CVB_SOURCES.keys()),
                    format_func=lambda k: _available_src_labels.get(k, k),
                    key='cvb_src_db',
                    help=(
                        "Each entry shows how many rows are stored for this league. "
                        "Sources showing '0 rows' need their corresponding tab populated first."
                    ),
                )

                _cvb_df      = _cvb_load_df(_cv_sport, _cv_data_src)
                _cvb_cols    = list(_cvb_df.columns) if not _cvb_df.empty else []
                _cvb_numcols = [c for c in _cvb_cols if pd.api.types.is_numeric_dtype(_cvb_df[c])]
                _cvb_ok      = bool(_cvb_cols)
                _cvb_is_live = False
                _cvb_live_url    = ''
                _cvb_live_params = {}
                _cvb_live_fields: List[str] = []

                if not _cvb_ok:
                    _src_how = (
                        'Sync Scoreboard tab' if _cv_data_src in ('game_history',)
                        else 'sync the Scoreboard tab' if _cv_data_src in ('standings', 'rankings', 'news')
                        else 'Teams tab → Load Teams' if _cv_data_src == 'teams'
                        else 'Teams tab → Load Teams → Load Detail' if _cv_data_src == 'team_detail'
                        else 'Player Trends → Load Roster' if _cv_data_src == 'roster'
                        else 'Scoreboard → Fetch Summary → Sync Player Stats' if _cv_data_src == 'player_stats'
                        else 'Scoreboard → Fetch Summary' if _cv_data_src == 'play_by_play'
                        else 'Player Trends → Build Profile' if _cv_data_src == 'player_profiles'
                        else 'populate the relevant tab first'
                    )
                    st.warning(
                        f"⚠️ **{_CVB_SOURCES[_cv_data_src][0]}** has no data for "
                        f"**{_cv_sport}** yet.  To populate: *{_src_how}*."
                    )

            # ════════════════════════════════════════════════════════
            # PATH B — ESPN live via crawler
            # ════════════════════════════════════════════════════════
            else:
                # Build endpoint map for this sport
                _cvb_ep_list = [
                    ep for ep in crawler.build_endpoints()
                    if ep['sport_key'] == _cv_sport
                ]
                _cvb_ep_labels = {
                    ep['endpoint_type']: ep
                    for ep in _cvb_ep_list
                }

                if not _cvb_ep_list:
                    st.warning(
                        f"No endpoints registered for **{_cv_sport}**. "
                        "Check EndpointRegistry or crawl this league first."
                    )
                else:

                    # How many fields have been discovered per endpoint?
                    _cvb_ep_field_counts: Dict[str, int] = {}
                    for _et, _ep_obj in _cvb_ep_labels.items():
                        _ep_df = db.get_schema_df(sport_key=_cv_sport, endpoint_type=_et)
                        _cvb_ep_field_counts[_et] = len(_ep_df)

                    _cv_data_src = 'espn_live'
                    _cv_ep_type = st.selectbox(
                        "ESPN Endpoint",
                        list(_cvb_ep_labels.keys()),
                        format_func=lambda et: (
                            f"{et}  ({_cvb_ep_field_counts.get(et, 0):,} fields discovered)"
                            if _cvb_ep_field_counts.get(et, 0) > 0
                            else f"{et}  (not yet crawled — crawl first for field hints)"
                        ),
                        key='cvb_src_ep',
                        help=(
                            "Select which ESPN endpoint to hit live. "
                            "Endpoints showing field counts have been crawled — "
                            "their fields load in the picker below. "
                            "Un-crawled endpoints still work; you'll need to type paths manually."
                        ),
                    )
                    _cvb_sel_ep   = _cvb_ep_labels[_cv_ep_type]
                    _cvb_live_url    = _cvb_sel_ep['url']
                    _cvb_live_params = _cvb_sel_ep.get('params', {})

                    st.caption(f"🌐 `{_cvb_live_url}`" + (f"  `{_cvb_live_params}`" if _cvb_live_params else ""))

                    # Field picker — populated from crawled schema if available
                    _cvb_ep_schema_df = db.get_schema_df(sport_key=_cv_sport, endpoint_type=_cv_ep_type)
                    _cvb_all_paths    = _cvb_ep_schema_df['field_path'].tolist() if not _cvb_ep_schema_df.empty else []
                    _cvb_n_paths      = len(_cvb_all_paths)

                    if _cvb_n_paths == 0:
                        st.info(
                            f"No fields discovered yet for `{_cv_ep_type}`. "
                            "Click **🕷 Crawl Endpoints** at the top of this tab (set Sport filter to this league), "
                            "then return here — the field picker will populate automatically."
                        )
                    else:
                        st.caption(
                            f"**{_cvb_n_paths:,} fields available** from crawl of `{_cv_ep_type}`. "
                            "Search inside the picker or use quick groups below."
                        )

                    # Quick-group checkboxes
                    _cvb_grp_map: Dict[str, List[str]] = {}
                    for _fp in _cvb_all_paths:
                        _segs = [s.rstrip(']') for s in re.split(r'[.\[]', _fp) if s and not s.rstrip(']').isdigit()]
                        _grp  = '.'.join(_segs[:3]) or '(root)'
                        _cvb_grp_map.setdefault(_grp, []).append(_fp)

                    _cvb_top_groups = sorted(_cvb_grp_map.items(), key=lambda x: (-len(x[1]), x[0]))[:16]
                    _cvb_grp_adds: List[str] = []
                    if _cvb_top_groups:
                        st.markdown("**Quick-select field groups:**")
                        _gc_cols = st.columns(min(4, len(_cvb_top_groups)))
                        for _gi, (_grp, _gpaths) in enumerate(_cvb_top_groups):
                            with _gc_cols[_gi % 4]:
                                if st.checkbox(
                                    f"{_grp} ({len(_gpaths)})",
                                    key=f'cvb_grp_{_gi}',
                                    help=f"Add all {len(_gpaths)} fields under `{_grp}`",
                                ):
                                    _cvb_grp_adds.extend(_gpaths)
                        _cvb_grp_adds = list(dict.fromkeys(_cvb_grp_adds))

                    _cvb_live_fields = st.multiselect(
                        f"Fields to extract ({_cvb_n_paths:,} available — type to search)",
                        options=_cvb_all_paths,
                        default=[p for p in _cvb_grp_adds if p in _cvb_all_paths][:60],
                        key='cvb_live_fields',
                        placeholder="Type any part of a field name…",
                        help=(
                            "Each selected path becomes one column in the output. "
                            "Names are shortened to the last 3 path segments automatically."
                        ),
                    )

                    # Fetch button — loads data into session state for column pickers
                    _cvb_fetch_key = f"cvb_live_df_{_cv_sport}_{_cv_ep_type}"
                    _cvb_fetch_col1, _cvb_fetch_col2 = st.columns([2, 4])
                    with _cvb_fetch_col1:
                        _do_cvb_fetch = st.button(
                            f"📡 Fetch ({len(_cvb_live_fields)} fields)",
                            key='cvb_fetch_btn',
                            disabled=not bool(_cvb_live_fields),
                            type='primary',
                            help="Hits the ESPN endpoint now and populates column pickers below.",
                        )
                    with _cvb_fetch_col2:
                        if not _cvb_live_fields:
                            st.caption("Select at least one field to enable fetch.")
                        elif _cvb_all_paths:
                            st.caption(
                                f"Ready to fetch `{_cv_ep_type}` — "
                                f"{len(_cvb_live_fields)} columns selected."
                            )

                    if _do_cvb_fetch:
                        with st.spinner(f"Fetching {_cvb_live_url}…"):
                            _fetched_df, _fetch_err = _schema_extract_to_df(
                                _cvb_live_url, _cvb_live_params, _cvb_live_fields,
                            )
                        if _fetch_err:
                            st.error(f"Fetch error: {_fetch_err}")
                        elif _fetched_df.empty:
                            st.warning("Fetch returned 0 rows. Try selecting paths from a shared root array.")
                        else:
                            st.session_state[_cvb_fetch_key] = _fetched_df
                            st.success(
                                f"✅ {len(_fetched_df):,} rows × {len(_fetched_df.columns)} columns. "
                                "Column pickers updated below."
                            )

                    # Use cached fetch result for column pickers
                    _cvb_df = st.session_state.get(_cvb_fetch_key, pd.DataFrame())
                    _cvb_cols    = list(_cvb_df.columns) if not _cvb_df.empty else []
                    _cvb_numcols = [c for c in _cvb_cols if pd.api.types.is_numeric_dtype(_cvb_df[c])]
                    _cvb_ok      = bool(_cvb_cols)
                    _cvb_is_live = True

                    if not _cvb_ok and _cvb_live_fields:
                        st.info("Click **📡 Fetch** above to load data and populate column pickers.")

            # ════════════════════════════════════════════════════════
            # SHARED — chart type + column pickers + filter + preview
            # ════════════════════════════════════════════════════════
            st.markdown("---")
            _cv_chart = st.selectbox(
                "Display As",
                ['table', 'bar_chart', 'line_chart', 'scatter', 'metric_cards'],
                key='cvb_chart',
                help=(
                    "table = sortable dataframe  |  bar/line/scatter = Plotly chart  "
                    "|  metric_cards = up to 5 large KPI tiles"
                ),
            )
            _need_axes = _cv_chart in ('bar_chart', 'line_chart', 'scatter', 'metric_cards')

            _cvc1, _cvc2, _cvc3 = st.columns(3)
            with _cvc1:
                if _need_axes:
                    _cv_chart_x = st.selectbox(
                        "X axis / Label column",
                        _cvb_cols if _cvb_ok else ['(fetch data first)'],
                        key='cvb_cx',
                        disabled=not _cvb_ok,
                    )
                    if not _cvb_ok:
                        _cv_chart_x = ''
                else:
                    _cv_chart_x = ''
                    st.caption("*X / Y not needed for table view*")

            with _cvc2:
                if _need_axes:
                    _yopts = _cvb_numcols if _cvb_numcols else _cvb_cols
                    _cv_chart_y = st.selectbox(
                        "Y axis / Value column",
                        _yopts if _cvb_ok else ['(fetch data first)'],
                        key='cvb_cy',
                        disabled=not _cvb_ok,
                    )
                    if not _cvb_ok:
                        _cv_chart_y = ''
                else:
                    _cv_chart_y = ''

            with _cvc3:
                _cv_fcol_raw = st.selectbox(
                    "Filter column (optional)",
                    ['(none)'] + (_cvb_cols if _cvb_ok else []),
                    key='cvb_fcol',
                )
                _cv_filter_col = '' if _cv_fcol_raw == '(none)' else _cv_fcol_raw

            _cv_filter_val = ''
            if _cv_filter_col and _cvb_ok and _cv_filter_col in _cvb_df.columns:
                _fv_uniq = sorted(
                    _cvb_df[_cv_filter_col].dropna().astype(str).unique().tolist()[:80]
                )
                if _fv_uniq:
                    _cv_fval_sel = st.selectbox(
                        f"Filter value for `{_cv_filter_col}`",
                        ['(all)'] + _fv_uniq,
                        key='cvb_fval',
                    )
                    _cv_filter_val = '' if _cv_fval_sel == '(all)' else _cv_fval_sel
                else:
                    st.caption(f"No values found in `{_cv_filter_col}`.")
            elif _cv_filter_col:
                _cv_filter_val = st.text_input("Filter value", key='cvb_fval')

            # ── Live Preview ──────────────────────────────────────
            st.markdown("---")
            st.markdown("##### 🔍 Live Preview")
            if _cvb_ok:
                if _cvb_is_live:
                    st.caption(
                        f"Showing live data from **{_cv_ep_type}** for **{_cv_sport}** "
                        f"({len(_cvb_df):,} rows fetched)"
                    )
                    _cvb_now_cfg = dict(
                        name=_cv_name or '(untitled)',
                        description=_cv_desc or '',
                        sport_key=_cv_sport,
                        data_source='espn_live',
                        chart_type=_cv_chart,
                        chart_x=_cv_chart_x if isinstance(_cv_chart_x, str) else '',
                        chart_y=_cv_chart_y if isinstance(_cv_chart_y, str) else '',
                        filter_col=_cv_filter_col,
                        filter_val=_cv_filter_val if isinstance(_cv_filter_val, str) else '',
                        schema_url=_cvb_live_url,
                        schema_params=_cvb_live_params,
                        schema_fields=_cvb_live_fields,
                    )
                else:
                    _src_label = _CVB_SOURCES.get(_cv_data_src, (_cv_data_src, ''))[0]
                    st.caption(
                        f"Showing **{_src_label}** for **{_cv_sport}** "
                        f"({len(_cvb_df):,} rows in DB)"
                    )
                    _cvb_now_cfg = dict(
                        name=_cv_name or '(untitled)',
                        description=_cv_desc or '',
                        sport_key=_cv_sport,
                        data_source=_cv_data_src,
                        chart_type=_cv_chart,
                        chart_x=_cv_chart_x if isinstance(_cv_chart_x, str) else '',
                        chart_y=_cv_chart_y if isinstance(_cv_chart_y, str) else '',
                        filter_col=_cv_filter_col,
                        filter_val=_cv_filter_val if isinstance(_cv_filter_val, str) else '',
                    )
                _cv_run_view(_cvb_now_cfg)
            else:
                st.info(
                    "⬜ No preview yet — "
                    + ("click **📡 Fetch** above to load live data."
                       if _cv_src_type.startswith("📡")
                       else "populate the selected DB table to see a preview.")
                )

            # ── Save ──────────────────────────────────────────────
            st.markdown("---")
            _cvs_col1, _cvs_col2 = st.columns(2)

            def _cvb_build_cfg():
                _base = dict(
                    name=(_cv_name or '').strip(),
                    description=(_cv_desc or '').strip(),
                    sport_key=_cv_sport,
                    chart_type=_cv_chart,
                    chart_x=_cv_chart_x if isinstance(_cv_chart_x, str) else '',
                    chart_y=_cv_chart_y if isinstance(_cv_chart_y, str) else '',
                    filter_col=_cv_filter_col,
                    filter_val=_cv_filter_val if isinstance(_cv_filter_val, str) else '',
                )
                if _cvb_is_live:
                    _base.update(dict(
                        data_source='espn_live',
                        schema_url=_cvb_live_url,
                        schema_params=_cvb_live_params,
                        schema_fields=_cvb_live_fields,
                    ))
                else:
                    _base['data_source'] = _cv_data_src
                return _base

            with _cvs_col1:
                if st.button("💾 Add to Session", key='cvb_ses',
                             help="Store for this session only — lost on page reload."):
                    if not (_cv_name or '').strip():
                        st.error("View Name is required.")
                    else:
                        st.session_state['cv_session_views'].append(_cvb_build_cfg())
                        st.success(f"✅ \"{_cv_name}\" added to session.")
                        st.rerun()

            with _cvs_col2:
                if st.button("📁 Save to Disk", key='cvb_disk',
                             help="Saves a JSON config — appears on the Custom Views tab after restart."):
                    if not (_cv_name or '').strip():
                        st.error("View Name is required.")
                    else:
                        _new_cv = _cvb_build_cfg()
                        _safe_name = "".join(
                            c if c.isalnum() or c in '._- ' else '_'
                            for c in _new_cv['name']
                        ).replace(' ', '_')[:60]
                        _cv_path = os.path.join(_cv_dir, f"{_safe_name}.json")
                        with open(_cv_path, 'w', encoding='utf-8') as _cvf:
                            json.dump(_new_cv, _cvf, indent=2)
                        if _new_cv not in st.session_state['cv_session_views']:
                            st.session_state['cv_session_views'].append(_new_cv)
                        st.success(
                            f"✅ Saved to `{_cv_path}`. "
                            "Appears on the **📋 Custom Views** tab."
                        )
                        st.rerun()

    # ── TAB 9: RAW INSPECTOR ───────────────────────────────
    with tab9:
        if not _render_admin_gate('t8'):
            pass
        else:
            st.subheader("Raw JSON Inspector")
            st.caption("Explore the full JSON structure returned by ESPN for any endpoint.")

            active_eps = json.loads(db.get_config('active_endpoints', '[]'))

            col_ep6, col_type6 = st.columns(2)
            with col_ep6:
                sel_ep6 = st.selectbox("Endpoint", active_eps or ['football/nfl'], key="raw_ep")
            with col_type6:
                ep_types = ['scoreboard', 'teams', 'news', 'rankings']
                sel_type = st.selectbox("Type", ep_types, key="raw_type")

            date_param = st.text_input(
                "Date param (YYYYMMDD, scoreboard only)",
                placeholder="e.g. 20260416"
            )

            if st.button("Fetch Raw JSON"):
                cat, sport = sel_ep6.split('/')
                params = {'dates': date_param} if date_param and sel_type == 'scoreboard' else None
                with st.spinner("Fetching…"):
                    data = worker.fetch_and_process(cat, sport, sel_type,
                                                    force_refresh=True, params=params)
                if data:
                    # Summary counts  — educational: explain what each type returns
                    type_explainers = {
                        'scoreboard': 'Live/final game scores, per-period breakdown, leaders, venue, broadcast info.',
                        'teams':      'Team metadata: name, abbreviation, colors, logos.',
                        'news':       'Latest ESPN articles tagged by athlete and team.',
                        'rankings':   'AP / Coaches poll rankings with rank movement.',
                    }
                    note = type_explainers.get(sel_type, '')
                    if note:
                        st.caption(f'ℹ️  **{sel_type}** endpoint returns: {note}')

                    if sel_type == 'scoreboard':
                        events = data.get('events', data.get('season', {}).get('events', []))
                        st.success(f"✅ {len(events)} events")
                    elif sel_type == 'teams':
                        try:
                            n = len(data['sports'][0]['leagues'][0]['teams'])
                            st.success(f"✅ {n} teams")
                        except Exception:
                            st.success("✅ Data fetched")
                    elif sel_type == 'news':
                        st.success(f"✅ {len(data.get('articles', []))} articles")
                    elif sel_type == 'rankings':
                        polls = data.get('rankings', [])
                        total = sum(len(p.get('ranks', [])) for p in polls)
                        st.success(f"✅ {len(polls)} polls, {total} ranked teams")

                    st.json(data)
                else:
                    st.error(f"Failed to fetch. Error: {worker.last_error}")

    # ── TAB 10: CUSTOM VIEWS ────────────────────────────────────
    with tab10:
        st.subheader("📋 Custom Views")
        st.caption(
            "Run saved views from this session, from disk, or downloaded from the Admin Panel. "
            "Build new views in the **🔬 Schema Explorer** tab."
        )

        _cv_dir9 = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'custom_views')
        _cv_pub9 = os.path.join(_cv_dir9, 'public')
        os.makedirs(_cv_dir9, exist_ok=True)
        os.makedirs(_cv_pub9, exist_ok=True)

        if 'cv_session_views' not in st.session_state:
            st.session_state['cv_session_views'] = []

        # ── Load views from disk into session ──────────────
        _cv9_disk_files = sorted(
            [f for f in os.listdir(_cv_dir9) if f.endswith('.json')
             and os.path.isfile(os.path.join(_cv_dir9, f))]
        )
        _cv9_pub_files = sorted(
            [f for f in os.listdir(_cv_pub9) if f.endswith('.json')
             and os.path.isfile(os.path.join(_cv_pub9, f))]
        )

        _cv9_c1, _cv9_c2 = st.columns([1, 1])
        with _cv9_c1:
            if _cv9_disk_files:
                _cv9_load_sel = st.multiselect(
                    "Load saved views from disk",
                    _cv9_disk_files,
                    key='cv9_load_sel',
                )
                if st.button("▶ Load Selected", key='cv9_load_btn'):
                    for _fn9 in _cv9_load_sel:
                        try:
                            with open(os.path.join(_cv_dir9, _fn9),
                                      encoding='utf-8') as _f9:
                                _loaded = json.load(_f9)
                            if _loaded not in st.session_state['cv_session_views']:
                                st.session_state['cv_session_views'].append(_loaded)
                        except Exception as _le:
                            st.warning(f"Could not load {_fn9}: {_le}")
                    st.rerun()
        with _cv9_c2:
            if _cv9_pub_files:
                st.caption(f"**{len(_cv9_pub_files)} public view(s)** available from Admin Panel")
                _cv9_pub_sel = st.multiselect(
                    "Load public views",
                    _cv9_pub_files,
                    key='cv9_pub_sel',
                )
                if st.button("▶ Load Public Views", key='cv9_pub_btn'):
                    for _fn9 in _cv9_pub_sel:
                        try:
                            with open(os.path.join(_cv_pub9, _fn9),
                                      encoding='utf-8') as _f9:
                                _loaded = json.load(_f9)
                            if _loaded not in st.session_state['cv_session_views']:
                                st.session_state['cv_session_views'].append(_loaded)
                        except Exception as _le:
                            st.warning(f"Could not load {_fn9}: {_le}")
                    st.rerun()

        # ── Render session views ──────────────────────────
        _sv_list = st.session_state.get('cv_session_views', [])
        if not _sv_list:
            st.info(
                "No views loaded yet. Build one in **🔬 Schema Explorer → Custom View Builder**, "
                "or load a saved view above."
            )
        else:
            for _vi, _vcfg in enumerate(_sv_list):
                with st.expander(
                    f"📊 {_vcfg.get('name', 'Unnamed View')}  ·  "
                    f"{_vcfg.get('sport_key', '')}  ·  "
                    f"{_vcfg.get('data_source', '')}  ·  "
                    f"{_vcfg.get('chart_type', 'table')}",
                    expanded=(_vi == 0),
                ):
                    if _vcfg.get('description'):
                        st.caption(_vcfg['description'])
                    _vcc1, _vcc2 = st.columns([5, 1])
                    with _vcc2:
                        if st.button("🗑 Remove", key=f'cv_remove_{_vi}'):
                            st.session_state['cv_session_views'].pop(_vi)
                            st.rerun()
                        _vexport = json.dumps(_vcfg, indent=2)
                        st.download_button(
                            "💾 Save .json",
                            data=_vexport,
                            file_name=f"{_vcfg.get('name','view').replace(' ','_')}.json",
                            mime='application/json',
                            key=f'cv_dl_{_vi}',
                        )
                    with _vcc1:
                        _cv_run_view(_vcfg)

    # ── TAB 11: ADMIN PANEL ───────────────────────────────────
    with tab11:
        st.subheader("🛠 Admin Panel")
        st.caption(
            "Upload custom view files to make them available to all users. "
            "Manage and delete published views."
        )

        if not _render_admin_gate('t10'):
            pass
        else:
            st.success("✅ Logged in as Admin")
            if st.button("🔒 Log out", key='admin_logout'):
                st.session_state['admin_authed'] = False
                st.session_state['_admin_pw_ok'] = False
                st.rerun()

            st.divider()

            # ── Change credentials ─────────────────────────────
            st.markdown("#### 🔑 Change Admin Credentials")
            _cred_c1, _cred_c2 = st.columns(2)
            with _cred_c1:
                _chg_pw = st.text_input(
                    "New Password (leave blank to keep)", type='password', key='adm_chg_pw')
                _chg_pw2 = st.text_input(
                    "Confirm New Password", type='password', key='adm_chg_pw2')
                if st.button("💾 Save Password", key='adm_save_pw'):
                    if not _chg_pw:
                        st.error("Password cannot be empty.")
                    elif _chg_pw != _chg_pw2:
                        st.error("Passwords do not match.")
                    elif len(_chg_pw) < 8:
                        st.error("Password must be at least 8 characters.")
                    else:
                        db.update_config(
                            'admin_password',
                            hashlib.sha256(_chg_pw.encode()).hexdigest()
                        )
                        st.success("Password updated. You will need it on next login.")
            with _cred_c2:
                _chg_pin = st.text_input(
                    "New PIN (leave blank to keep)", type='password', key='adm_chg_pin')
                _chg_pin2 = st.text_input(
                    "Confirm New PIN", type='password', key='adm_chg_pin2')
                if st.button("💾 Save PIN", key='adm_save_pin'):
                    if not _chg_pin:
                        st.error("PIN cannot be empty.")
                    elif _chg_pin != _chg_pin2:
                        st.error("PINs do not match.")
                    elif len(_chg_pin) < 4:
                        st.error("PIN must be at least 4 characters.")
                    else:
                        db.update_config(
                            'admin_pin',
                            hashlib.sha256(_chg_pin.encode()).hexdigest()
                        )
                        st.success("PIN updated. You will need it on next login.")

            st.divider()

            # ── Daily Auto-Sync ────────────────────────────
            st.markdown("#### 🔁 Daily Auto-Sync")
            st.caption(
                "Automatically fetch all data types (scoreboard, teams, news, rankings) "
                "for every active league once every 24 hours. "
                "The last sync time is stored in the database."
            )
            _adm_active_eps = json.loads(db.get_config('active_endpoints', '[]'))
            _last_daily_str = db.get_config('last_daily_sync', '')
            _daily_interval_h = int(db.get_config('daily_sync_interval_h', '24'))

            if _last_daily_str:
                try:
                    _last_daily_ts = float(_last_daily_str)
                    _since_h = (time.time() - _last_daily_ts) / 3600
                    _next_in = max(0, _daily_interval_h - _since_h)
                    st.info(
                        f"Last sync: **{datetime.fromtimestamp(_last_daily_ts).strftime('%Y-%m-%d %H:%M')}**"
                        f"  ·  Next sync due in **{_next_in:.1f}h**"
                        f"  ·  Interval: every **{_daily_interval_h}h**"
                    )
                except Exception:
                    st.info("Last sync time unavailable.")
            else:
                st.info("No daily sync has run yet.")

            _adm_da_c1, _adm_da_c2, _adm_da_c3 = st.columns([2, 2, 3])
            with _adm_da_c1:
                _new_interval = st.number_input(
                    "Sync interval (hours)", min_value=1, max_value=168,
                    value=_daily_interval_h, step=1, key='adm_sync_interval'
                )
                if st.button("💾 Save Interval", key='adm_save_interval'):
                    db.update_config('daily_sync_interval_h', str(_new_interval))
                    st.success("Saved!")
                    st.rerun()
            with _adm_da_c2:
                st.write("")
                st.write("")
                if st.button("▶ Run Full Sync Now", key='adm_run_sync', type='primary'):
                    if not _adm_active_eps:
                        st.warning("No active leagues configured. Add leagues in the sidebar first.")
                    else:
                        _sync_log = []
                        with st.spinner(f"Syncing {len(_adm_active_eps)} league(s) across all data types…"):
                            for _ep_s in _adm_active_eps:
                                _cat_s, _spt_s = _ep_s.split('/')
                                for _et_s in ['scoreboard', 'teams', 'news', 'rankings']:
                                    if not EndpointRegistry.get_url(_cat_s, _spt_s, _et_s):
                                        continue
                                    try:
                                        worker.fetch_and_process(
                                            _cat_s, _spt_s, _et_s, force_refresh=True
                                        )
                                        _sync_log.append(f"✅ {_ep_s}/{_et_s}")
                                    except Exception as _se:
                                        _sync_log.append(f"❌ {_ep_s}/{_et_s}: {_se}")
                        db.update_config('last_daily_sync', str(time.time()))
                        _fails = [l for l in _sync_log if l.startswith('❌')]
                        if _fails:
                            st.warning(
                                f"Sync complete with {len(_fails)} error(s):\n"
                                + '\n'.join(_fails[:5])
                            )
                        else:
                            st.success(f"✅ Full sync complete — {len(_sync_log)} endpoint(s) refreshed.")
                        st.rerun()
            with _adm_da_c3:
                with st.expander("📋 What does this sync?"):
                    st.markdown(
                        "For **every active league** it fetches:\n"
                        "- **Scoreboard** — latest game scores, status, leaders\n"
                        "- **Teams** — roster metadata, colours, logos\n"
                        "- **News** — latest ESPN articles\n"
                        "- **Rankings** — AP / Coaches poll (where available)\n\n"
                        "Data is written to the local SQLite database so all tabs "
                        "have fresh information without needing manual fetches."
                    )

            # Auto-trigger check (runs on every page load while admin is logged in)
            if _adm_active_eps and _last_daily_str:
                try:
                    _auto_ts = float(_last_daily_str)
                    _hours_elapsed = (time.time() - _auto_ts) / 3600
                    if _hours_elapsed >= _daily_interval_h:
                        st.toast(
                            f"⏰ Auto-sync triggered ({_hours_elapsed:.1f}h since last sync)…",
                            icon="🔄"
                        )
                        for _ep_a in _adm_active_eps:
                            _cat_a, _spt_a = _ep_a.split('/')
                            for _et_a in ['scoreboard', 'teams', 'news', 'rankings']:
                                if not EndpointRegistry.get_url(_cat_a, _spt_a, _et_a):
                                    continue
                                try:
                                    worker.fetch_and_process(
                                        _cat_a, _spt_a, _et_a, force_refresh=True
                                    )
                                except Exception:
                                    pass
                        db.update_config('last_daily_sync', str(time.time()))
                except Exception:
                    pass

            st.divider()

            _cv_dir10 = os.path.join(
                os.path.dirname(os.path.abspath(__file__)), 'custom_views')
            _cv_pub10 = os.path.join(_cv_dir10, 'public')
            os.makedirs(_cv_pub10, exist_ok=True)

            # Upload a custom view file
            st.markdown("#### Upload / Publish a Custom View")
            _up_file = st.file_uploader(
                "Upload a `.json` custom view file",
                type=['json'],
                key='admin_upload',
            )
            if _up_file is not None:
                try:
                    _up_data = json.loads(_up_file.read())
                    if 'name' not in _up_data:
                        st.error(
                            "Invalid view file — must have a `name` field."
                        )
                    else:
                        _safe10 = "".join(
                            c if c.isalnum() or c in '._- ' else '_'
                            for c in _up_data['name']
                        ).replace(' ', '_')[:60]
                        _pub_path = os.path.join(_cv_pub10, f"{_safe10}.json")
                        with open(_pub_path, 'w', encoding='utf-8') as _pf:
                            json.dump(_up_data, _pf, indent=2)
                        st.success(
                            f"✅ Published **{_up_data['name']}** — "
                            "users can now load it from the 📋 Custom Views tab."
                        )
                except Exception as _ue:
                    st.error(f"Failed to parse file: {_ue}")

            st.divider()

            # Manage published views
            st.markdown("#### Published Views")
            _pub10_files = sorted(
                [f for f in os.listdir(_cv_pub10) if f.endswith('.json')
                 and os.path.isfile(os.path.join(_cv_pub10, f))]
            )
            if not _pub10_files:
                st.info("No public views published yet. Upload one above.")
            else:
                for _pf_name in _pub10_files:
                    _pf_path = os.path.join(_cv_pub10, _pf_name)
                    try:
                        with open(_pf_path, encoding='utf-8') as _pff:
                            _pf_cfg = json.load(_pff)
                    except Exception:
                        _pf_cfg = {}
                    _pfc1, _pfc2, _pfc3 = st.columns([4, 2, 1])
                    with _pfc1:
                        st.markdown(
                            f"**{_pf_cfg.get('name', _pf_name)}**  "
                            f"·  `{_pf_cfg.get('sport_key','')}` "
                            f"·  {_pf_cfg.get('data_source','')} "
                            f"·  {_pf_cfg.get('chart_type','table')}"
                        )
                        if _pf_cfg.get('description'):
                            st.caption(_pf_cfg['description'])
                    with _pfc2:
                        _dl_bytes = json.dumps(_pf_cfg, indent=2).encode()
                        st.download_button(
                            "⬇ Download",
                            data=_dl_bytes,
                            file_name=_pf_name,
                            mime='application/json',
                            key=f'adm_dl_{_pf_name}',
                        )
                    with _pfc3:
                        if st.button("🗑", key=f'adm_del_{_pf_name}',
                                     help="Delete this public view"):
                            os.remove(_pf_path)
                            st.success(f"Deleted {_pf_name}")
                            st.rerun()
                    st.divider()

            # Personal saved views management
            st.markdown("#### Personal Saved Views")
            _cv10_files = sorted(
                [f for f in os.listdir(_cv_dir10) if f.endswith('.json')
                 and os.path.isfile(os.path.join(_cv_dir10, f))]
            )
            if not _cv10_files:
                st.info("No personal views saved yet.")
            else:
                for _cvf10 in _cv10_files:
                    _cvf10_path = os.path.join(_cv_dir10, _cvf10)
                    try:
                        with open(_cvf10_path, encoding='utf-8') as _f10:
                            _cfg10 = json.load(_f10)
                    except Exception:
                        _cfg10 = {}
                    _cv10c1, _cv10c2, _cv10c3 = st.columns([4, 2, 1])
                    with _cv10c1:
                        st.write(
                            f"**{_cfg10.get('name', _cvf10)}**  "
                            f"·  `{_cfg10.get('sport_key','')}` "
                            f"·  {_cfg10.get('data_source','')}"
                        )
                    with _cv10c2:
                        if st.button("📤 Publish", key=f'cv10_pub_{_cvf10}',
                                     help="Copy to public views"):
                            import shutil as _sh10
                            _sh10.copy2(
                                _cvf10_path,
                                os.path.join(_cv_pub10, _cvf10),
                            )
                            st.success(f"Published {_cvf10}")
                            st.rerun()
                    with _cv10c3:
                        if st.button("🗑", key=f'cv10_del_{_cvf10}',
                                     help="Delete personal view"):
                            os.remove(_cvf10_path)
                            st.success(f"Deleted {_cvf10}")
                            st.rerun()

    # ── TAB 12: SUPPORT / DONATE ───────────────────────────────
    with tab12:
        _render_donation_page()


if __name__ == "__main__":
    main()

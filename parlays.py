"""Parlay builder: every leg gets a probability from named sources, then we search for the most likely combinations.

Sources behind a leg (each is recorded so the UI can show exactly why a parlay was built):
  * team-form model   - season margin / points for and against from each team's results (matchups.predict)
  * betting markets   - ESPN's embedded book (no-vig) and Kalshi game-winner prices; the market anchors the model
  * live game state   - current score and clock projected to the final (live.live_projection)
  * player history    - how often a player cleared a milestone in his last games, adjusted for the opponent
  * NFL engine        - our play-by-play simulator, when it is loaded

Honest limits: legs from different games are treated as independent; one leg per game per parlay; player legs have no
sportsbook price here (model-only); live legs are propositions on the pre-game line that books no longer offer at those
terms.  Probabilities are estimates from public data, not guarantees and not betting advice.
"""
from __future__ import annotations

import heapq
import json
import math
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple

import pandas as pd

# Model leagues: team-form model + embedded lines exist for these.
MODEL_LEAGUES = ['football/nfl', 'football/college-football', 'basketball/nba', 'basketball/wnba',
                 'basketball/mens-college-basketball', 'basketball/womens-college-basketball',
                 'hockey/nhl', 'baseball/mlb']
# Spread of final margin / total by league (points, goals, runs): used to turn a mean into a probability.
SIGMA_MARGIN = {'football': 13.5, 'basketball': 12.0, 'hockey': 2.4, 'baseball': 4.2}
SIGMA_TOTAL = {'football/nfl': 10.5, 'football/college-football': 14.0, 'basketball/nba': 17.5, 'basketball/wnba': 14.0,
               'basketball/mens-college-basketball': 15.0, 'basketball/womens-college-basketball': 14.0,
               'hockey/nhl': 1.75, 'baseball/mlb': 3.6}
MAX_LEG_P = 0.97  # never treat a single leg as a lock
MAX_MODEL_ONLY_P = 0.90  # a winner leg with no market behind it is never more than this
PLAYER_AVAIL = 0.94  # allowance for a player resting, scratched late, hurt or benched in a blowout
MAX_PLAYER_P = 0.92

# Player milestone ladders per box-score category: stat -> thresholds.
MILESTONES: Dict[str, Dict[str, List[float]]] = {
    'stats': {'PTS': [10, 15, 20, 25], 'REB': [4, 6, 8, 10], 'AST': [3, 5, 7], '3PT': [2, 3]},
    'passing': {'YDS': [200, 250, 300], 'TD': [1, 2]},
    'rushing': {'YDS': [40, 60, 80]},
    'receiving': {'REC': [3, 4, 5, 6], 'YDS': [40, 60, 80]},
    'forwards': {'G': [1], 'A': [1], 'SOG': [3], 'S': [3]},
    'defenses': {'A': [1], 'SOG': [2]},
    'batting': {'H': [1, 2], 'R': [1], 'RBI': [1], 'HR': [1]},
    'pitching': {'K': [4, 5, 6, 7]},
}
STAT_WORD = {'PTS': 'points', 'REB': 'rebounds', 'AST': 'assists', '3PT': '3-pointers', 'YDS': 'yards', 'TD': 'TD',
             'REC': 'receptions', 'G': 'goals', 'A': 'assists', 'SOG': 'shots', 'S': 'shots', 'H': 'hits', 'R': 'runs',
             'RBI': 'RBI', 'HR': 'home runs', 'K': 'strikeouts'}
CAT_WORD = {'passing': 'passing', 'rushing': 'rushing', 'receiving': 'receiving'}


# ── Small probability helpers ────────────────────────────────────────────────

def norm_cdf(x: float) -> float:
    return 0.5 * (1 + math.erf(x / math.sqrt(2)))


def logit(p: float) -> float:
    p = min(1 - 1e-4, max(1e-4, p))
    return math.log(p / (1 - p))


def sigmoid(z: float) -> float:
    return 1 / (1 + math.exp(-z))


def american_to_prob(price: Optional[float]) -> Optional[float]:
    if price is None or (isinstance(price, float) and math.isnan(price)) or price == 0:
        return None
    return 100 / (price + 100) if price > 0 else -price / (-price + 100)


def prob_to_american(p: float) -> Optional[int]:
    if p <= 0 or p >= 1:
        return None
    return int(round(-100 * p / (1 - p))) if p >= 0.5 else int(round(100 * (1 - p) / p))


def devig_home(home_ml: Optional[float], away_ml: Optional[float]) -> Optional[float]:
    h, a = american_to_prob(home_ml), american_to_prob(away_ml)
    return h / (h + a) if h and a else None


def decimal_odds(price: Optional[float]) -> Optional[float]:
    if price is None or price == 0:
        return None
    return 1 + (price / 100 if price > 0 else 100 / -price)


def market_prob(parts: List[Tuple[str, float]]) -> Optional[float]:
    """Average of market probabilities in logit space (each already no-vig)."""
    vals = [p for _, p in parts if p is not None]
    return sigmoid(sum(logit(p) for p in vals) / len(vals)) if vals else None


# ── Data classes ─────────────────────────────────────────────────────────────

@dataclass
class Source:
    name: str      # e.g. "Team-form model"
    kind: str      # model | market | live | player | engine
    p: Optional[float]
    detail: str


@dataclass
class Leg:
    key: str
    game_id: str
    ep: str
    league: str
    matchup: str
    start: str
    state: str                 # pre | in
    kind: str                  # ml | spread | total | player
    pick: str
    p: float
    price: Optional[float] = None       # American price when a book offers this leg
    sources: List[Source] = field(default_factory=list)
    notes: List[str] = field(default_factory=list)
    live: bool = False
    meta: Dict[str, Any] = field(default_factory=dict)  # what is needed to grade the leg from a final box score
    edge: Optional[float] = None                        # our chance minus the market's, when a market exists
    bettable: bool = True                               # false once the game has started or no market can take it
    quotes: List[Dict[str, Any]] = field(default_factory=list)  # every price we found for this exact bet (see parlay_pricing)
    info: Dict[str, Any] = field(default_factory=dict)          # game, team, injury, model and player details shown to the user


@dataclass
class Parlay:
    legs: List[Leg]
    p: float
    fair_decimal: float
    market_decimal: Optional[float]
    ev: Optional[float]
    score: float

    @property
    def k(self) -> int:
        return len(self.legs)


# ── Leg construction ─────────────────────────────────────────────────────────

def anchored_margin(ep: str, model_margin: Optional[float], spread: Optional[float], w_model: float = 0.3
                    ) -> Tuple[Optional[float], str]:
    """Market-anchored expected margin: the line, nudged toward the model by w_model."""
    mkt = -spread if spread is not None and not math.isnan(spread) else None
    if model_margin is None and mkt is None:
        return None, 'none'
    if mkt is None:
        return model_margin * 0.85, 'model only (shrunk)'
    if model_margin is None:
        return mkt, 'market only'
    return mkt + w_model * (model_margin - mkt), 'market-anchored'


def anchored_total(model_total: Optional[float], line: Optional[float], w_model: float = 0.3
                   ) -> Tuple[Optional[float], str]:
    if line is not None and not math.isnan(line):
        if model_total is None:
            return line, 'market only'
        return line + w_model * (model_total - line), 'market-anchored'
    return (model_total, 'model only') if model_total is not None else (None, 'none')


def ml_legs(g: Dict, pred: Optional[Dict], blend_w: float, engine_p: Optional[float],
            live_proj: Optional[Dict], require_market: bool = False) -> List[Leg]:
    """Winner legs for both sides of one game."""
    parts: List[Tuple[str, float]] = []
    ph_espn = devig_home(g.get('home_ml'), g.get('away_ml'))
    if ph_espn is not None:
        parts.append((g.get('book') or 'ESPN book', ph_espn))
    if g.get('kalshi_home') is not None and not pd.isna(g.get('kalshi_home')):
        parts.append(('Kalshi', float(g['kalshi_home'])))
    p_mkt = market_prob(parts)
    p_model = pred['p_home'] if pred else None
    srcs: List[Source] = []
    if pred:
        srcs.append(Source('Team-form model', 'model', p_model,
                           f"{g['home_abbr']} margin rating vs {g['away_abbr']}: projected margin {pred['margin']:+.1f}"))
    if engine_p is not None:
        srcs.append(Source('NFL engine', 'engine', engine_p, 'play-by-play simulation, calibrated'))
        p_model = engine_p if p_model is None else sigmoid((logit(p_model) + logit(engine_p)) / 2)
    for name, p in parts:
        srcs.append(Source(name, 'market', p, 'no-vig win probability'))

    live = live_proj is not None
    if live:
        p_home = live_proj['p_home']
        srcs.append(Source('Live game state', 'live', p_home,
                           f"score {g['away_abbr']} {g['away_score']} - {g['home_abbr']} {g['home_score']}, "
                           f"{live_proj['f']:.0%} of game left, projected final margin {live_proj['margin']:+.1f}"))
        how = 'live projection (pre-game model / market prior + current score and clock)'
    elif p_model is not None and p_mkt is not None:
        p_home = sigmoid(logit(p_mkt) + blend_w * (logit(p_model) - logit(p_mkt)))
        how = f'market-anchored: market {p_mkt:.0%}, model nudged in with weight {blend_w:.2f}'
    elif p_mkt is not None:
        p_home, how = p_mkt, 'market only (no model for this matchup yet)'
    elif p_model is not None and not require_market:
        p_home, how = sigmoid(0.85 * logit(p_model)), 'model only, shrunk 15% toward even because no market price was found'
        p_home = min(MAX_MODEL_ONLY_P, max(1 - MAX_MODEL_ONLY_P, p_home))
    else:
        return []
    legs = []
    for side, p, name, abbr in (('home', p_home, g['home'], g['home_abbr']), ('away', 1 - p_home, g['away'], g['away_abbr'])):
        pp = min(MAX_LEG_P, p)
        if pp <= 0.5:
            continue
        mkt_side = None if p_mkt is None else (p_mkt if side == 'home' else 1 - p_mkt)
        price = g.get('home_ml') if side == 'home' else g.get('away_ml')
        sg = [Source(s.name, s.kind, s.p if side == 'home' or s.p is None else 1 - s.p, s.detail) for s in srcs]
        legs.append(Leg(
            key=f"{g['id']}:ml:{side}", game_id=g['id'], ep=g['ep'], league=g['league'],
            matchup=f"{g['away_abbr']} @ {g['home_abbr']}", start=g['start'], state=g['state'], kind='ml',
            pick=f'{name} to win', p=pp, price=None if live else (None if price is None or pd.isna(price) else float(price)),
            sources=sg, notes=[how], live=live,
            meta={'kind': 'ml', 'side': side, 'home': g['home'], 'away': g['away'], 'home_abbr': g['home_abbr'],
                  'away_abbr': g['away_abbr']},
            edge=None if mkt_side is None else pp - mkt_side, bettable=(not live and g['state'] == 'pre')))
    return legs


def spread_total_legs(g: Dict, pred: Optional[Dict], blend_w: float, live_proj: Optional[Dict]) -> List[Leg]:
    ep = g['ep']
    sigma = SIGMA_MARGIN.get(ep.split('/')[0], 12.0)
    legs: List[Leg] = []
    spread, total = g.get('spread'), g.get('total')
    live = live_proj is not None
    mname = f"{g['away_abbr']} @ {g['home_abbr']}"
    if spread is not None and not pd.isna(spread):
        if live:
            m, s_eff = live_proj['margin'], math.sqrt(sigma ** 2 * live_proj['f'] + (0.25 * sigma) ** 2)
            how = f"live: projected final margin {m:+.1f} vs the pre-game line {spread:+g}, uncertainty {s_eff:.1f}"
            src = Source('Live game state', 'live', None, how)
        else:
            m, how = anchored_margin(ep, pred['margin'] if pred else None, spread, blend_w)
            s_eff = sigma
            src = Source('Team-form model + line', 'model', None, f"{how}: expected margin {m:+.1f} vs line {spread:+g}")
        if m is not None:
            p_home = norm_cdf((m + spread) / s_eff)
            for side, p, name, line in (('home', p_home, g['home_abbr'], spread), ('away', 1 - p_home, g['away_abbr'], -spread)):
                if min(MAX_LEG_P, p) > 0.5:
                    legs.append(Leg(f"{g['id']}:spread:{side}", g['id'], ep, g['league'], mname, g['start'], g['state'], 'spread',
                                    f'{name} {line:+g}', min(MAX_LEG_P, p), None, [Source(src.name, src.kind, min(MAX_LEG_P, p), src.detail)],
                                    [how], live,
                                    meta={'kind': 'spread', 'side': side, 'line': float(line), 'home': g['home'], 'away': g['away'],
                                          'home_abbr': g['home_abbr'], 'away_abbr': g['away_abbr']},
                                    bettable=(not live and g['state'] == 'pre')))
    if total is not None and not pd.isna(total):
        sig_t = SIGMA_TOTAL.get(ep, 12.0)
        if live:
            t_mean = live_proj['home_final'] + live_proj['away_final']
            s_eff = math.sqrt(sig_t ** 2 * live_proj['f'] + (0.15 * sig_t) ** 2)
            how = f"live: projected final total {t_mean:.1f} vs the pre-game total {total:g}, uncertainty {s_eff:.1f}"
            name_src = 'Live game state'
        else:
            mt = (pred['home_pts'] + pred['away_pts']) if pred else None
            t_mean, how0 = anchored_total(mt, total, blend_w)
            s_eff, name_src = sig_t, 'Team-form model + line'
            how = f"{how0}: expected total {t_mean:.1f} vs line {total:g}" if t_mean is not None else ''
        if t_mean is not None:
            p_over = 1 - norm_cdf((total - t_mean) / s_eff)
            for side, p, word in (('over', p_over, 'Over'), ('under', 1 - p_over, 'Under')):
                if min(MAX_LEG_P, p) > 0.5:
                    legs.append(Leg(f"{g['id']}:total:{side}", g['id'], ep, g['league'], mname, g['start'], g['state'], 'total',
                                    f'{word} {total:g} total', min(MAX_LEG_P, p), None,
                                    [Source(name_src, 'live' if live else 'model', min(MAX_LEG_P, p), how)], [how], live,
                                    meta={'kind': 'total', 'side': side, 'line': float(total), 'home': g['home'], 'away': g['away'],
                                          'home_abbr': g['home_abbr'], 'away_abbr': g['away_abbr']},
                                    bettable=(not live and g['state'] == 'pre')))
    return legs


def player_legs(db: Any, g: Dict, team_abbr: str, team_id: str, opp_factor: float, max_per_team: int = 4) -> List[Leg]:
    """Milestone legs from each rotation player's recent box scores, adjusted for the opponent."""
    ep = g['ep']
    try:
        raw = db.get_team_players_stats(ep, team_abbr)
    except Exception:
        return []
    if raw is None or raw.empty:
        return []
    out_names = set()
    try:
        roster = db.get_team_roster_players(ep, team_id)
        if not roster.empty:
            bad = roster['injury_status'].fillna('').str.lower().str.contains('out|reserve|doubtful|suspen|inactive')
            out_names = set(roster.loc[bad, 'display_name'])
            quest = set(roster.loc[roster['injury_status'].fillna('').str.lower().str.contains('questionable|day'), 'display_name'])
        else:
            quest = set()
    except Exception:
        quest = set()
    rows = []
    for r in raw.itertuples():
        cat = (r.category or 'stats').lower()
        ladder = MILESTONES.get(cat)
        if not ladder:
            continue
        try:
            labels, vals = json.loads(r.stat_labels), json.loads(r.stat_values)
        except Exception:
            continue
        for lab, v in zip(labels, vals):
            if lab not in ladder:
                continue
            try:
                num = float(str(v).split('-')[0].split('/')[0].replace(',', ''))
            except ValueError:
                continue
            rows.append((r.player_name, cat, lab, num, r.event_id, r.game_date or ''))
    if not rows:
        return []
    df = pd.DataFrame(rows, columns=['player', 'cat', 'stat', 'value', 'event', 'date'])
    recent = (df[['event', 'date']].drop_duplicates('event').sort_values('date', ascending=False)['event'].head(10).tolist())
    team_games = max(1, len(recent))
    df = df[df['event'].isin(recent)]
    f = min(1.1, max(0.9, opp_factor or 1.0))
    mname = f"{g['away_abbr']} @ {g['home_abbr']}"
    cands: List[Leg] = []
    for (player, cat, stat), sub in df.groupby(['player', 'cat', 'stat']):
        if player in out_names:
            continue
        vals = sub['value'].tolist()
        n = len(vals)
        if n < 6 or n < 0.6 * team_games:
            continue
        mu = sum(vals) / n
        mean = mu * f
        sd = max(0.5, (sum((x - mu) ** 2 for x in vals) / max(1, n - 1)) ** 0.5)
        rungs = []
        for thr in MILESTONES[cat][stat]:
            hits = sum(1 for x in vals if x >= thr)
            p_emp = (hits + 0.5) / (n + 1)
            p_norm = 1 - norm_cdf((thr - 0.5 - mean) / sd)
            p = 0.5 * p_emp + 0.5 * p_norm
            notes = []
            if player in quest:
                p *= 0.8
                notes.append('listed questionable: probability cut 20%')
            if PLAYER_AVAIL < 1:
                p *= PLAYER_AVAIL
            rungs.append((thr, min(MAX_PLAYER_P, p), hits, p_norm, notes))
        good = [r for r in rungs if r[1] >= 0.8]
        pick_r = max(good, key=lambda r: r[0]) if good else max(rungs, key=lambda r: r[1])
        thr, p, hits, p_norm, notes = pick_r
        if p < 0.55:
            continue
        word = STAT_WORD.get(stat, stat.lower())
        cat_w = CAT_WORD.get(cat, '')
        src = Source('Player history', 'player', p,
                     f'{hits} of last {n} games at {thr:g}+ ({100 * hits / n:.0f}%); avg {mu:.1f}, sd {sd:.1f}; '
                     f'opponent factor {f:.2f} -> expected {mean:.1f}; normal-curve {p_norm:.0%}; includes a '
                     f'{round((1 - PLAYER_AVAIL) * 100)}% allowance for him not playing a full role')
        cands.append(Leg(f"{g['id']}:pl:{player}:{cat}:{stat}:{thr:g}", g['id'], ep, g['league'], mname, g['start'], g['state'],
                         'player', f'{player} {thr:g}+ {cat_w + " " if cat_w else ""}{word}', p, None, [src],
                         notes + ['model-only: no sportsbook price in our data'],
                         meta={'kind': 'player', 'player': player, 'cat': cat, 'stat': stat, 'thr': float(thr), 'team_abbr': team_abbr,
                               'home': g.get('home', ''), 'away': g.get('away', ''), 'home_abbr': g['home_abbr'],
                               'away_abbr': g['away_abbr']},
                         bettable=(g['state'] == 'pre'),
                         info={'player': player, 'team': team_abbr, 'stat': f'{stat} ({cat})', 'threshold': float(thr),
                               'games_used': n, 'team_games': team_games, 'recent_values': [float(v) for v in vals],
                               'average': mu, 'std_dev': sd, 'hits': hits, 'opponent_factor': f, 'expected': mean,
                               'availability_allowance': 1 - PLAYER_AVAIL, 'listed_questionable': player in quest}))
    cands.sort(key=lambda l: -l.p)
    return cands[:max_per_team]


def _start_ts(start: str) -> Optional[pd.Timestamp]:
    t = pd.to_datetime(start, utc=True, errors='coerce')
    return None if pd.isna(t) else t


def drop_unbettable(legs: List[Leg], now: Optional[pd.Timestamp] = None, lead_minutes: int = 3) -> List[Leg]:
    """Keep only legs a bettor can still place: not live, not started (or about to), flagged bettable."""
    now = now if now is not None else pd.Timestamp.now(tz='UTC')
    keep = []
    for l in legs:
        t = _start_ts(l.start)
        if not l.bettable or l.live or l.state != 'pre' or t is None or t <= now + pd.Timedelta(minutes=lead_minutes):
            continue
        keep.append(l)
    return keep


def eligible_leagues(board: pd.DataFrame, hours: int, leagues: List[str], now: Optional[pd.Timestamp] = None) -> Dict[str, int]:
    """{league: games still to be played inside the window}.  A league with none is out of season (or idle) and is excluded."""
    if board is None or board.empty:
        return {}
    now = now if now is not None else pd.Timestamp.now(tz='UTC')
    start = pd.to_datetime(board['start'], utc=True, errors='coerce')
    ok = board[(board['state'] == 'pre') & (start > now) & (start < now + pd.Timedelta(hours=hours))]
    counts = ok.groupby('ep').size().to_dict()
    return {e: int(counts[e]) for e in leagues if counts.get(e)}


def leg_to_dict(l: Leg) -> Dict:
    return {'key': l.key, 'game_id': l.game_id, 'ep': l.ep, 'league': l.league, 'matchup': l.matchup, 'start': l.start,
            'kind': l.kind, 'pick': l.pick, 'p': l.p, 'price': l.price, 'meta': l.meta, 'edge': l.edge,
            'sources': [vars(s) for s in l.sources], 'notes': l.notes, 'quotes': l.quotes, 'info': l.info}


def leg_from_dict(d: Dict) -> Leg:
    return Leg(d['key'], d['game_id'], d['ep'], d['league'], d['matchup'], d.get('start', ''), 'pre', d['kind'], d['pick'],
               float(d['p']), d.get('price'), [Source(**s) for s in d.get('sources', [])], list(d.get('notes', [])), False,
               meta=d.get('meta', {}), edge=d.get('edge'), quotes=list(d.get('quotes', [])), info=dict(d.get('info', {})))


# ── Collecting candidate legs ────────────────────────────────────────────────

_CACHE: Dict[tuple, Tuple[float, Any]] = {}
CACHE_TTL = 90


def _form_view(f: Dict) -> Dict:
    if not f or not f.get('n'):
        return {}
    keep = ('n', 'wins', 'losses', 'pf', 'pa', 'margin', 'last5', 'rating', 'streak')
    return {k: (round(f[k], 2) if isinstance(f.get(k), float) else f.get(k)) for k in keep if k in f}


def _decorate(legs: List[Leg], g: Dict, pred: Optional[Dict], fh: Dict, fa: Dict, inj_h: Dict, inj_a: Dict,
              engine_p: Optional[float], blend_w: float) -> None:
    """Attach ESPN and Kalshi prices and the game and team facts behind the numbers to every leg of one game."""
    import parlay_pricing as PP
    game = {'matchup': f"{g['away']} at {g['home']}", 'start': g['start'], 'tv': g.get('tv', ''), 'espn_book': g.get('book', ''),
            'lines': {'spread (home)': g.get('spread'), 'total': g.get('total'), 'home moneyline': g.get('home_ml'),
                      'away moneyline': g.get('away_ml')},
            'kalshi_home_win': g.get('kalshi_home'), 'engine_home_win': engine_p, 'model_weight_vs_market': blend_w,
            'form_home': _form_view(fh), 'form_away': _form_view(fa),
            'model': None if not pred else {k: round(float(v), 2) for k, v in pred.items() if isinstance(v, (int, float))},
            'injuries_home': inj_h.get('players', [])[:6], 'injuries_away': inj_a.get('players', [])[:6]}
    for l in legs:
        if l.kind in ('ml', 'spread', 'total'):
            l.quotes += PP.espn_quotes(g, l.kind, l.meta['side'])
            if l.kind == 'ml':
                l.quotes += PP.kalshi_quote(g, l.meta['side'])
            l.info = dict(game)
        else:
            l.info = {**l.info, 'game': game}


def collect_legs(db: Any, worker: Any, season_for: Callable[[str], int], label: Callable[[str], str],
                 eps: List[str], hours_ahead: int = 24, include_live: bool = False, per_league: int = 10,
                 types: Tuple[str, ...] = ('ml', 'spread', 'total', 'player'), engine_probs: Optional[Dict] = None,
                 blend: Optional[Dict[str, float]] = None, progress: Optional[Callable[[str], None]] = None,
                 require_market: bool = True) -> Tuple[List[Leg], Dict]:
    """Candidate legs for live and upcoming games.  Returns (legs, info) where info lists what was and was not covered."""
    key = (tuple(sorted(eps)), hours_ahead, include_live, per_league, tuple(types), bool(engine_probs), require_market)
    hit = _CACHE.get(key)
    if hit and time.time() - hit[0] < CACHE_TTL:
        return drop_unbettable(hit[1][0]), hit[1][1]
    from concurrent.futures import as_completed

    from live import fetch_all_games, fraction_remaining, live_projection
    from matchups import BLEND, injury_penalty, predict, team_form
    from odds_page import KALSHI_SERIES, attach_kalshi, fetch_kalshi_markets

    say = progress or (lambda m: None)
    say('Reading every scoreboard...')
    allg = fetch_all_games(tuple(eps))
    info: Dict = {'leagues': {}, 'built_at': time.time(), 'skipped': [], 'errors': {}}
    if allg.empty:
        return [], info
    allg = allg.copy()
    allg['league'] = allg['ep'].map(label)
    now = pd.Timestamp.now(tz='UTC')
    start = pd.to_datetime(allg['start'], utc=True, errors='coerce')
    soon = allg['state'].eq('pre') & (start < now + pd.Timedelta(hours=hours_ahead)) & (start > now - pd.Timedelta(hours=1))
    keep = allg[(allg['state'].eq('in') & include_live) | soon].copy()
    w_all = dict(BLEND)
    w_all.update(blend or {})

    def one_league(ep: str, grp: pd.DataFrame) -> Tuple[List[Leg], int, Dict[str, Dict]]:
        grp = grp.assign(_live=grp['state'].eq('in')).sort_values(['_live', 'start'], ascending=[False, True]).head(per_league)
        cat, spt = ep.split('/')
        season = season_for(cat)
        if ep in KALSHI_SERIES:
            kdf = grp.assign(home_team=grp['home'], away_team=grp['away'], home_loc=grp.get('home_loc', ''),
                             away_loc=grp.get('away_loc', ''))
            grp = attach_kalshi(kdf.reset_index(drop=True), fetch_kalshi_markets(KALSHI_SERIES[ep])[0])
        else:
            grp = grp.assign(kalshi_home=None)
        tids = sorted(set(grp['home_id']) | set(grp['away_id']))
        with ThreadPoolExecutor(max_workers=4) as pool:
            forms = dict(zip(tids, pool.map(lambda t: team_form(db, worker, cat, spt, t, season), tids)))
        pas = [f['pa'] for f in forms.values() if f.get('n')]
        avg_pa = sum(pas) / len(pas) if pas else None
        out: List[Leg] = []
        seen_games: Dict[str, Dict] = {}
        for g in grp.to_dict('records'):
            seen_games[str(g['id'])] = g
            first = len(out)
            fh, fa = forms.get(g['home_id'], {'n': 0}), forms.get(g['away_id'], {'n': 0})
            pred, inj_h, inj_a = None, {'penalty': 0.0, 'players': []}, {'penalty': 0.0, 'players': []}
            if fh.get('n') and fa.get('n'):
                inj_h = injury_penalty(db, ep, g['home_id'], g['home_abbr'], fh.get('pf', 0))
                inj_a = injury_penalty(db, ep, g['away_id'], g['away_abbr'], fa.get('pf', 0))
                ph, pa = inj_h['penalty'], inj_a['penalty']
                pred = predict(ep, fh, fa, ph, pa)
            bw = w_all.get(ep, 0.3)
            lp = None
            if g['state'] == 'in':
                # anchor the live projection on the market-anchored pre-game expectation
                anchor = dict(pred) if pred else None
                if anchor is not None:
                    m_a, _ = anchored_margin(ep, anchor['margin'], g.get('spread'), bw)
                    t_a, _ = anchored_total(anchor['home_pts'] + anchor['away_pts'], g.get('total'), bw)
                    if m_a is not None and t_a is not None:
                        anchor.update(margin=m_a, home_pts=t_a / 2 + m_a / 2, away_pts=t_a / 2 - m_a / 2)
                lp = live_projection(ep, anchor, int(g['home_score']), int(g['away_score']), int(g['period'] or 0), g['clock'])
                lp['f'] = fraction_remaining(ep, int(g['period'] or 0), g['clock'])
            eng = (engine_probs or {}).get((g['home_abbr'], g['away_abbr'])) if ep == 'football/nfl' and g['state'] == 'pre' else None
            if 'ml' in types:
                out += ml_legs(g, pred, bw, eng, lp, require_market)
            if 'spread' in types or 'total' in types:
                out += [l for l in spread_total_legs(g, pred, bw, lp) if l.kind in types]
            if 'player' in types and g['state'] == 'pre' and avg_pa:
                for abbr, tid, opp in ((g['home_abbr'], g['home_id'], fa), (g['away_abbr'], g['away_id'], fh)):
                    of = (opp.get('pa') / avg_pa) if opp.get('n') and avg_pa else 1.0
                    out += player_legs(db, g, abbr, tid, of)
            _decorate(out[first:], g, pred, fh, fa, inj_h, inj_a, eng, bw)
        return out, int(len(grp)), seen_games

    legs: List[Leg] = []
    all_games: Dict[str, Dict] = {}
    groups = [(ep, grp) for ep, grp in keep.groupby('ep')]
    with ThreadPoolExecutor(max_workers=3) as pool:
        futs = {pool.submit(one_league, ep, grp): ep for ep, grp in groups}
        for f in as_completed(futs):
            ep = futs[f]
            try:
                ls, n_games, gms = f.result()
                legs += ls
                all_games.update(gms)
                info['leagues'][ep] = {'label': label(ep), 'games': n_games, 'legs': len(ls)}
                say(f'{label(ep)}: {n_games} games priced, {len(ls)} candidate legs')
            except Exception as exc:  # one league failing must not sink the page
                info['errors'][ep] = str(exc)[:120]
                say(f'{label(ep)}: skipped ({str(exc)[:80]})')
    info['skipped'] = [label(e) for e in eps if e not in info['leagues']]
    if True:
        say('Fetching sportsbook prices (Unabated)...')
        try:
            import parlay_pricing
            info['pricing'] = parlay_pricing.attach_unabated(legs, all_games)
        except Exception as exc:  # prices are an add-on: never lose the legs because a price feed failed
            info['pricing'] = {'errors': [str(exc)[:100]], 'leagues': {}}
    try:
        import parlay_pricing as _pp
        for l in legs:
            bq = _pp._book_quotes(l)
            if bq:
                l.price = max(bq.values(), key=lambda q: q['decimal'])['price']
    except Exception:
        pass
    res = (legs, info)
    _CACHE[key] = (time.time(), res)
    kept = drop_unbettable(legs)
    info['dropped_unbettable'] = len(legs) - len(kept)
    return kept, info


# ── Parlay search ────────────────────────────────────────────────────────────

def _parlay(legs: List[Leg], rank: str) -> Parlay:
    p = 1.0
    for l in legs:
        p *= l.p
    dec = None
    if all(l.price is not None for l in legs):
        dec = 1.0
        for l in legs:
            dec *= decimal_odds(l.price) or 1.0
    ev = None if dec is None else p * dec - 1
    if rank == 'value' and ev is not None:
        score = ev
    elif rank == 'value':  # unpriced legs earn no edge; rank by probability among the priced
        score = -1 + p * 0.001
    else:
        score = p
    return Parlay(legs, p, 1 / p if p else float('inf'), dec, ev, score)


def build_parlays(legs: List[Leg], kmin: int = 4, kmax: int = 7, top: int = 10, min_p: float = 0.6,
                  max_player: int = 2, rank: str = 'likely', width: int = 1500, max_overlap: Optional[int] = None,
                  options_per_game: int = 3) -> List[Parlay]:
    """Best combinations of ``kmin``..``kmax`` legs from different games.

    Beam search over games ordered by their best leg; each game offers its few strongest legs.  A greedy pass then keeps
    the top ``top`` parlays, mixing leg counts and rejecting near-duplicates (sharing more than ``max_overlap`` legs).
    """
    pool = [l for l in legs if l.p >= min_p]
    by_game: Dict[str, List[Leg]] = {}
    for l in pool:
        by_game.setdefault(l.game_id, []).append(l)
    games = []
    for gid, ls in by_game.items():
        ls.sort(key=lambda x: -x.p)
        # at most options_per_game legs per game, always keeping the best non-player leg as an option
        opts = ls[:options_per_game]
        games.append((gid, opts))
    games.sort(key=lambda t: -t[1][0].p)
    if len(games) < kmin:
        return []
    # beam[size] = list of (neg_logp, last_game_index, leg_indices tuple, n_player)
    flat: List[Leg] = []
    index: Dict[str, int] = {}
    for _, opts in games:
        for l in opts:
            index[l.key] = len(flat)
            flat.append(l)
    beams: Dict[int, List[Tuple[float, int, Tuple[int, ...], int]]] = {0: [(0.0, -1, (), 0)]}
    results: Dict[int, List[Tuple[float, Tuple[int, ...]]]] = {k: [] for k in range(kmin, kmax + 1)}
    for size in range(1, kmax + 1):
        nxt: List[Tuple[float, int, Tuple[int, ...], int]] = []
        for neg, last, chosen, npl in beams[size - 1]:
            for gi in range(last + 1, len(games)):
                for l in games[gi][1]:
                    is_pl = l.kind == 'player'
                    if is_pl and npl >= max_player:
                        continue
                    nxt.append((neg - math.log(l.p), gi, chosen + (index[l.key],), npl + is_pl))
        nxt = heapq.nsmallest(width, nxt, key=lambda t: t[0])
        beams[size] = nxt
        if size >= kmin:
            results[size] = [(t[0], t[2]) for t in nxt]
    # candidates from every size, scored; then greedy diversified selection
    cands: List[Parlay] = []
    for size, lst in results.items():
        for neg, chosen in lst[:400]:
            cands.append(_parlay([flat[i] for i in chosen], rank))
    cands.sort(key=lambda p: -p.score)
    picked: List[Parlay] = []
    sets: List[Tuple[int, set]] = []
    # first the best parlay of each leg count so the page offers real options, then fill by score
    order: List[Parlay] = []
    for size in range(kmin, kmax + 1):
        best = next((c for c in cands if c.k == size), None)
        if best is not None:
            order.append(best)
    order = sorted(order, key=lambda p: -p.score)[:max(1, min(top, kmax - kmin + 1))] + cands
    for c in order:
        ks = {l.key for l in c.legs}
        ov = max_overlap if max_overlap is not None else max(1, c.k - 2)
        # near-duplicates are judged within the same leg count (a 5-leg option naturally extends a 4-leg one)
        if any(ks == s for _, s in sets) or any(len(ks & s) > ov for k2, s in sets if k2 == c.k):
            continue
        picked.append(c)
        sets.append((c.k, ks))
        if len(picked) >= top:
            break
    picked.sort(key=lambda p: -p.score)
    return picked


# ── Explanations ─────────────────────────────────────────────────────────────

def explain_leg(l: Leg) -> Dict:
    return {'leg': l.pick, 'game': l.matchup, 'league': l.league, 'type': l.kind, 'probability': l.p,
            'price': l.price, 'live': l.live, 'sources': [vars(s) for s in l.sources], 'notes': l.notes}


def explain_parlay(p: Parlay) -> Dict:
    prod = ' × '.join(f'{l.p:.0%}' for l in p.legs)
    kinds = sorted({s.name for l in p.legs for s in l.sources})
    return {
        'formula': f'{prod} = {p.p:.1%}',
        'fair_odds': f'{p.fair_decimal:.1f}x (fair American {prob_to_american(p.p):+d})' if prob_to_american(p.p) else '',
        'market': None if p.market_decimal is None else
        f'sportsbook parlay pays about {p.market_decimal:.1f}x; expected value {p.ev:+.1%} per $1 if our probabilities are right',
        'sources': kinds,
        'assumptions': [
            'Each leg is from a different game, so outcomes are treated as independent.',
            'Leg probabilities blend the sources shown (market-anchored where a price exists).',
            'Live legs are propositions on the pre-game line; sportsbooks reprice live and will not offer these terms.',
            'Player legs come from recent box scores only and carry no sportsbook price.',
            'Injury news after the last data refresh is not reflected.'],
    }

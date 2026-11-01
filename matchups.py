"""Matchups page: upcoming games with an expected outcome, a moneyline
comparison across sources, and side-by-side team/player breakdowns.

The model is deliberately simple and transparent:
  rating   = recent-weighted average scoring margin, shrunk toward 0 for
             small samples
  margin   = home rating − away rating + home advantage − injury penalty
  win prob = Normal CDF(margin / sport-specific σ)
Injury penalty uses stored roster injuries × each player's share of team
production from stored box scores.
"""
import json
import math
import time
from concurrent.futures import ThreadPoolExecutor
from typing import Any, Callable, Dict, Optional

import pandas as pd
import streamlit as st

from fanduel_odds import ODDS_SPORT_MAP, _api_key, _fmt_price, american_to_prob, \
    events_to_df, fetch_fanduel_odds
from odds_page import KALSHI_SERIES, attach_fanduel, attach_kalshi, fetch_espn_lines, \
    fetch_kalshi_markets

# Home advantage (points/goals/runs) and game-to-game margin std-dev by sport.
_HFA = {'football/nfl': 1.5, 'football/college-football': 2.5, 'basketball/nba': 2.5,
        'basketball/wnba': 2.5, 'basketball/mens-college-basketball': 3.0,
        'basketball/womens-college-basketball': 3.0, 'hockey/nhl': 0.15, 'baseball/mlb': 0.15}
_SIGMA = {'football': 13.5, 'basketball': 12.0, 'hockey': 2.4, 'baseball': 4.2, 'soccer': 1.6}
_INJ_WEIGHT = {'out': 1.0, 'injured reserve': 1.0, 'suspension': 1.0, 'doubtful': 0.75,
               'questionable': 0.3, 'day-to-day': 0.25}
# Stat that best represents a player's offensive production, per sport.
_PRODUCTION = {'football': ['YDS', 'TD'], 'basketball': ['PTS'], 'hockey': ['G', 'A'],
               'baseball': ['H', 'R', 'RBI']}
# Primary stat to rank players by within each box-score category.
_RANK_STATS = ['PTS', 'YDS', 'G', 'H', 'K', 'TOT', 'SV']
# Show the most-read box-score categories first.
_CAT_ORDER = ['passing', 'rushing', 'receiving', 'defensive', 'stats', 'batting', 'pitching',
              'forwards', 'defenses', 'goalies', 'interceptions', 'kicking', 'punting']


def _ok(v) -> bool:
    return v is not None and not pd.isna(v)


def _norm_cdf(x: float) -> float:
    return 0.5 * (1 + math.erf(x / math.sqrt(2)))


def prob_to_american(p: Optional[float]) -> Optional[float]:
    if p is None or p <= 0 or p >= 1:
        return None
    return round(-100 * p / (1 - p)) if p >= 0.5 else round(100 * (1 - p) / p)


# ── Team form ────────────────────────────────────────────────

def team_form(db: Any, worker: Any, cat: str, spt: str, team_id: str, season: int) -> Dict:
    """Season form from the team schedule; falls back to last season early on."""
    for yr in (season, season - 1):
        sched = db.get_team_schedule_games(cat, spt, team_id, yr)
        if sched.empty:
            worker.fetch_team_schedule(cat, spt, team_id, yr)
            sched = db.get_team_schedule_games(cat, spt, team_id, yr)
        done = sched[sched['completed']] if not sched.empty else sched
        if len(done) >= 2:
            break
    if done.empty:
        return {'n': 0}
    n = len(done)
    margin = done['diff'].mean()
    last5 = done['diff'].tail(5).mean()
    rating = (0.6 * margin + 0.4 * last5) * n / (n + 3)  # shrink small samples
    return {
        'n': n, 'season': yr, 'wins': int(done['won'].sum()), 'losses': int(n - done['won'].sum()),
        'pf': done['my_score'].mean(), 'pa': done['opp_score'].mean(),
        'margin': margin, 'last5': last5, 'rating': rating,
        'streak': ''.join('W' if w else 'L' for w in done['won'].tail(5)),
    }


# ── Player data ──────────────────────────────────────────────

def _player_table(db: Any, sport_key: str, team_abbr: str) -> pd.DataFrame:
    """Long table: player, category, stat, per-game average, games."""
    raw = db.get_team_players_stats(sport_key, team_abbr)
    if raw.empty:
        return pd.DataFrame()
    rows = []
    for r in raw.itertuples():
        try:
            labels, vals = json.loads(r.stat_labels), json.loads(r.stat_values)
        except Exception:
            continue
        for lab, v in zip(labels, vals):
            try:
                num = float(str(v).replace(',', ''))
            except ValueError:
                continue
            rows.append((r.player_name, r.category or 'stats', lab, num, r.event_id))
    df = pd.DataFrame(rows, columns=['player', 'category', 'stat', 'value', 'game_date'])
    if df.empty:
        return df
    g = df.groupby(['player', 'category', 'stat'])
    out = g['value'].mean().rename('avg').reset_index()
    out['games'] = g['game_date'].nunique().values
    return out


def injury_penalty(db: Any, ep: str, team_id: str, team_abbr: str, pf: float) -> Dict:
    """Points lost to injuries: injured players' share of production × team scoring."""
    roster = db.get_team_roster_players(ep, team_id)
    if roster.empty or not pf:
        return {'penalty': 0.0, 'players': []}
    inj = roster[roster['injury_status'].fillna('') != '']
    if inj.empty:
        return {'penalty': 0.0, 'players': []}
    stats = _player_table(db, ep, team_abbr)
    prod_stats = _PRODUCTION.get(ep.split('/')[0], [])
    share: Dict[str, float] = {}
    if not stats.empty and prod_stats:
        prod = stats[stats['stat'].isin(prod_stats) & (stats['stat'] != 'TD')]
        by_player = prod.groupby('player')['avg'].sum()
        total = by_player.sum()
        if total > 0:
            share = (by_player / total).to_dict()
    pen, players = 0.0, []
    for r in inj.itertuples():
        w = _INJ_WEIGHT.get(str(r.injury_status).lower(), 0.0)
        s = share.get(r.display_name, 0.0)
        if w and s:
            # Replacements recover about half of a missing player's output.
            pen += 0.5 * w * s * pf
        players.append({'name': r.display_name, 'pos': r.position,
                        'status': r.injury_status, 'share': s})
    players.sort(key=lambda p: -p['share'])
    return {'penalty': pen, 'players': players}


# Per-league shrink factor for the rating difference, fitted by the backtest
# (raw ratings are overconfident). Loaded from config by the app each run.
CALIBRATION: Dict[str, float] = {}


# Weight on the model when blending with the market (logit space), fitted by
# the backtest. 0 = trust the market entirely, 1 = model only.
BLEND: Dict[str, float] = {}


def _logit(p: float) -> float:
    p = min(1 - 1e-4, max(1e-4, p))
    return math.log(p / (1 - p))


def blended_prob(ep: str, p_model: Optional[float], p_market: Optional[float]) -> Optional[float]:
    """Market-anchored probability: the market line, nudged toward the model by
    the backtest-fitted weight. Falls back to the model when there's no line."""
    if p_model is None:
        return p_market
    if p_market is None:
        return p_model
    w = BLEND.get(ep, 0.3)
    return 1 / (1 + math.exp(-(_logit(p_market) + w * (_logit(p_model) - _logit(p_market)))))


def predict(ep: str, home: Dict, away: Dict, pen_h: float = 0.0, pen_a: float = 0.0,
            calibrate: bool = True) -> Optional[Dict]:
    if not home.get('n') or not away.get('n'):
        return None
    sigma = _SIGMA.get(ep.split('/')[0], 12.0)
    k = CALIBRATION.get(ep, 1.0) if calibrate else 1.0
    margin = k * (home['rating'] - away['rating']) + _HFA.get(ep, 1.0) - pen_h + pen_a
    total = (home['pf'] + away['pa']) / 2 + (away['pf'] + home['pa']) / 2 - pen_h - pen_a
    p_home = _norm_cdf(margin / sigma)
    return {'margin': margin, 'p_home': p_home,
            'home_pts': total / 2 + margin / 2, 'away_pts': total / 2 - margin / 2}


# ── Slate: every upcoming game with markets + model ─────────

_SLATE_CACHE: Dict[tuple, tuple] = {}
_SLATE_TTL = 300  # seconds; lines move, so keep it short


def build_slate(db: Any, worker: Any, ep: str, season: int, include_fd: bool = True):
    """Upcoming games for a league with ESPN/FanDuel/Kalshi markets attached and
    model columns: pred (dict or None), form_home, form_away. Returns (df, err).
    Cached for 5 minutes and shared by Matchups and Best Bets."""
    key = (ep, season, include_fd)
    hit = _SLATE_CACHE.get(key)
    if hit and time.time() - hit[0] < _SLATE_TTL:
        return hit[1].copy(), hit[2]
    games, err = _build_slate(db, worker, ep, season, include_fd)
    _SLATE_CACHE[key] = (time.time(), games, err)
    return games.copy(), err


def _build_slate(db: Any, worker: Any, ep: str, season: int, include_fd: bool):
    cat, spt = ep.split('/')
    games, err = fetch_espn_lines(ep)
    if not games.empty:
        games = games[games['status'] == 'pre'].reset_index(drop=True)
    if games.empty:
        return games, err
    if ep in KALSHI_SERIES:
        games = attach_kalshi(games, fetch_kalshi_markets(KALSHI_SERIES[ep])[0])
    else:
        games['kalshi_home'] = None
    fd = pd.DataFrame()
    if include_fd and _api_key() and ep in ODDS_SPORT_MAP:
        fd = events_to_df(fetch_fanduel_odds(ODDS_SPORT_MAP[ep], _api_key())[0])
    games = attach_fanduel(games, fd)

    team_ids = sorted(set(games['home_id']) | set(games['away_id']))
    with ThreadPoolExecutor(max_workers=4) as pool:
        forms = dict(zip(team_ids, pool.map(
            lambda t: team_form(db, worker, cat, spt, t, season), team_ids)))
    preds, fh_l, fa_l = [], [], []
    for g in games.itertuples():
        fh, fa = forms.get(g.home_id, {'n': 0}), forms.get(g.away_id, {'n': 0})
        ph = injury_penalty(db, ep, g.home_id, g.home_abbr, fh.get('pf', 0))['penalty']
        pa = injury_penalty(db, ep, g.away_id, g.away_abbr, fa.get('pf', 0))['penalty']
        pred = predict(ep, fh, fa, ph, pa)
        if pred:
            pred.update(pen_home=ph, pen_away=pa)
            from tracker import log_prediction  # lock in the pre-game number for grading
            log_prediction(db.db_name, str(g.espn_id), ep, 'pre', pred)
        preds.append(pred)
        fh_l.append(fh)
        fa_l.append(fa)
    games['pred'], games['form_home'], games['form_away'] = preds, fh_l, fa_l
    return games, err


def league_avg_allowed(forms) -> Optional[float]:
    vals = [f['pa'] for f in forms if f.get('n')]
    return sum(vals) / len(vals) if vals else None


# Stats worth projecting per box-score category (others are noise).
_PROJ_STATS = {
    'passing': ['YDS', 'TD', 'INT'], 'rushing': ['CAR', 'YDS', 'TD'],
    'receiving': ['REC', 'YDS', 'TD', 'TGTS'], 'defensive': ['TOT', 'SACKS'],
    'stats': ['PTS', 'REB', 'AST', '3PT', 'STL', 'BLK'],
    'forwards': ['G', 'A', 'S', 'SOG'], 'defenses': ['G', 'A', 'BS', 'HT'],
    'goalies': ['SV', 'GA'], 'batting': ['H', 'R', 'HR', 'RBI'], 'pitching': ['IP', 'K', 'ER'],
}


def player_projections(db: Any, ep: str, team_abbr: str, opp_factor: float = 1.0,
                       top: int = 5) -> Dict[str, pd.DataFrame]:
    """Projected stat line per player for the next game, by category.

    projection = (0.6 x last-3 average + 0.4 x last-8 average) x opponent factor,
    where opponent factor = opponent's points allowed / league average (capped
    0.8-1.2). Only players who appeared in at least 2 of the team's last 8 games."""
    raw = db.get_team_players_stats(ep, team_abbr)
    if raw.empty:
        return {}
    rows = []
    for r in raw.itertuples():
        keep = _PROJ_STATS.get((r.category or 'stats').lower())
        if not keep:
            continue
        try:
            labels, vals = json.loads(r.stat_labels), json.loads(r.stat_values)
        except Exception:
            continue
        for lab, v in zip(labels, vals):
            if lab not in keep:
                continue
            try:
                num = float(str(v).split('-')[0].split('/')[0].replace(',', ''))
            except ValueError:
                continue
            rows.append((r.player_name, (r.category or 'stats').lower(), lab, num,
                         r.event_id, r.game_date or ''))
    df = pd.DataFrame(rows, columns=['player', 'category', 'stat', 'value', 'event', 'date'])
    if df.empty:
        return {}
    recent = (df[['event', 'date']].drop_duplicates('event')
              .sort_values('date', ascending=False)['event'].head(8).tolist())
    df = df[df['event'].isin(recent)].copy()
    df['rank'] = df['event'].map({e: i for i, e in enumerate(recent)})
    f = min(1.2, max(0.8, opp_factor or 1.0))
    out = {}
    for cat, sub in df.groupby('category'):
        l8 = sub.groupby(['player', 'stat'])['value'].mean()
        l3 = sub[sub['rank'] < 3].groupby(['player', 'stat'])['value'].mean()
        gp = sub.groupby('player')['event'].nunique()
        proj = 0.6 * l3.reindex(l8.index).fillna(l8) + 0.4 * l8
        # Volume stats scale with the matchup; defense/goalie/pitching less so.
        if cat in ('passing', 'rushing', 'receiving', 'stats', 'forwards', 'batting'):
            proj = proj * f
        wide = proj.unstack('stat')
        wide = wide[gp.reindex(wide.index).fillna(0) >= 2]
        if wide.empty:
            continue
        cols = [c for c in _PROJ_STATS[cat] if c in wide.columns]
        wide = wide[cols].sort_values(cols[0], ascending=False).head(top).round(1)
        wide.insert(0, 'GP', gp.reindex(wide.index).astype(int))
        out[cat] = wide
    return out


# ── Rendering ────────────────────────────────────────────────

def _fmt_pts(v: float, ep: str) -> str:
    return f'{v:.1f}' if ep.split('/')[0] in ('hockey', 'baseball', 'soccer') else f'{v:.0f}'


def _ml_table(g, model_p: Optional[float]) -> pd.DataFrame:
    def nv(h, a):
        ph, pa = american_to_prob(h), american_to_prob(a)
        return ph / (ph + pa) if ph and pa else None

    rows = []
    if model_p is not None:
        rows.append(('📐 Model (market-anchored)', prob_to_american(model_p), prob_to_american(1 - model_p), model_p))
    if _ok(g.fd_home_ml):
        rows.append(('FanDuel', g.fd_home_ml, g.fd_away_ml, nv(g.fd_home_ml, g.fd_away_ml)))
    if _ok(g.espn_home_ml):
        rows.append((g.espn_book or 'ESPN book', g.espn_home_ml, g.espn_away_ml,
                     nv(g.espn_home_ml, g.espn_away_ml)))
    if _ok(g.kalshi_home):
        k = float(g.kalshi_home)
        rows.append(('Kalshi', prob_to_american(k), prob_to_american(1 - k), k))
    df = pd.DataFrame(rows, columns=['Source', g.home_abbr, g.away_abbr, 'home_p'])
    if df.empty:
        return df
    df[f'{g.home_abbr} win %'] = df['home_p'].map(lambda p: f'{p:.0%}' if p is not None else '—')
    if model_p is not None:
        df['Model edge'] = df['home_p'].map(
            lambda p: '—' if p is None else f'{model_p - p:+.1%} {g.home_abbr}')
        df.loc[0, 'Model edge'] = ''
    for c in (g.home_abbr, g.away_abbr):
        df[c] = df[c].map(_fmt_price)
    return df.drop(columns='home_p')


def _compare_teams(db, worker, ep, season, ensure_box, goto,
                   h_id, h_abbr, h_name, a_id, a_abbr, a_name) -> None:
    cat, spt = ep.split('/')
    for tid, abbr in ((h_id, h_abbr), (a_id, a_abbr)):
        if db.get_team_roster_players(ep, tid).empty:
            with st.spinner(f'Loading {abbr} roster…'):
                worker.fetch_team_roster(cat, spt, tid, abbr)
        ensure_box(db, worker, cat, spt, tid, season, limit=6)

    fh = team_form(db, worker, cat, spt, h_id, season)
    fa = team_form(db, worker, cat, spt, a_id, season)
    ih = injury_penalty(db, ep, h_id, h_abbr, fh.get('pf', 0))
    ia = injury_penalty(db, ep, a_id, a_abbr, fa.get('pf', 0))

    def rec(f):
        return f"{f['wins']}-{f['losses']}" if f.get('n') else '—'

    def num(f, k):
        return f'{f[k]:+.1f}' if k in ('margin', 'last5') and f.get('n') else (
            f'{f[k]:.1f}' if f.get('n') else '—')

    st.markdown(f'##### {a_name} vs {h_name}')
    st.dataframe(pd.DataFrame({
        'Stat': ['Record', 'Scored / game', 'Allowed / game', 'Avg margin', 'Last 5 margin',
                 'Last 5', 'Injured players'],
        a_abbr: [rec(fa), num(fa, 'pf'), num(fa, 'pa'), num(fa, 'margin'), num(fa, 'last5'),
                 fa.get('streak', '—'), str(len(ia['players']))],
        h_abbr: [rec(fh), num(fh, 'pf'), num(fh, 'pa'), num(fh, 'margin'), num(fh, 'last5'),
                 fh.get('streak', '—'), str(len(ih['players']))],
    }), hide_index=True, use_container_width=True)

    st.markdown('**Player breakdown** · per-game averages, recent games')
    th, ta = _player_table(db, ep, h_abbr), _player_table(db, ep, a_abbr)
    cats = sorted((set(th['category']) if not th.empty else set())
                  | (set(ta['category']) if not ta.empty else set()),
                  key=lambda c: (_CAT_ORDER.index(c) if c in _CAT_ORDER else 99, c))
    if not cats:
        st.caption('No box scores stored for these teams yet.')
    else:
        tabs = st.tabs([c.title() for c in cats])
        for tab, c in zip(tabs, cats):
            with tab:
                cols = st.columns(2)
                for col, abbr, t in ((cols[0], a_abbr, ta), (cols[1], h_abbr, th)):
                    with col:
                        st.markdown(f'**{abbr}**')
                        sub = t[t['category'] == c] if not t.empty else t
                        if sub.empty:
                            st.caption('—')
                            continue
                        wide = sub.pivot_table(index='player', columns='stat', values='avg')
                        rank = next((s for s in _RANK_STATS if s in wide.columns), wide.columns[0])
                        keep = [s for s in [rank] + [x for x in wide.columns if x != rank]][:5]
                        top = wide.sort_values(rank, ascending=False)[keep].head(6).round(1)
                        st.dataframe(top, use_container_width=True)

    # Projected stat lines vs this opponent.
    lg_pa = league_avg_allowed([fh, fa])
    pj_a = player_projections(db, ep, a_abbr, (fh.get('pa', 0) / lg_pa) if lg_pa else 1.0)
    pj_h = player_projections(db, ep, h_abbr, (fa.get('pa', 0) / lg_pa) if lg_pa else 1.0)
    pcats = ([c for c in _CAT_ORDER if c in pj_a or c in pj_h]
             + sorted((set(pj_a) | set(pj_h)) - set(_CAT_ORDER)))
    if pcats:
        st.markdown('**🔮 Projected player lines** · recent form x opponent defense')
        ptabs = st.tabs([c.title() for c in pcats])
        for tab, c in zip(ptabs, pcats):
            with tab:
                cols = st.columns(2)
                for col, abbr, pj in ((cols[0], a_abbr, pj_a), (cols[1], h_abbr, pj_h)):
                    with col:
                        st.markdown(f'**{abbr}**')
                        if c in pj:
                            st.dataframe(pj[c], use_container_width=True)
                        else:
                            st.caption('—')

    # PrizePicks lines vs our projections (fetched only when asked: costs credits).
    st.markdown('**🟣 PrizePicks props**')
    from prizepicks_props import render_prizepicks
    render_prizepicks(db, ep, h_name, a_name,
                      [(a_abbr, (fh.get('pa', 0) / lg_pa) if lg_pa else 1.0),
                       (h_abbr, (fa.get('pa', 0) / lg_pa) if lg_pa else 1.0)],
                      player_projections, key_suffix=f'_{a_id}_{h_id}')

    inj_rows = [{'Team': abbr, 'Player': p['name'], 'Pos': p['pos'], 'Status': p['status'],
                 'Share of production': f"{p['share']:.0%}" if p['share'] else '—'}
                for abbr, inj in ((a_abbr, ia), (h_abbr, ih)) for p in inj['players'][:8]]
    if inj_rows:
        st.markdown('**Injury report**')
        st.dataframe(pd.DataFrame(inj_rows), hide_index=True, use_container_width=True)

    b1, b2 = st.columns(2)
    b1.button(f'👤 {a_abbr} players', key=f'mu_go_a_{a_id}_{h_id}', use_container_width=True,
              on_click=goto, args=('👤 Players',), kwargs={'pt_ep': ep, f'pt_team_{ep}': a_id})
    b2.button(f'👤 {h_abbr} players', key=f'mu_go_h_{a_id}_{h_id}', use_container_width=True,
              on_click=goto, args=('👤 Players',), kwargs={'pt_ep': ep, f'pt_team_{ep}': h_id})


def render_matchups_page(db: Any, worker: Any, season_for: Callable[[str], int],
                         ensure_box: Callable, goto: Callable) -> None:
    st.markdown('## ⚔️ Matchups')
    st.caption('Upcoming games with an expected outcome from team form and player '
               'availability, plus moneylines side by side. Tap **Compare** for the full breakdown.')

    active = json.loads(db.get_config('active_endpoints', '[]'))
    leagues = [k for k in active if k in _HFA] or sorted(_HFA)
    ep = st.selectbox('League', leagues, key='mu_league')
    cat, spt = ep.split('/')
    season = season_for(cat)

    with st.spinner('Crunching team form…'):
        games, err = build_slate(db, worker, ep, season,
                                 include_fd=st.session_state.get('fd_on', False))
    if err:
        st.error(f'ESPN: {err}')
    if games.empty:
        st.info('No upcoming games on the schedule for this league right now.')
        return

    from sporting_shared import viewer_tz
    tz = viewer_tz()
    sel = st.session_state.get('mu_open')
    for g in games.itertuples():
        fh, fa, pred = g.form_home, g.form_away, g.pred
        ph, pa = (pred or {}).get('pen_home', 0), (pred or {}).get('pen_away', 0)
        start = pd.to_datetime(g.date).tz_convert(tz).strftime('%a %b %d · %I:%M %p')

        with st.container(border=True):
            c1, c2 = st.columns([3, 1])
            c1.markdown(f'**{g.away_team} @ {g.home_team}**  \n'
                        f'<span style="color:#888;font-size:12px">{start}</span>',
                        unsafe_allow_html=True)
            open_now = sel == g.espn_id
            c2.button('Hide' if open_now else '⚔️ Compare', key=f'mu_btn_{g.espn_id}',
                      use_container_width=True,
                      on_click=lambda e=g.espn_id, o=open_now: st.session_state.update(
                          mu_open=None if o else e))

            if pred:
                fav, p = (g.home_abbr, pred['p_home']) if pred['p_home'] >= 0.5 else \
                    (g.away_abbr, 1 - pred['p_home'])
                st.markdown(
                    f"**Expected:** {g.away_abbr} {_fmt_pts(pred['away_pts'], ep)} – "
                    f"{_fmt_pts(pred['home_pts'], ep)} {g.home_abbr} · "
                    f"**{fav} {p:.0%}** to win")
                st.progress(pred['p_home'], text=f"{g.away_abbr} ◀ win probability ▶ {g.home_abbr}")
                bits = [f"{g.away_abbr} {fa['wins']}-{fa['losses']} ({fa['streak']})",
                        f"{g.home_abbr} {fh['wins']}-{fh['losses']} ({fh['streak']})"]
                if ph or pa:
                    bits.append(f'injury adj. {g.home_abbr} −{ph:.1f}, {g.away_abbr} −{pa:.1f}')
                st.caption(' · '.join(bits))
            else:
                st.caption('Not enough completed games yet to project this one.')

            # Market-anchored: blend the model into the best available line.
            _mkt = None
            for _h, _a in ((g.fd_home_ml, g.fd_away_ml), (g.espn_home_ml, g.espn_away_ml)):
                _ph, _pa = american_to_prob(_h), american_to_prob(_a)
                if _ph and _pa:
                    _mkt = _ph / (_ph + _pa)
                    break
            if _mkt is None and _ok(g.kalshi_home):
                _mkt = float(g.kalshi_home)
            ml = _ml_table(g, blended_prob(ep, pred['p_home'], _mkt) if pred else None)
            if not ml.empty:
                st.dataframe(ml, hide_index=True, use_container_width=True)

            if open_now:
                _compare_teams(db, worker, ep, season, ensure_box, goto,
                               g.home_id, g.home_abbr, g.home_team,
                               g.away_id, g.away_abbr, g.away_team)

    # Free-form comparison of any two teams in the league.
    st.divider()
    with st.expander('🆚 Compare any two teams'):
        teams = db.get_teams_df(ep)
        if teams.empty:
            st.caption('No teams stored for this league yet.')
            return
        opts = {str(r.team_id): f'{r.team_name} ({r.team_abbr})' for r in teams.itertuples()}
        ids = list(opts)
        x1, x2 = st.columns(2)
        a = x1.selectbox('Team A', ids, format_func=opts.get, key='mu_cmp_a')
        b = x2.selectbox('Team B', ids, index=min(1, len(ids) - 1), format_func=opts.get,
                         key='mu_cmp_b')
        if a == b:
            st.caption('Pick two different teams.')
        elif st.button('Compare', key='mu_cmp_go', type='primary'):
            st.session_state['mu_cmp_pair'] = (a, b)
        pair = st.session_state.get('mu_cmp_pair')
        if pair and pair == (a, b):
            ra = teams[teams['team_id'].astype(str) == a].iloc[0]
            rb = teams[teams['team_id'].astype(str) == b].iloc[0]
            _compare_teams(db, worker, ep, season, ensure_box, goto,
                           b, rb.team_abbr, rb.team_name, a, ra.team_abbr, ra.team_name)

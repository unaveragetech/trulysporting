"""Player insights: rich per-game data for ANY player straight from ESPN's
athlete game log and splits (not limited to games stored locally), turned into
trends, consistency, splits, opponent history, multi-season comparison and
plain-English insights.
"""
import re
from typing import List, Optional

import pandas as pd
import plotly.graph_objects as go
import requests
import streamlit as st

GAMELOG = "https://site.web.api.espn.com/apis/common/v3/sports/{ep}/athletes/{pid}/gamelog"
SPLITS = "https://site.web.api.espn.com/apis/common/v3/sports/{ep}/athletes/{pid}/splits"

_session = requests.Session()
_session.headers.update({'User-Agent': 'Mozilla/5.0 (TrulySporting Players)'})

# Headline stats per sport, in priority order (ESPN `names`).
KEY_STATS = {
    'football': ['passingYards', 'passingTouchdowns', 'rushingYards', 'rushingTouchdowns',
                 'receptions', 'receivingYards', 'receivingTouchdowns', 'totalTackles', 'sacks',
                 'interceptions', 'fieldGoalsMade'],
    'basketball': ['points', 'totalRebounds', 'rebounds', 'assists', 'threePointFieldGoalsMade',
                   'steals', 'blocks', 'minutes'],
    'hockey': ['goals', 'assists', 'points', 'shotsTotal', 'plusMinus', 'saves', 'savePct'],
    'baseball': ['hits', 'homeRuns', 'RBIs', 'runs', 'strikeouts', 'walks', 'innings',
                 'earnedRuns'],
    'soccer': ['totalGoals', 'goalAssists', 'totalShots', 'shotsOnTarget', 'saves'],
}


def _label(name: str) -> str:
    """'passingYards' -> 'Passing Yards'."""
    return re.sub(r'(?<!^)(?=[A-Z])', ' ', name).replace('R B Is', 'RBIs').title()


def _num(v) -> Optional[float]:
    s = str(v).replace(',', '').strip()
    if '/' in s or (s.count('-') == 1 and not s.startswith('-')):
        s = re.split(r'[/-]', s)[0]  # "5-11" made-attempted -> made
    try:
        return float(s.rstrip('%'))
    except ValueError:
        return None


@st.cache_data(ttl=1800, show_spinner=False)
def fetch_gamelog(ep: str, pid: str, season: Optional[int] = None) -> pd.DataFrame:
    """One row per game: date, opponent, home/away, result, score + every stat."""
    params = {'season': season} if season else {}
    try:
        r = _session.get(GAMELOG.format(ep=ep, pid=pid), params=params, timeout=15)
        r.raise_for_status()
        data = r.json()
    except Exception:
        return pd.DataFrame()
    names = data.get('names') or []
    events = data.get('events') or {}
    rows = []
    for stype in data.get('seasonTypes') or []:
        kind = 'Postseason' if 'post' in stype.get('displayName', '').lower() else (
            'Preseason' if 'pre' in stype.get('displayName', '').lower() else 'Regular')
        for cat in stype.get('categories') or []:
            for e in cat.get('events') or []:
                meta = events.get(e.get('eventId'), {})
                row = {'event_id': e.get('eventId'), 'type': kind,
                       'date': (meta.get('gameDate') or '')[:10],
                       'opp': (meta.get('opponent') or {}).get('abbreviation', ''),
                       'home': meta.get('atVs') != '@',
                       'result': meta.get('gameResult', ''), 'score': meta.get('score', '')}
                for n, v in zip(names, e.get('stats') or []):
                    row[n] = _num(v)
                rows.append(row)
    df = pd.DataFrame(rows)
    if df.empty:
        return df
    return df.drop_duplicates('event_id').sort_values('date').reset_index(drop=True)


@st.cache_data(ttl=3600, show_spinner=False)
def fetch_splits(ep: str, pid: str, season: Optional[int] = None) -> pd.DataFrame:
    params = {'season': season} if season else {}
    try:
        r = _session.get(SPLITS.format(ep=ep, pid=pid), params=params, timeout=15)
        r.raise_for_status()
        data = r.json()
    except Exception:
        return pd.DataFrame()
    labels = data.get('labels') or []
    rows = []
    for sc in data.get('splitCategories') or []:
        for sp in sc.get('splits') or []:
            rows.append([sc.get('displayName', ''), sp.get('displayName', '')]
                        + (sp.get('stats') or [])[:len(labels)])
    return pd.DataFrame(rows, columns=['Group', 'Split'] + labels) if rows else pd.DataFrame()


def key_stats(df: pd.DataFrame, cat: str, n: int = 4) -> List[str]:
    """The player's headline stats: sport priority list, keeping ones they actually record."""
    have = [c for c in KEY_STATS.get(cat, []) if c in df.columns and df[c].fillna(0).abs().sum() > 0]
    if not have:
        skip = {'event_id', 'type', 'date', 'opp', 'home', 'result', 'score'}
        have = [c for c in df.columns if c not in skip and df[c].fillna(0).abs().sum() > 0]
    return have[:n]


def insights(df: pd.DataFrame, stats: List[str]) -> List[str]:
    """Plain-English observations from the game log."""
    out = []
    if len(df) < 3:
        return out
    for s in stats[:3]:
        col = df[s].dropna()
        if len(col) < 3:
            continue
        avg, last5 = col.mean(), col.tail(5).mean()
        name = _label(s).lower()
        if avg < 0.5:  # rare-event stats (sacks, TDs for a lineman) are too noisy
            continue
        if abs(last5 - avg) / avg >= 0.15 and abs(last5 - avg) >= 0.5:
            word = '🔥 Trending up' if last5 > avg else '🧊 Cooling off'
            out.append(f"{word}: {last5:.1f} {name} over the last {min(5, len(col))} games vs "
                       f"{avg:.1f} season average ({(last5 - avg) / avg:+.0%}).")
        line = round(avg * 2) / 2
        if line > 0:
            hit = (col >= line).mean()
            out.append(f"🎯 Reached {line:g}+ {name} in {int((col >= line).sum())} of {len(col)} "
                       f"games ({hit:.0%}).")
        home, away = df[df['home']][s].dropna(), df[~df['home']][s].dropna()
        if len(home) >= 2 and len(away) >= 2:
            diff = home.mean() - away.mean()
            if abs(diff) / max(home.mean(), away.mean()) >= 0.15 and abs(diff) >= 0.5:
                out.append(f"🏟 {'Better at home' if diff > 0 else 'Better on the road'}: "
                           f"{home.mean():.1f} home vs {away.mean():.1f} away {name}.")
        w, l = df[df['result'] == 'W'][s].dropna(), df[df['result'] == 'L'][s].dropna()
        if len(w) >= 2 and len(l) >= 2:
            if (abs(w.mean() - l.mean()) / max(w.mean(), l.mean(), 1e-9) >= 0.2
                    and abs(w.mean() - l.mean()) >= 0.5):
                out.append(f"🏆 {w.mean():.1f} {name} in wins vs {l.mean():.1f} in losses.")
        cv = col.std() / avg if avg else 0
        if avg and cv < 0.25:
            out.append(f"📏 Very consistent {name} (typical game {col.quantile(.25):.0f}–"
                       f"{col.quantile(.75):.0f}).")
        elif avg >= 1 and cv > 0.6:
            out.append(f"🎢 Boom-or-bust {name}: ranges {col.min():.0f}–{col.max():.0f}.")
    return out[:8]


def _trend_chart(df: pd.DataFrame, s: str) -> go.Figure:
    colors = ['#16a34a' if r == 'W' else '#dc2626' if r == 'L' else '#94a3b8' for r in df['result']]
    x = [f"{d[5:]} {'vs' if h else '@'} {o}" for d, h, o in zip(df['date'], df['home'], df['opp'])]
    fig = go.Figure()
    fig.add_bar(x=x, y=df[s], marker_color=colors, name=_label(s),
                hovertemplate='%{x}<br>%{y}<extra></extra>')
    fig.add_scatter(x=x, y=df[s].rolling(5, min_periods=1).mean(), mode='lines',
                    line=dict(color='#2563eb', width=3), name='5-game average')
    fig.add_hline(y=df[s].mean(), line_dash='dot', line_color='#64748b',
                  annotation_text='season avg', annotation_position='top left')
    fig.update_layout(height=300, margin=dict(l=10, r=10, t=10, b=10), showlegend=False,
                      xaxis=dict(showgrid=False, tickangle=-45), yaxis_title=_label(s))
    return fig


def render_player_insights(ep: str, pid: str, season: int, season_label, player_name: str) -> None:
    cat = ep.split('/')[0]
    with st.spinner(f'Loading {player_name}\'s game log from ESPN…'):
        df = fetch_gamelog(ep, pid, season)
    if df.empty:
        st.info(f"ESPN has no game log for {player_name} in {season_label(season)}.")
        return
    reg = df[df['type'] != 'Preseason']
    if not reg.empty:
        df = reg
    stats = key_stats(df, cat)
    if not stats:
        st.info('No stats recorded in these games.')
        return

    wins = (df['result'] == 'W').sum()
    st.caption(f"{len(df)} games · team {wins}-{(df['result'] == 'L').sum()} with "
               f"{player_name} · source: ESPN game log")

    # Season vs last-5 cards
    cols = st.columns(len(stats))
    for col, s in zip(cols, stats):
        avg, last5 = df[s].mean(), df[s].tail(5).mean()
        col.metric(_label(s), f'{avg:.1f}', f'{last5 - avg:+.1f} last 5',
                   help=f'Season per-game average; delta = last 5 games vs season. '
                        f'Best game: {df[s].max():g}')

    tips = insights(df, stats)
    if tips:
        st.markdown('##### 💡 Insights')
        for t in tips:
            st.markdown(f'- {t}')

    st.markdown('##### 📈 Game by game')
    pick = st.segmented_control('Stat', stats, format_func=_label, default=stats[0],
                                key=f'pi_stat_{pid}', label_visibility='collapsed') or stats[0]
    st.plotly_chart(_trend_chart(df, pick), use_container_width=True, key=f'pi_chart_{pid}')
    st.caption('Bars: green = win, red = loss · blue line = 5-game average')

    c1, c2 = st.columns(2)
    with c1:
        st.markdown('##### 🏟 Splits')
        rows = []
        for nm, mask in (('Home', df['home']), ('Away', ~df['home']),
                         ('Wins', df['result'] == 'W'), ('Losses', df['result'] == 'L'),
                         ('Last 5', df.index.isin(df.tail(5).index))):
            sub = df[mask]
            if len(sub):
                rows.append({'Split': nm, 'G': len(sub),
                             **{_label(s): round(sub[s].mean(), 1) for s in stats}})
        st.dataframe(pd.DataFrame(rows), hide_index=True, use_container_width=True)
    with c2:
        st.markdown('##### 🆚 By opponent')
        opp = df.groupby('opp').agg(G=('event_id', 'size'),
                                    **{_label(s): (s, 'mean') for s in stats}).round(1)
        st.dataframe(opp.sort_values(_label(stats[0]), ascending=False),
                     use_container_width=True)

    st.markdown('##### 🗓 Season over season')
    seasons = []
    for yr in (season, season - 1, season - 2):
        g = df if yr == season else fetch_gamelog(ep, pid, yr)
        if g.empty:
            continue
        g = g[g['type'] != 'Preseason']
        row = {'Season': season_label(yr), 'G': len(g)}
        for s in stats:
            row[_label(s)] = round(g[s].mean(), 1) if s in g else None
        seasons.append(row)
    st.dataframe(pd.DataFrame(seasons), hide_index=True, use_container_width=True)

    best = df.loc[df[stats[0]].idxmax()]
    st.caption(f"Best {_label(stats[0]).lower()} game: {best[stats[0]]:g} "
               f"{'vs' if best['home'] else '@'} {best['opp']} on {best['date']} ({best['result']} {best['score']}).")

    with st.expander('📋 Full game log'):
        show = df.drop(columns=['event_id']).rename(columns=lambda c: _label(c) if c[0].islower()
                                                    and c not in ('date', 'opp', 'home', 'result',
                                                                  'score', 'type') else c)
        st.dataframe(show.iloc[::-1], hide_index=True, use_container_width=True)
    sp = fetch_splits(ep, pid, season)
    if not sp.empty:
        with st.expander('🧮 ESPN official splits (month, opponent, situation…)'):
            for grp, sub in sp.groupby('Group', sort=False):
                st.caption(grp)
                st.dataframe(sub.drop(columns='Group'), hide_index=True, use_container_width=True)

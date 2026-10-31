"""Walk-forward backtest of the game model against stored results and ESPN's
closing lines (game_summaries.pickcenter_json).

Every completed game is predicted using only games played *before* it, with
the same rating formula the live app uses (matchups.predict). Injury
adjustments are left out: historical injury reports aren't stored.
"""
import json
import math
import sqlite3
from collections import defaultdict
from typing import Any, Dict, List, Optional

import pandas as pd
import plotly.graph_objects as go
import streamlit as st

from matchups import _HFA, _SIGMA, predict


def _american_profit(price: float) -> float:
    return price if price > 0 else 10000 / -price


def _nv(h: Optional[float], a: Optional[float]):
    def p(x):
        if x is None or x == 0:
            return None
        return 100 / (x + 100) if x > 0 else -x / (-x + 100)
    ph, pa = p(h), p(a)
    return ph / (ph + pa) if ph and pa else None


def _num(v) -> Optional[float]:
    try:
        f = float(v)
        return None if math.isnan(f) else f
    except (TypeError, ValueError):
        return None


def load_games(db_name: str, ep: str) -> pd.DataFrame:
    cat, spt = ep.split('/')
    con = sqlite3.connect(db_name)
    df = pd.read_sql_query(
        """SELECT h.event_id, h.event_date, h.home_team, h.away_team, h.home_abbr, h.away_abbr,
                  h.home_score, h.away_score, s.pickcenter_json
           FROM game_history h
           LEFT JOIN game_summaries s ON s.event_id = h.event_id
           WHERE h.category=? AND h.sport=? AND h.status LIKE '%FINAL%'
           ORDER BY h.event_date, h.id""", con, params=(cat, spt))
    con.close()
    df = df.drop_duplicates('event_id')
    df['home_score'] = pd.to_numeric(df['home_score'], errors='coerce')
    df['away_score'] = pd.to_numeric(df['away_score'], errors='coerce')
    return df.dropna(subset=['home_score', 'away_score'])


def _lines(pc_json) -> Dict:
    try:
        pc = (json.loads(pc_json or '[]') or [{}])[0]
    except Exception:
        pc = {}
    return {'home_line': _num(pc.get('spread')), 'total_line': _num(pc.get('overUnder')),
            'home_ml': _num(pc.get('home_ml')), 'away_ml': _num(pc.get('away_ml')),
            'home_sp_odds': _num(pc.get('home_spread')) or -110.0,
            'away_sp_odds': _num(pc.get('away_spread')) or -110.0,
            'over_odds': _num(pc.get('overOdds')) or -110.0,
            'under_odds': _num(pc.get('underOdds')) or -110.0}


def _form(hist: List[tuple]) -> Dict:
    """Same formula as matchups.team_form, from (margin, pf, pa, won) tuples."""
    n = len(hist)
    if n == 0:
        return {'n': 0}
    margins = [h[0] for h in hist]
    margin = sum(margins) / n
    last5 = sum(margins[-5:]) / len(margins[-5:])
    return {'n': n, 'rating': (0.6 * margin + 0.4 * last5) * n / (n + 3),
            'pf': sum(h[1] for h in hist) / n, 'pa': sum(h[2] for h in hist) / n,
            'margin': margin}


def season_of(ep: str, date: str, bounds) -> int:
    yr = int(date[:4])
    for y in (yr - 1, yr, yr + 1):
        lo, hi = bounds(ep.split('/')[0], y)
        if lo <= date[:10] <= hi:
            return y
    return yr


@st.cache_data(ttl=3600, show_spinner=False)
def run_backtest(db_name: str, ep: str, n_games_key: int, _bounds) -> pd.DataFrame:
    """One row per predicted game. n_games_key busts the cache as data grows."""
    games = load_games(db_name, ep)
    team_hist: Dict[tuple, List[tuple]] = defaultdict(list)  # (team, season) -> games
    rows = []
    for g in games.itertuples():
        season = season_of(ep, g.event_date, _bounds)

        def form(team):
            cur = team_hist[(team, season)]
            return _form(cur if len(cur) >= 2 else team_hist[(team, season - 1)])

        fh, fa = form(g.home_team), form(g.away_team)
        # Raw (uncalibrated) predictions: calibration is fitted from these.
        pred = predict(ep, fh, fa, calibrate=False) if fh.get('n') and fa.get('n') else None
        margin = g.home_score - g.away_score
        if pred:
            rows.append({'event_id': g.event_id, 'date': g.event_date[:10], 'season': season,
                         'game': f'{g.away_abbr} @ {g.home_abbr}',
                         'p_home': pred['p_home'], 'pred_margin': pred['margin'],
                         'pred_total': pred['home_pts'] + pred['away_pts'],
                         'margin': margin, 'total': g.home_score + g.away_score,
                         'home_won': 1.0 if margin > 0 else (0.5 if margin == 0 else 0.0),
                         **_lines(g.pickcenter_json)})
        # Record the result only after predicting (no look-ahead).
        team_hist[(g.home_team, season)].append((margin, g.home_score, g.away_score, margin > 0))
        team_hist[(g.away_team, season)].append((-margin, g.away_score, g.home_score, margin < 0))
    return pd.DataFrame(rows)


def score(df: pd.DataFrame, edge: float) -> Dict:
    out: Dict = {'n': len(df)}
    if df.empty:
        return out
    dec = df[df['home_won'] != 0.5]
    out['accuracy'] = ((dec['p_home'] >= .5) == (dec['home_won'] == 1)).mean()
    out['brier'] = ((df['p_home'] - df['home_won']) ** 2).mean()
    out['home_rate'] = dec['home_won'].mean()
    out['mae_margin'] = (df['pred_margin'] - df['margin']).abs().mean()

    mk = df.dropna(subset=['home_ml', 'away_ml']).copy()
    mk['p_mkt'] = [_nv(h, a) for h, a in zip(mk['home_ml'], mk['away_ml'])]
    mk = mk.dropna(subset=['p_mkt'])
    out['n_market'] = len(mk)
    if len(mk):
        dm = mk[mk['home_won'] != 0.5]
        out['mkt_accuracy'] = ((dm['p_mkt'] >= .5) == (dm['home_won'] == 1)).mean()
        out['mkt_brier'] = ((mk['p_mkt'] - mk['home_won']) ** 2).mean()
        out['model_brier_same'] = ((mk['p_home'] - mk['home_won']) ** 2).mean()

    # Against the spread: bet the side the model prefers vs the closing line.
    sp = df.dropna(subset=['home_line']).copy()
    if len(sp):
        sp['pick_home'] = sp['pred_margin'] + sp['home_line'] > 0
        res = sp['margin'] + sp['home_line']
        sp['win'] = ((res > 0) & sp['pick_home']) | ((res < 0) & ~sp['pick_home'])
        sp['push'] = res == 0
        price = sp['home_sp_odds'].where(sp['pick_home'], sp['away_sp_odds'])
        sp['profit'] = [0 if p else (_american_profit(pr) if w else -100)
                        for w, p, pr in zip(sp['win'], sp['push'], price)]
        graded = sp[~sp['push']]
        out['ats_n'], out['ats_rate'] = len(graded), graded['win'].mean() if len(graded) else None
        out['ats_roi'] = sp['profit'].sum() / (100 * max(1, len(graded)))
        out['mkt_mae_margin'] = (-sp['home_line'] - sp['margin']).abs().mean()
        out['model_mae_same'] = (sp['pred_margin'] - sp['margin']).abs().mean()

    tt = df.dropna(subset=['total_line']).copy()
    if len(tt):
        over = tt['pred_total'] > tt['total_line']
        res = tt['total'] - tt['total_line']
        win = ((res > 0) & over) | ((res < 0) & ~over)
        graded = res != 0
        out['tot_n'], out['tot_rate'] = int(graded.sum()), win[graded].mean() if graded.any() else None

    # Best-bets strategy: flat $100 on any moneyline side with model edge ≥ `edge`.
    bets = []
    for r in mk.itertuples():
        for side, p_mod, p_mkt, price, won in (
                ('home', r.p_home, r.p_mkt, r.home_ml, r.home_won == 1),
                ('away', 1 - r.p_home, 1 - r.p_mkt, r.away_ml, r.home_won == 0)):
            if p_mod - p_mkt >= edge and r.home_won != 0.5:
                bets.append({'date': r.date, 'game': r.game, 'side': side, 'price': price,
                             'edge': p_mod - p_mkt,
                             'profit': _american_profit(price) if won else -100.0})
    b = pd.DataFrame(bets)
    out['bets'] = b
    if len(b):
        out['bet_n'], out['bet_profit'] = len(b), b['profit'].sum()
        out['bet_roi'] = b['profit'].sum() / (100 * len(b))
        out['bet_hit'] = (b['profit'] > 0).mean()
    return out


def apply_shrink(df: pd.DataFrame, ep: str, k: float) -> pd.DataFrame:
    """Re-derive margin/probability with the rating difference scaled by k."""
    hfa = _HFA.get(ep, 1.0)
    sigma = _SIGMA.get(ep.split('/')[0], 12.0)
    out = df.copy()
    out['pred_margin'] = k * (df['pred_margin'] - hfa) + hfa
    out['p_home'] = [0.5 * (1 + math.erf(m / sigma / math.sqrt(2))) for m in out['pred_margin']]
    return out


def fit_shrink(df: pd.DataFrame, ep: str) -> float:
    """Shrink factor (0.2–1.0) that minimises the Brier score over all stored games."""
    if len(df) < 50:
        return 1.0
    grid = [round(0.2 + 0.05 * i, 2) for i in range(17)]
    return min(grid, key=lambda k: ((apply_shrink(df, ep, k)['p_home'] - df['home_won']) ** 2).mean())


def save_summary(db: Any, ep: str, df: pd.DataFrame, edge: float = 0.03) -> Dict:
    """Store the headline backtest numbers so Best Bets can show its track record."""
    s = score(df, edge)
    out = {'games': s.get('n', 0), 'accuracy': s.get('accuracy'),
           'mkt_accuracy': s.get('mkt_accuracy'), 'ats_rate': s.get('ats_rate'),
           'bet_n': s.get('bet_n', 0), 'bet_roi': s.get('bet_roi'), 'edge': edge}
    out = {k: (float(v) if v is not None else None) for k, v in out.items()}
    db.update_config(f'backtest_summary_{ep}', json.dumps(out))
    return out


def calibration(df: pd.DataFrame) -> pd.DataFrame:
    p_fav = df['p_home'].where(df['p_home'] >= .5, 1 - df['p_home'])
    fav_won = df['home_won'].where(df['p_home'] >= .5, 1 - df['home_won'])
    bins = pd.cut(p_fav, [.5, .55, .6, .65, .7, .75, .8, .85, .9, 1.0], include_lowest=True)
    cal = pd.DataFrame({'bin': bins, 'p': p_fav, 'won': fav_won}).groupby('bin', observed=True)
    return cal.agg(predicted=('p', 'mean'), actual=('won', 'mean'), games=('won', 'size')).reset_index()


# ── Page ──────────────────────────────────────────────────────

def _pct(v) -> str:
    return '—' if v is None or (isinstance(v, float) and math.isnan(v)) else f'{v:.1%}'


def render_backtest_page(db: Any, ep: str, label, bounds) -> None:
    st.markdown('## 📊 Model Backtest')
    st.caption(f'{label(ep)} · every stored game predicted using only the games before it, '
               'then graded against the result and ESPN\'s closing lines.')
    if ep not in _HFA:
        st.info('Backtests are available for NFL, college football, NBA, WNBA, college '
                'basketball, NHL and MLB.')
        return
    n_key = len(load_games(db.db_name, ep))
    with st.spinner('Replaying every season…'):
        df = run_backtest(db.db_name, ep, n_key, bounds)
    if df.empty:
        st.info('Not enough completed games stored yet. The data engine fills past seasons '
                'in the background — check back once the header shows "All seasons up to date".')
        return

    raw = df
    k = fit_shrink(raw, ep)
    db.update_config(f'model_shrink_{ep}', str(k))
    df = apply_shrink(raw, ep, k)
    st.info(f"**Auto-calibrated:** the raw ratings were overconfident, so rating "
            f"differences are scaled by **{k:.2f}** for {label(ep)}. Matchups, Live and "
            f"Best Bets now use this. Brier score {((raw['p_home'] - raw['home_won']) ** 2).mean():.4f}"
            f" → {((df['p_home'] - df['home_won']) ** 2).mean():.4f} (lower is better).")

    save_summary(db, ep, df)

    seasons = sorted(df['season'].unique())
    c1, c2 = st.columns([2, 1])
    pick = c1.multiselect('Seasons', seasons, default=seasons, key='bt_seasons',
                          format_func=str)
    edge = c2.slider('Best-bet edge', 0, 15, 3, format='%d%%', key='bt_edge') / 100
    view = df[df['season'].isin(pick)] if pick else df
    s = score(view, edge)

    st.markdown('#### Picking winners')
    m = st.columns(4)
    m[0].metric('Games predicted', f"{s['n']:,}")
    m[1].metric('Model accuracy', _pct(s.get('accuracy')),
                f"vs {_pct(s.get('home_rate'))} always-home", delta_color='off')
    if s.get('n_market'):
        m[2].metric('Market accuracy', _pct(s.get('mkt_accuracy')),
                    f"{s['n_market']:,} games with closing ML", delta_color='off')
        m[3].metric('Brier (lower = better)', f"{s['model_brier_same']:.3f}",
                    f"market {s['mkt_brier']:.3f}", delta_color='off')
    else:
        m[3].metric('Brier (lower = better)', f"{s['brier']:.3f}")

    st.markdown('#### Against the closing line')
    m = st.columns(4)
    if s.get('ats_n'):
        m[0].metric('Against the spread', _pct(s['ats_rate']), f"{s['ats_n']:,} games",
                    delta_color='off')
        m[1].metric('ATS ROI', _pct(s['ats_roi']),
                    help='Flat $100 on the model side at the actual spread price. '
                         'Break-even at −110 is 52.4%.')
        m[2].metric('Margin error (MAE)', f"{s['model_mae_same']:.1f}",
                    f"market {s['mkt_mae_margin']:.1f}", delta_color='off')
    if s.get('tot_n'):
        m[3].metric('Totals (over/under)', _pct(s['tot_rate']), f"{s['tot_n']:,} games",
                    delta_color='off')
    if not s.get('ats_n') and not s.get('tot_n'):
        st.caption('No closing lines stored for these games yet.')

    st.markdown(f'#### 💡 Best-bets strategy · moneyline edge ≥ {edge:.0%}')
    b = s.get('bets')
    if b is None or b.empty:
        st.caption('No bets cleared that edge.')
    else:
        m = st.columns(4)
        m[0].metric('Bets', f"{s['bet_n']:,}")
        m[1].metric('Win rate', _pct(s['bet_hit']))
        m[2].metric('Profit', f"${s['bet_profit']:+,.0f}", help='Flat $100 per bet')
        m[3].metric('ROI', _pct(s['bet_roi']))
        b = b.sort_values('date')
        fig = go.Figure(go.Scatter(x=list(range(1, len(b) + 1)), y=b['profit'].cumsum(),
                                   mode='lines', line=dict(color='#2563eb', width=2)))
        fig.add_hline(y=0, line_color='#94a3b8', line_dash='dot')
        fig.update_layout(height=260, margin=dict(l=10, r=10, t=10, b=10),
                          xaxis_title='Bet #', yaxis_title='Cumulative profit ($)')
        st.plotly_chart(fig, use_container_width=True)

    st.markdown('#### Calibration · when the model says X%, does it happen X% of the time?')
    cal = calibration(view)
    fig = go.Figure()
    fig.add_trace(go.Scatter(x=[.5, 1], y=[.5, 1], mode='lines', name='Perfect',
                             line=dict(color='#94a3b8', dash='dot')))
    fig.add_trace(go.Scatter(x=cal['predicted'], y=cal['actual'], mode='lines+markers',
                             name='Model', text=cal['games'].map(lambda n: f'{n} games'),
                             line=dict(color='#2563eb', width=2)))
    fig.update_layout(height=300, margin=dict(l=10, r=10, t=10, b=10),
                      xaxis=dict(title='Predicted (favorite)', tickformat='.0%'),
                      yaxis=dict(title='Actual win rate', tickformat='.0%'),
                      legend=dict(orientation='h', y=1.1))
    st.plotly_chart(fig, use_container_width=True)

    by = []
    for yr in sorted(view['season'].unique()):
        ss = score(view[view['season'] == yr], edge)
        by.append({'Season': yr, 'Games': ss['n'], 'Accuracy': _pct(ss.get('accuracy')),
                   'ATS': _pct(ss.get('ats_rate')), 'Totals': _pct(ss.get('tot_rate')),
                   'Best bets': ss.get('bet_n', 0),
                   'Bet ROI': _pct(ss.get('bet_roi'))})
    st.markdown('#### By season')
    st.dataframe(pd.DataFrame(by), hide_index=True, use_container_width=True)
    st.caption('Injury adjustments are excluded (historical injury reports aren\'t stored). '
               'Past results don\'t guarantee future performance.')

"""App shell: design system CSS, landing/terms screens, header and navigation.

One responsive UI for every screen size (no separate "mobile mode"):
  • ≥ 769px: sticky header with league picker + a pill tab bar
  • < 769px: compact header + thumb-reach bottom bar with a More sheet
The Streamlit sidebar is not used at all; settings live on their own page.
"""
import streamlit as st

# ── Design tokens ────────────────────────────────────────────
CSS = """
<style>
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap');
:root {
  --ts-bg: #f5f7fb; --ts-card: #ffffff; --ts-ink: #0f172a; --ts-muted: #64748b;
  --ts-line: #e5e9f2; --ts-brand: #2563eb; --ts-brand-soft: #e8efff;
  --ts-good: #16a34a; --ts-bad: #dc2626; --ts-radius: 14px;
  --ts-shadow: 0 1px 2px rgba(15,23,42,.04), 0 4px 16px rgba(15,23,42,.06);
}
html, body, [class*="css"], .stApp { font-family: 'Inter', system-ui, -apple-system, 'Segoe UI', sans-serif; }
.stApp { background: var(--ts-bg); }

/* No sidebar anywhere: navigation is in the header / bottom bar */
section[data-testid="stSidebar"], [data-testid="stSidebarCollapsedControl"],
[data-testid="stExpandSidebarButton"] { display: none !important; }
#MainMenu, footer, [data-testid="stAppDeployButton"] { visibility: hidden; }
header[data-testid="stHeader"] { background: transparent; height: 0; }

.block-container { padding: 0.75rem 1.25rem 2rem !important; max-width: 1280px; }

/* ── Header ── */
.st-key-ts_header {
  position: sticky; top: 0; z-index: 999; background: rgba(245,247,251,.92);
  backdrop-filter: saturate(180%) blur(10px); -webkit-backdrop-filter: saturate(180%) blur(10px);
  border-bottom: 1px solid var(--ts-line); margin: -0.75rem -1.25rem 0.75rem; padding: 10px 1.25rem 8px;
}
.ts-brand { display: flex; align-items: center; gap: 10px; }
.ts-brand .logo { font-size: 26px; line-height: 1; }
.ts-brand .name { font-weight: 800; font-size: 19px; color: var(--ts-ink); letter-spacing: -.3px; }
.ts-brand .sub { font-size: 12px; color: var(--ts-muted); }
.ts-chip { display: inline-flex; align-items: center; gap: 6px; padding: 4px 10px; border-radius: 999px;
  background: var(--ts-brand-soft); color: #1e40af; font-size: 12px; font-weight: 600; white-space: nowrap;
  overflow: hidden; text-overflow: ellipsis; max-width: 100%; }

/* ── Desktop tab bar ── */
.st-key-ts_topnav [data-testid="stButtonGroup"] div:has(> button) { flex-wrap: wrap; gap: 6px; }
.st-key-ts_topnav button { border-radius: 999px !important; padding: 6px 14px !important;
  border: 1px solid var(--ts-line) !important; background: var(--ts-card) !important; }
.st-key-ts_topnav button[kind*="Active"], .st-key-ts_topnav button[aria-checked="true"] {
  background: var(--ts-ink) !important; color: #fff !important; border-color: var(--ts-ink) !important; }

/* ── Mobile bottom bar ── */
.st-key-ts_bottomnav { display: none; }

/* ── Cards & widgets ── */
[data-testid="stVerticalBlockBorderWrapper"]:has(> div > [data-testid="stVerticalBlock"]) {
  border-radius: var(--ts-radius); }
div[data-testid="stVerticalBlockBorderWrapper"][style*="border"] , .stContainer {
  background: var(--ts-card); }
[data-testid="stMetric"] { background: var(--ts-card); border: 1px solid var(--ts-line);
  border-radius: var(--ts-radius); padding: 12px 14px; box-shadow: var(--ts-shadow); }
[data-testid="stMetricValue"] { font-weight: 800; }
[data-testid="stExpander"] details { background: var(--ts-card); border: 1px solid var(--ts-line) !important;
  border-radius: var(--ts-radius) !important; box-shadow: var(--ts-shadow); }
[data-testid="stDataFrame"] { border-radius: 12px; overflow: hidden; border: 1px solid var(--ts-line); }
.stButton > button, .stDownloadButton > button { border-radius: 10px; font-weight: 600; }
.stTabs [data-baseweb="tab-list"] { gap: 4px; background: #eef1f7; padding: 4px; border-radius: 12px;
  overflow-x: auto; flex-wrap: nowrap; scrollbar-width: none; }
.stTabs [data-baseweb="tab"] { border-radius: 9px; padding: 6px 12px; font-size: 13px; white-space: nowrap; }
.stTabs [aria-selected="true"] { background: #fff !important; box-shadow: 0 1px 4px rgba(0,0,0,.08); }
.stTabs [data-baseweb="tab-highlight"], .stTabs [data-baseweb="tab-border"] { display: none; }
h1, h2, h3 { letter-spacing: -.4px; color: var(--ts-ink); }
[data-baseweb="select"] > div { border-radius: 10px !important; }

/* ── Score cards ── */
      .tsg { background:#fff;border:1px solid #e5e9f2;border-radius:16px;padding:14px 16px;
             margin-bottom:12px;box-shadow:0 1px 2px rgba(15,23,42,.04),0 4px 16px rgba(15,23,42,.06);
             font-family:Inter,system-ui,sans-serif;color:#0f172a; }
      .tsg-top { display:flex;flex-wrap:wrap;gap:6px;align-items:center;margin-bottom:10px; }
      .tsg-pill { font-size:12px;font-weight:600;padding:3px 10px;border-radius:999px; }
      .tsg-row { display:flex;align-items:center;gap:10px;padding:5px 0; }
      .tsg-name { flex:1;font-size:15px;min-width:0; }
      .tsg-rec { font-size:12px;color:#94a3b8;font-weight:500;margin-left:6px; }
      .tsg-score { font-size:24px;min-width:44px;text-align:right;font-variant-numeric:tabular-nums; }
      .tsg-line { overflow-x:auto;margin:8px 0 2px; }
      .tsg-line table { border-collapse:collapse;font-size:12px;color:#475569; }
      .tsg-line th, .tsg-line td { padding:2px 8px;text-align:center; }
      .tsg-line td:first-child, .tsg-line th:first-child { text-align:left;font-weight:600;color:#0f172a; }
      .tsg-chips { display:flex;flex-wrap:wrap;gap:6px;margin-top:10px; }
      .tsg-chip { font-size:12px;color:#475569;background:#f1f5f9;border-radius:999px;padding:4px 10px; }
      .tsg-meta { font-size:12px;color:#64748b;margin-top:10px; }
      .tsg-link { font-size:12px;font-weight:600;color:#2563eb;text-decoration:none;margin-right:12px; }
      .tsg-head { font-size:13px;color:#334155;font-style:italic;margin-top:8px; }
/* ── Phones ── */
@media (max-width: 768px) {
  .block-container { padding: 0.5rem 0.75rem 110px !important; }
  .st-key-ts_header { margin: -0.5rem -0.75rem 0.5rem; padding: 8px 0.75rem 6px; }
  .ts-brand .name { font-size: 16px; } .ts-brand .sub { display: none; }
  .st-key-ts_topnav { display: none; }
  .st-key-ts_bottomnav {
    display: block; position: fixed; left: 0; right: 0; bottom: 0; z-index: 999990;
    background: rgba(255,255,255,.97); border-top: 1px solid var(--ts-line);
    box-shadow: 0 -4px 18px rgba(15,23,42,.08);
    padding: 6px 6px calc(6px + env(safe-area-inset-bottom));
  }
  .st-key-ts_bottomnav [data-testid="stButtonGroup"] { width: 100%; }
  .st-key-ts_bottomnav [data-testid="stButtonGroup"] div:has(> button) {
    display: flex !important; width: 100% !important; max-width: none !important; gap: 4px; flex-wrap: nowrap !important; }
  .st-key-ts_bottomnav button {
    flex: 0 0 calc((100% - 16px) / 5) !important; width: calc((100% - 16px) / 5) !important;
    min-width: 0 !important; max-width: none !important; min-height: 58px; padding: 4px 2px !important;
    border-radius: 14px !important; border: none !important; background: transparent !important;
    flex-direction: column !important; gap: 2px !important; }
  .st-key-ts_bottomnav button[kind*="Active"], .st-key-ts_bottomnav button[aria-checked="true"] {
    background: var(--ts-brand-soft) !important; color: var(--ts-brand) !important; }
  .st-key-ts_bottomnav button [data-testid="stIconEmoji"] { font-size: 21px; margin: 0 !important; }
  .st-key-ts_bottomnav button p, .st-key-ts_bottomnav button [data-testid="stMarkdownContainer"] {
    font-size: 11px !important; line-height: 1.2 !important; overflow: visible !important; text-overflow: clip !important; }
  /* Columns stack; bigger tap targets */
  [data-testid="stHorizontalBlock"] { flex-wrap: wrap; gap: .5rem; }
  [data-testid="stHorizontalBlock"] > [data-testid="stColumn"] { min-width: 100% !important; flex: 1 1 100% !important; }
  .st-key-ts_header [data-testid="stHorizontalBlock"] { flex-wrap: nowrap; }
  .st-key-ts_header [data-testid="stHorizontalBlock"] > [data-testid="stColumn"] { min-width: 0 !important; flex: 1 1 0 !important; }
  .stButton > button { min-height: 44px; }
  [data-baseweb="select"] > div { min-height: 44px; }
  h1 { font-size: 1.5rem !important; } h2 { font-size: 1.3rem !important; } h3 { font-size: 1.15rem !important; }
  [data-testid="stMetric"] { padding: 10px; }
  [data-testid="stMetricValue"] { font-size: 1.3rem !important; }
}
</style>
"""

# Streamlit Cloud draws its own Fork/avatar/badge over the app and they can't be
# hidden from inside it, so on phones the layout leaves room for them.
CLOUD_CSS = """
<style>
@media (max-width: 768px) {
  .st-key-ts_header { padding-top: 44px !important; }
  /* The badge and avatar can sit anywhere along the bottom, so clear them vertically. */
  .st-key-ts_bottomnav { bottom: 62px !important; border-radius: 14px 14px 0 0; }
  .block-container { padding-bottom: 180px !important; }
}
</style>
"""

LANDING_CSS = """
<style>
.ts-hero { text-align: center; padding: 6vh 8px 2vh; }
.ts-hero .t { font-size: clamp(30px, 7vw, 56px); font-weight: 800; letter-spacing: -1.5px; color: #0f172a; line-height: 1.05; }
.ts-hero .t span { background: linear-gradient(90deg,#2563eb,#7c3aed); -webkit-background-clip: text; background-clip: text; color: transparent; }
.ts-hero .s { font-size: clamp(15px, 2.4vw, 19px); color: #64748b; max-width: 640px; margin: 14px auto 0; line-height: 1.55; }
.ts-feats { display: grid; grid-template-columns: repeat(auto-fit, minmax(150px, 1fr)); gap: 10px; max-width: 900px; margin: 22px auto; }
.ts-feat { background: #fff; border: 1px solid #e5e9f2; border-radius: 14px; padding: 14px; text-align: left; box-shadow: 0 4px 16px rgba(15,23,42,.05); }
.ts-feat b { display: block; margin: 6px 0 2px; color: #0f172a; } .ts-feat small { color: #64748b; }
.ts-terms { max-width: 640px; margin: 0 auto; font-size: 13px; color: #64748b; line-height: 1.6; }
</style>
"""

FEATURES = [
    ('🏅', 'Live scores', 'Every game, box scores and play-by-play'),
    ('⚔️', 'Matchups', 'Projected winners and score predictions'),
    ('🎯', 'Odds', 'FanDuel, ESPN and Kalshi lines side by side'),
    ('👤', 'Players', 'Game logs and season stats for every player'),
]


def render_landing() -> bool:
    """Single welcome screen with the terms inline. Returns True once accepted."""
    st.html(CSS + LANDING_CSS)
    st.html(
        '<div class="ts-hero"><div class="t">Truly<span>Sporting</span></div>'
        '<div class="s">Scores, matchups, odds and player stats for every major league — '
        'all loaded for you, on any screen.</div></div>'
        '<div class="ts-feats">' + ''.join(
            f'<div class="ts-feat"><span style="font-size:24px">{i}</span><b>{t}</b><small>{d}</small></div>'
            for i, t, d in FEATURES) + '</div>')
    _, mid, _ = st.columns([1, 2, 1])
    with mid:
        agree = st.checkbox('I am 18+ and understand this data is from ESPN and other public '
                            'sources, provided "as is", for information only — not betting advice.',
                            key='tos_check')
        if st.button('Get started  →', type='primary', use_container_width=True, disabled=not agree):
            st.session_state['tos_accepted'] = True
            st.query_params['ok'] = '1'  # a refresh or bookmark shouldn't ask again
            st.session_state['app_started'] = True
            st.rerun()
    st.html('<div class="ts-terms" style="text-align:center;margin-top:10px">'
            'Not affiliated with or endorsed by ESPN, FanDuel, Kalshi or any league.</div>')
    return False


def render_header(league_opts, league_label, status_fn=None) -> str:
    """Sticky header: brand, global league picker, live sync status. Returns league."""
    with st.container(key='ts_header'):
        c1, c2 = st.columns([3, 2], vertical_alignment='center')
        with c1:
            st.html('<div class="ts-brand"><span class="logo">🏆</span><div>'
                    '<div class="name">TrulySporting</div>'
                    '<div class="sub">Scores · Matchups · Odds · Players</div></div></div>')
        with c2:
            league = st.selectbox('League', league_opts, key='g_league',
                                  format_func=league_label, label_visibility='collapsed')
        if status_fn:
            status_fn()
    return league


def render_nav(pages, bottom: dict, current: str, on_pick, on_bottom) -> None:
    """Desktop pill tabs + mobile bottom bar, both bound to the same page state."""
    # A value outside the options makes the widget raise and takes the page down.
    st.session_state['ts_topnav_sel'] = current if current in pages else None
    with st.container(key='ts_topnav'):
        st.segmented_control('Pages', pages, key='ts_topnav_sel', on_change=on_pick,
                             label_visibility='collapsed')
    more_key = next(k for k, v in bottom.items() if v is None)
    st.session_state['ts_bottomnav_sel'] = next(
        (k for k, v in bottom.items() if v == current), more_key)
    with st.container(key='ts_bottomnav'):
        st.segmented_control('Pages', list(bottom), key='ts_bottomnav_sel',
                             on_change=on_bottom, label_visibility='collapsed')

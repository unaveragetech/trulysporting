"""Colour system: a soft light theme, a real dark theme, and an Auto / Light / Dark switch.

Auto follows the visitor's system setting.  The switch works by reloading the app with Streamlit's own
``embed_options=dark_theme|light_theme`` URL option, so Streamlit's widgets and tables switch with our cards.
Older pages were written with hard-coded light colours; in dark mode ``LEGACY`` remaps those inline colours to the
palette so nothing stays glaring white.
"""
import base64
from typing import Dict, List, Tuple
from urllib.parse import urlencode

import streamlit as st

# ── Palettes ─────────────────────────────────────────────────────────────────
# Light is deliberately off-white with slate ink (no pure white fields, no pure black text); dark is a deep navy
# "night game" palette with lowered saturation so bright accents do not glare.
LIGHT: Dict[str, str] = {
    "--ts-bg": "#eef1f6", "--ts-card": "#fbfcfe", "--ts-card2": "#e9edf4", "--ts-ink": "#1b2536",
    "--ts-muted": "#5b6980", "--ts-line": "#d9dfe9", "--ts-brand": "#15803d", "--ts-brand-ink": "#166534",
    "--ts-brand-soft": "#dcf2e3", "--ts-accent": "#d97706", "--ts-good": "#15803d", "--ts-bad": "#dc2626",
    "--ts-live": "#dc2626", "--ts-live-soft": "#fde4e4", "--ts-final-soft": "#e3e8f0", "--ts-header-bg": "rgba(238,241,246,.92)",
    "--ts-shadow": "0 1px 2px rgba(20,30,50,.05), 0 6px 18px rgba(20,30,50,.07)",
    "--ts-on-brand": "#ffffff", "--ts-turf": "#1f7a3d", "--ts-turf2": "#2a9d4f", "--ts-hero1": "#0f3d2e", "--ts-hero2": "#14532d",
}
DARK: Dict[str, str] = {
    "--ts-bg": "#0b101a", "--ts-card": "#131b2a", "--ts-card2": "#1a2437", "--ts-ink": "#e6ebf4",
    "--ts-muted": "#93a1b8", "--ts-line": "#263249", "--ts-brand": "#4ade80", "--ts-brand-ink": "#86efac",
    "--ts-brand-soft": "rgba(74,222,128,.13)", "--ts-accent": "#fbbf24", "--ts-good": "#4ade80", "--ts-bad": "#f87171",
    "--ts-live": "#fb7185", "--ts-live-soft": "rgba(251,113,133,.16)", "--ts-final-soft": "rgba(147,161,184,.16)",
    "--ts-header-bg": "rgba(11,16,26,.9)",
    "--ts-shadow": "0 1px 2px rgba(0,0,0,.4), 0 8px 22px rgba(0,0,0,.35)",
    "--ts-on-brand": "#052e16", "--ts-turf": "#14532d", "--ts-turf2": "#166534", "--ts-hero1": "#0a2a20", "--ts-hero2": "#0f3b2a",
}

# League accent colours (header strip and chips). Keys match substrings of the league endpoint.
LEAGUE_ACCENT: List[Tuple[str, str, str]] = [
    ("college-football", "#9f1239", "#e11d48"), ("football/nfl", "#1d4ed8", "#dc2626"), ("football/ufl", "#1d4ed8", "#f59e0b"),
    ("nba", "#ea580c", "#1d4ed8"), ("wnba", "#7c3aed", "#ea580c"), ("basketball", "#ea580c", "#f59e0b"),
    ("mlb", "#1e3a8a", "#dc2626"), ("baseball", "#1e3a8a", "#16a34a"), ("nhl", "#0ea5e9", "#1e3a8a"),
    ("hockey", "#0ea5e9", "#64748b"), ("soccer", "#16a34a", "#0ea5e9"),
]


def league_accent(ep: str) -> Tuple[str, str]:
    for key, a, b in LEAGUE_ACCENT:
        if key in (ep or ""):
            return a, b
    return "#16a34a", "#0ea5e9"


# ── Legacy remap (dark only): inline colours from older pages -> palette ─────
_BG: Dict[str, str] = {
    "#fff": "var(--ts-card)", "#ffffff": "var(--ts-card)", "#fafafa": "var(--ts-card2)", "#f8fafc": "var(--ts-card2)",
    "#f1f5f9": "var(--ts-card2)", "#f5f7fb": "var(--ts-bg)", "#f0f2f6": "var(--ts-card2)", "#eef1f7": "var(--ts-card2)",
    "#e2e8f0": "var(--ts-line)", "#f0fdf4": "rgba(74,222,128,.12)", "#f0fff0": "rgba(74,222,128,.12)",
    "#d4edda": "rgba(74,222,128,.18)", "#f0f9ff": "rgba(56,189,248,.12)", "#e8efff": "rgba(96,165,250,.16)",
    "#f0f4ff": "rgba(129,140,248,.14)", "#fdf4ff": "rgba(192,132,252,.13)", "#f8f0ff": "rgba(167,139,250,.13)",
    "#fff8f0": "rgba(251,146,60,.13)", "#fff3cd": "rgba(251,191,36,.16)", "#fee2e2": "var(--ts-live-soft)",
    "#ede9fe": "rgba(167,139,250,.18)", "#cbd5e1": "var(--ts-line)", "#fefce8": "rgba(251,191,36,.12)",
    "#fff7ed": "rgba(251,146,60,.12)", "#f0f9ff": "rgba(56,189,248,.12)", "#ecfdf5": "rgba(74,222,128,.12)",
}
_FG: Dict[str, str] = {
    "#1a1a2e": "var(--ts-ink)", "#0f172a": "var(--ts-ink)", "#111": "var(--ts-ink)", "#222": "var(--ts-ink)",
    "#333": "var(--ts-ink)", "#444": "var(--ts-ink)", "#334155": "var(--ts-ink)", "#555": "var(--ts-muted)",
    "#666": "var(--ts-muted)", "#777": "var(--ts-muted)", "#888": "var(--ts-muted)", "#999": "var(--ts-muted)",
    "#bbb": "var(--ts-muted)", "#aaa": "var(--ts-muted)", "#94a3b8": "var(--ts-muted)", "#64748b": "var(--ts-muted)",
    "#475569": "var(--ts-muted)", "#6c757d": "var(--ts-muted)", "#166534": "#86efac", "#059669": "#34d399",
    "#0c4a6e": "#7dd3fc", "#1e40af": "#93c5fd", "#92400e": "#fcd34d", "#581c87": "#d8b4fe", "#6d28d9": "#c4b5fd",
    "#b91c1c": "#fca5a5", "#4c1d95": "#c4b5fd", "#2563eb": "#93c5fd", "#854d0e": "#fcd34d", "#0f766e": "#5eead4",
}
_BORDER: Dict[str, str] = {
    "#e5e9f2": "var(--ts-line)", "#e2e8f0": "var(--ts-line)", "#e5e7eb": "var(--ts-line)", "#d0d5e0": "var(--ts-line)",
    "#cbd5e1": "var(--ts-line)", "#bbf7d0": "rgba(74,222,128,.35)", "#bae6fd": "rgba(56,189,248,.35)",
    "#e9d5ff": "rgba(192,132,252,.35)", "#fed7aa": "rgba(251,146,60,.35)", "#ddd6fe": "rgba(167,139,250,.35)",
    "#fde68a": "rgba(251,191,36,.4)", "#f1f5f9": "var(--ts-line)",
}


def _legacy_rules() -> str:
    """Attribute selectors for inline ``prop:#hex`` (followed by ; or ending the style attribute), so older
    hard-coded colours follow the palette in dark mode."""
    out: List[str] = []
    props = {"background": _BG, "background-color": _BG, "color": _FG, "border-color": _BORDER}
    for prop, table in props.items():
        for hexv, new in table.items():
            for sp in ("", " "):
                frag = f"{prop}:{sp}{hexv}"
                out.append(f'[style*="{frag};"]{{{prop}:{new} !important}}')
                out.append(f'[style$="{frag}"]{{{prop}:{new} !important}}')
    for hexv, new in _BORDER.items():  # shorthand: border: 1px solid #e5e9f2
        for sp in ("", " "):
            frag = f"solid{sp}{hexv}"
            out.append(f'[style*="{frag};"]{{border-color:{new} !important}}')
            out.append(f'[style$="{frag}"]{{border-color:{new} !important}}')
    return "".join(out)


def _vars(d: Dict[str, str]) -> str:
    return ";".join(f"{k}:{v}" for k, v in d.items())


# ── The stylesheet ───────────────────────────────────────────────────────────
# Sports flourishes: a turf strip with yard lines above the header, league-coloured accents, scoreboard type,
# pulsing LIVE dot, team-colour stripe on game cards, stadium-lights hero.
BASE = """
:root { --ts-radius: 14px; --ts-league: #16a34a; --ts-league2: #0ea5e9; }
html { font-size: 16px; }
body, .stApp { line-height: 1.55; -webkit-font-smoothing: antialiased; }
.stApp { background: var(--ts-bg) !important; color: var(--ts-ink); }
.stApp p, .stApp li, .stApp label, .stApp span, .stApp td, .stApp th { color: inherit; }
h1, h2, h3, h4 { color: var(--ts-ink) !important; }
a { color: var(--ts-brand-ink); }
.stCaption, [data-testid="stCaptionContainer"] { color: var(--ts-muted) !important; }

/* Turf strip with yard lines across the very top, tinted by the selected league */
.stApp::before { content: ""; position: fixed; z-index: 1000000; top: 0; left: 0; right: 0; height: 5px; pointer-events: none;
  background:
    repeating-linear-gradient(90deg, rgba(255,255,255,.55) 0 1px, transparent 1px 22px),
    linear-gradient(90deg, var(--ts-league), var(--ts-turf2) 55%, var(--ts-league2)); }

/* Header */
.st-key-ts_header { background: var(--ts-header-bg) !important; border-bottom: 1px solid var(--ts-line) !important; }
.ts-brand { width: 100%; }
.ts-brand .name { color: var(--ts-ink) !important; }
.ts-brand .sub { color: var(--ts-muted) !important; }
.ts-logo { width: 34px; height: 34px; flex: none; filter: drop-shadow(0 2px 4px rgba(0,0,0,.25)); }
.ts-theme { margin-left: auto; display: inline-flex; gap: 2px; padding: 3px; border-radius: 999px;
  background: var(--ts-card2); border: 1px solid var(--ts-line); }
.ts-theme a { text-decoration: none !important; font-size: 12px; font-weight: 700; padding: 4px 10px; border-radius: 999px;
  color: var(--ts-muted) !important; }
.ts-theme a.on { background: var(--ts-card); color: var(--ts-ink) !important; box-shadow: 0 1px 3px rgba(0,0,0,.18); }
.ts-theme-cycle { display: none; margin-left: auto; text-decoration: none !important; font-size: 18px; width: 38px; height: 38px;
  align-items: center; justify-content: center; border-radius: 50%; background: var(--ts-card2); border: 1px solid var(--ts-line); }
@media (max-width: 768px) { .ts-theme { display: none; }
  .st-key-ts_header .ts-theme-cycle { display: inline-flex; position: absolute; right: 12px; bottom: 8px; margin: 0; } }
.ts-chip { background: var(--ts-brand-soft) !important; color: var(--ts-brand-ink) !important; }

/* Navigation pills pick up the league colour when active */
.st-key-ts_topnav button { background: var(--ts-card) !important; color: var(--ts-ink) !important; border-color: var(--ts-line) !important; }
.st-key-ts_topnav button[kind*="Active"], .st-key-ts_topnav button[aria-checked="true"] {
  background: var(--ts-league) !important; color: #fff !important; border-color: var(--ts-league) !important;
  box-shadow: 0 2px 10px color-mix(in srgb, var(--ts-league) 40%, transparent); }
.st-key-ts_bottomnav { background: var(--ts-header-bg) !important; border-top: 1px solid var(--ts-line) !important; }

/* Cards, metrics, expanders, tabs */
[data-testid="stMetric"], [data-testid="stExpander"] details, .stContainer { background: var(--ts-card) !important;
  border-color: var(--ts-line) !important; }
[data-testid="stMetricLabel"] { color: var(--ts-muted) !important; }
[data-testid="stMetricValue"] { color: var(--ts-ink) !important; }
.stTabs [data-baseweb="tab-list"] { background: var(--ts-card2) !important; }
.stTabs [data-baseweb="tab"] { color: var(--ts-muted) !important; }
.stTabs [aria-selected="true"] { background: var(--ts-card) !important; color: var(--ts-ink) !important; }
[data-testid="stDataFrame"] { border-color: var(--ts-line) !important; }
.stButton > button[kind="primary"] { background: var(--ts-brand) !important; border-color: var(--ts-brand) !important; color: var(--ts-on-brand) !important; font-weight: 700; }
.stButton > button[kind="primary"] p { color: var(--ts-on-brand) !important; }
.stButton > button:disabled { opacity: .45 !important; filter: saturate(.5); cursor: not-allowed; }
@media (prefers-reduced-motion: no-preference) { .stButton > button { transition: transform .08s ease, box-shadow .15s ease; }
  .stButton > button:hover { transform: translateY(-1px); } }

/* Inputs get a visible edge so fields never melt into the page */
[data-baseweb="input"] > div, [data-baseweb="base-input"], [data-baseweb="select"] > div, [data-baseweb="textarea"] {
  background: var(--ts-card) !important; border: 1px solid var(--ts-line) !important; border-radius: 10px !important; }
[data-baseweb="input"] input, [data-baseweb="select"] div, textarea { color: var(--ts-ink) !important; }
[data-baseweb="input"] input::placeholder { color: var(--ts-muted) !important; opacity: .8; }

/* Scoreboard-style game cards */
.tsg { position: relative; background: var(--ts-card) !important; border: 1px solid var(--ts-line) !important;
  color: var(--ts-ink) !important; box-shadow: var(--ts-shadow) !important; padding-left: 22px !important; overflow: hidden; }
.tsg-stripe { position: absolute; left: 0; top: 0; bottom: 0; width: 6px; }
.tsg-score { font-family: 'Inter', ui-monospace, monospace; font-weight: 800; letter-spacing: -.5px; font-size: 30px !important; }
.tsg-name { font-size: 16px !important; }
.tsg-rec, .tsg-meta { color: var(--ts-muted) !important; }
.tsg-chip { background: var(--ts-card2) !important; color: var(--ts-muted) !important; }
.tsg-chip b, .tsg-line td:first-child, .tsg-line th:first-child { color: var(--ts-ink) !important; }
.tsg-line table, .tsg-head { color: var(--ts-muted) !important; }
.tsg-link { color: var(--ts-brand-ink) !important; }
.tsg-pill { font-size: 12px; font-weight: 700; padding: 3px 10px; border-radius: 999px; letter-spacing: .2px; }
.tsg-pill.live { background: var(--ts-live-soft); color: var(--ts-live); }
.tsg-pill.final { background: var(--ts-final-soft); color: var(--ts-muted); }
.tsg-pill.pre { background: var(--ts-brand-soft); color: var(--ts-brand-ink); }
.tsg-pill.live::before { content: ""; display: inline-block; width: 8px; height: 8px; border-radius: 50%; margin-right: 6px;
  background: var(--ts-live); vertical-align: 1px; animation: ts-pulse 1.4s ease-out infinite; }
@keyframes ts-pulse { 0% { box-shadow: 0 0 0 0 color-mix(in srgb, var(--ts-live) 60%, transparent); }
  70% { box-shadow: 0 0 0 8px transparent; } 100% { box-shadow: 0 0 0 0 transparent; } }
@media (prefers-reduced-motion: reduce) { .tsg-pill.live::before { animation: none; } }

/* Landing hero: stadium lights over a field */
.ts-hero { position: relative; border-radius: 22px; padding: 7vh 18px 5vh !important; margin: 6px 0 12px; overflow: hidden;
  background:
    radial-gradient(900px 260px at 18% -10%, rgba(255,255,255,.20), transparent 60%),
    radial-gradient(900px 260px at 82% -10%, rgba(255,255,255,.16), transparent 60%),
    repeating-linear-gradient(90deg, rgba(255,255,255,.07) 0 2px, transparent 2px 64px),
    linear-gradient(180deg, var(--ts-hero1), var(--ts-hero2)); box-shadow: var(--ts-shadow); }
.ts-hero::after { content: ""; position: absolute; left: 50%; bottom: -120px; width: 420px; height: 420px; transform: translateX(-50%);
  border: 2px solid rgba(255,255,255,.12); border-radius: 50%; pointer-events: none; }
.ts-hero .t { color: #fff !important; text-shadow: 0 2px 14px rgba(0,0,0,.35); }
.ts-hero .t span { background: linear-gradient(90deg,#86efac,#fde68a) !important; -webkit-background-clip: text !important;
  background-clip: text !important; color: transparent !important; }
.ts-hero .s { color: rgba(255,255,255,.86) !important; }
.ts-hero .sports { margin-top: 18px; font-size: 26px; letter-spacing: 10px; opacity: .95; }
.ts-feat { background: var(--ts-card) !important; border-color: var(--ts-line) !important; }
.ts-feat b { color: var(--ts-ink) !important; } .ts-feat small, .ts-terms { color: var(--ts-muted) !important; }

/* Support / marketing blocks that use inline styles rely on the legacy remap below in dark mode. */
#ts-ad-bar { background: var(--ts-card) !important; border-top: 1px solid var(--ts-line) !important; }
.st-key-bottom_nav { background: var(--ts-header-bg) !important; border-top: 1px solid var(--ts-line) !important; }
"""

# Streamlit widgets that keep their own palette even when the theme matches (popovers, inputs) need no extra work
# because the matching embed_options theme is applied; only our own colours are handled here.
DARK_ONLY = """
.stApp { color-scheme: dark; }
img[src*="espncdn"], img[src*="logo"] { filter: drop-shadow(0 0 1px rgba(255,255,255,.35)); }
.ts-logo { filter: drop-shadow(0 2px 6px rgba(0,0,0,.6)); }
"""


def current_mode() -> str:
    """'light', 'dark' or 'auto' from the ``theme`` URL option the switch sets (Streamlit hides embed_options)."""
    try:
        v = str(st.query_params.get("theme", "")).lower()
    except Exception:
        return "auto"
    return v if v in ("light", "dark") else "auto"


def css(mode: str = "auto") -> str:
    legacy = _legacy_rules()
    if mode == "dark":
        body = f":root{{{_vars(LIGHT)}}}:root{{{_vars(DARK)}}}{BASE}{DARK_ONLY}{legacy}"
    elif mode == "light":
        body = f":root{{{_vars(LIGHT)}}}{BASE}"
    else:
        body = (f":root{{{_vars(LIGHT)}}}{BASE}"
                f"@media (prefers-color-scheme: dark){{:root{{{_vars(DARK)}}}{DARK_ONLY}{legacy}}}")
    return f"<style>{body}</style>"


def league_css(ep: str) -> str:
    a, b = league_accent(ep)
    return f"<style>:root{{--ts-league:{a};--ts-league2:{b}}}</style>"


_LOGO_SVG = (
    '<svg viewBox="0 0 48 48" xmlns="http://www.w3.org/2000/svg">'
    '<defs><linearGradient id="g" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#22c55e"/>'
    '<stop offset="1" stop-color="#15803d"/></linearGradient></defs>'
    '<rect x="2" y="2" width="44" height="44" rx="12" fill="url(#g)"/>'
    '<g transform="rotate(-35 24 24)"><ellipse cx="24" cy="24" rx="17" ry="10" fill="#a16207" stroke="#fff7ed" stroke-width="1.5"/>'
    '<path d="M14 24h20M19 20.5v7M24 19.5v9M29 20.5v7" stroke="#fff7ed" stroke-width="1.6" stroke-linecap="round"/></g></svg>')
# Streamlit strips inline <svg>, so the logo ships as an image data URI
LOGO_SVG = ('<img class="ts-logo" alt="" src="data:image/svg+xml;base64,'
            + base64.b64encode(_LOGO_SVG.encode()).decode() + '">')


_NATIVE = {"light": "light_theme", "dark": "dark_theme"}


def _href(mode: str) -> str:
    """Current URL params with the theme set (auto removes both options)."""
    try:
        params = {k: v for k, v in st.query_params.items() if k not in ("theme", "embed_options")}
    except Exception:
        params = {}
    if mode in _NATIVE:
        params["theme"] = mode
        params["embed_options"] = _NATIVE[mode]
    return "?" + urlencode(params)


def switch_html(mode: str) -> str:
    """Auto / Light / Dark links; each reloads with the matching Streamlit theme option, keeping other URL params."""
    items = [("auto", "Auto"), ("light", "☀ Light"), ("dark", "☾ Dark")]
    links = "".join(f'<a class="{"on" if m == mode else ""}" href="{_href(m)}" target="_self">{lbl}</a>' for m, lbl in items)
    return f'<div class="ts-theme" role="group" aria-label="Colour theme">{links}</div>'


def cycle_html(mode: str) -> str:
    """One-tap theme cycle (auto -> dark -> light) shown on phones, where the full switch does not fit."""
    nxt, icon = {"auto": ("dark", "🌓"), "dark": ("light", "☾"), "light": ("auto", "☀")}[mode]
    return f'<a class="ts-theme-cycle" href="{_href(nxt)}" target="_self" title="Switch colour theme">{icon}</a>'

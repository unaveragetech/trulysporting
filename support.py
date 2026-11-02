"""Support page and the occasional, dismiss-free support nudge.

Everything an owner edits lives in the CONFIG block below (amounts, milestones, extra donation links) so the page
never needs HTML edits.  Nothing here limits any feature: supporting is always optional.
"""
import os
import time
from typing import Dict, List

import streamlit as st

# ── CONFIG: edit these ───────────────────────────────────────────────────────
CASH_APP = "slightlysigh"
SITE_URL = "https://trulysporting.streamlit.app"
REPO_URL = "https://github.com/unaveragetech/trulysporting"
RAISED_USD = 365          # total donated so far (the original $65 plus the later $300 gift)
GOAL_USD = 1000
TIERS = [(3, "A coffee"), (5, "Say thanks"), (10, "Keep it running"), (25, "Fund a feature"), (50, "Big thank-you")]
# Optional extra ways to give; shown only when set (e.g. GitHub Sponsors, Ko-fi, Buy Me a Coffee)
EXTRA_LINKS: List[Dict[str, str]] = []
# (amount that unlocks it, name, what it means, shipped?)
MILESTONES = [
    (65, "📱 Mobile UI", "Phone-friendly layout", True),
    (100, "🔔 Game alerts", "Watchlist alerts for tracked teams", True),
    (250, "🤖 AI game summaries", "Plain-English game recaps", False),
    (500, "📊 Fantasy points engine", "Fantasy scores from box scores, any scoring format", False),
    (1000, "🌍 Multi-language + shared DB", "Spanish / French / Portuguese and team sharing", False),
]
# Things that are free today.
FREE_FEATURES = [
    ("🏅", "Live scores & box scores", "Every major league, play-by-play, refreshed live"),
    ("⚔️", "Matchups & projections", "Projected winners and scores for every upcoming game"),
    ("🎯", "Odds, side by side", "FanDuel, ESPN, Kalshi and sportsbook lines in one table"),
    ("🏈", "NFL Engine", "A play-by-play simulator trained on a decade of NFL games"),
    ("🔴", "Live engine vs reality", "Grades the engine's prediction for every snap as it happens"),
    ("📈", "Live win probability", "Calibrated against past games and the betting market"),
    ("🔮", "Next 5 plays", "Likely pass/run, punts and field goals for the next five snaps"),
    ("🧠", "Team dynamics", "Coach decisions, tendencies by situation, formations and coverage"),
    ("👤", "Player matchups", "Simulate a receiver against a specific defender"),
    ("📊", "Backtests", "See how every model really did on games it never saw"),
    ("🔔", "Watchlist & alerts", "Star games and teams, get alerted when they matter"),
    ("🛠", "Custom views", "Chart and table any combination of the data"),
]
# ─────────────────────────────────────────────────────────────────────────────


def _cash(amount: int = 0) -> str:
    return f"https://cash.app/${CASH_APP}" + (f"/{amount}" if amount else "")


def _secret(name: str, default: str = "") -> str:
    try:
        return str(st.secrets.get(name, "") or os.environ.get(name, default))
    except Exception:
        return os.environ.get(name, default)


def _progress_html() -> str:
    pct = max(2.0, min(100.0, 100.0 * RAISED_USD / GOAL_USD))
    marks, last = "", -99.0
    for m in MILESTONES:  # label every milestone but skip ones that would overlap the previous label
        x = min(100.0, 100.0 * m[0] / GOAL_USD)
        if x - last >= 9.0:
            marks += (f'<div style="position:absolute;top:100%;left:{x}%;transform:translateX(-50%);margin-top:6px;'
                      f'font-size:10px;color:#94a3b8;white-space:nowrap">${m[0]:,}</div>')
            last = x
    chips = ""
    for amt, name, desc, shipped in MILESTONES:
        if shipped:
            tag, bg, bd, col = "SHIPPED", "#f0fdf4", "#bbf7d0", "#166534"
        elif RAISED_USD >= amt:
            tag, bg, bd, col = "FUNDED · BUILDING", "#fefce8", "#fde68a", "#854d0e"
        else:
            tag, bg, bd, col = f"${max(0, amt - RAISED_USD):,} to go", "#f8fafc", "#e2e8f0", "#334155"
        chips += (f'<div style="background:{bg};border:1px solid {bd};border-radius:10px;padding:8px 12px;'
                  f'min-width:200px;flex:1"><div style="font-size:13px;font-weight:800;color:{col}">{name}'
                  f'<span style="font-size:9px;margin-left:8px;background:{col};color:#fff;border-radius:4px;'
                  f'padding:1px 6px;font-weight:700;vertical-align:middle">{tag}</span></div>'
                  f'<div style="font-size:12px;color:#475569;margin-top:2px">${amt:,} · {desc}</div></div>')
    return (
        '<div style="max-width:780px;margin:8px auto 0;padding:0 8px">'
        '<div style="background:linear-gradient(135deg,#064e3b,#047857);border-radius:16px;padding:22px 26px;'
        'text-align:center;box-shadow:0 4px 18px rgba(0,0,0,.18);margin-bottom:18px">'
        '<div style="font-size:36px">🙏</div>'
        '<div style="font-size:1.25rem;font-weight:900;color:#fff;margin:4px 0">Thank you, supporters</div>'
        f'<div style="font-size:.95rem;color:rgba(255,255,255,.88);line-height:1.7;max-width:560px;margin:0 auto">'
        f'Together you have funded <strong style="color:#6ee7b7">${RAISED_USD:,}</strong>. That paid for the mobile layout and '
        'game alerts, and it is paying for what comes next. One especially generous gift made a real difference. '
        'Every feature below stays free for everyone.</div></div>'
        '<div style="background:#fff;border:1px solid #e2e8f0;border-radius:16px;padding:22px 24px 26px">'
        '<div style="display:flex;justify-content:space-between;align-items:baseline;margin-bottom:12px">'
        '<div style="font-size:1rem;font-weight:800;color:#1a1a2e">💰 Community funding</div>'
        f'<div style="font-size:.85rem;color:#555"><strong style="font-size:1.05rem;color:#059669">${RAISED_USD:,}</strong>'
        f'<span style="color:#94a3b8"> of ${GOAL_USD:,}</span></div></div>'
        '<div style="position:relative;height:16px;background:#f1f5f9;border-radius:50px;margin-bottom:34px">'
        f'<div style="position:absolute;left:0;top:0;height:100%;width:{pct:.1f}%;background:linear-gradient(90deg,#059669,#10b981);'
        'border-radius:50px;box-shadow:0 2px 8px rgba(16,185,129,.45)"></div>' + marks + '</div>'
        f'<div style="display:flex;flex-wrap:wrap;gap:8px">{chips}</div>'
        '<p style="font-size:11px;color:#94a3b8;margin:12px 0 0;text-align:center">Funded features ship as free, open-source '
        'updates to everyone.</p></div></div>')


def _next_unfunded() -> str:
    for amt, name, _d, _s in MILESTONES:
        if RAISED_USD < amt:
            return f"${amt - RAISED_USD:,} from unlocking {name}"
    return "the next stretch goal"


def _free_html() -> str:
    cards = "".join(
        f'<div style="background:#fff;border:1px solid #e2e8f0;border-radius:12px;padding:14px 16px">'
        f'<div style="font-size:22px">{ic}</div><div style="font-weight:800;color:#1a1a2e;font-size:14px;margin-top:4px">{t}</div>'
        f'<div style="font-size:12px;color:#64748b;margin-top:2px;line-height:1.5">{d}</div></div>' for ic, t, d in FREE_FEATURES)
    return ('<div style="max-width:900px;margin:30px auto 0;padding:0 8px">'
            '<h2 style="text-align:center;font-size:1.25rem;font-weight:900;color:#1a1a2e;margin:0 0 4px">Everything here is free</h2>'
            '<p style="text-align:center;color:#64748b;font-size:.92rem;margin:0 0 16px">No paywall and no account needed. '
            'One developer, a decade of games, and a lot of simulations.</p>'
            f'<div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(230px,1fr));gap:12px">{cards}</div></div>')


def _tiers_html() -> str:
    btns = "".join(
        f'<a href="{_cash(a)}" target="_blank" rel="noopener noreferrer" style="text-decoration:none;flex:1;min-width:120px">'
        f'<div style="background:#fff;border:2px solid #16a34a;border-radius:14px;padding:14px 8px;text-align:center">'
        f'<div style="font-size:1.5rem;font-weight:900;color:#15803d">${a}</div>'
        f'<div style="font-size:11px;color:#64748b;margin-top:2px">{label}</div></div></a>' for a, label in TIERS)
    extra = "".join(
        f'<a href="{x["url"]}" target="_blank" rel="noopener noreferrer" style="text-decoration:none;color:#0c4a6e;'
        f'font-weight:700;font-size:13px;margin:0 10px">{x["label"]} →</a>' for x in EXTRA_LINKS)
    return ('<div style="max-width:780px;margin:30px auto 0;padding:0 8px">'
            '<div style="background:linear-gradient(135deg,#16a34a,#15803d);border-radius:18px;padding:24px 22px;'
            'box-shadow:0 6px 24px rgba(22,163,74,.35)">'
            '<div style="text-align:center;color:#fff;font-size:1.2rem;font-weight:900;margin-bottom:4px">Chip in with one tap</div>'
            f'<div style="text-align:center;color:rgba(255,255,255,.9);font-size:.9rem;margin-bottom:14px">'
            f'We are {_next_unfunded()}. Any amount helps; Cash App opens with the amount filled in.</div>'
            f'<div style="display:flex;flex-wrap:wrap;gap:10px">{btns}</div>'
            f'<div style="text-align:center;margin-top:14px"><a href="{_cash()}" target="_blank" rel="noopener noreferrer" '
            'style="color:#fff;font-weight:800;font-size:13px">Choose your own amount: $' + CASH_APP + ' →</a></div>'
            + (f'<div style="text-align:center;margin-top:10px;background:#fff;border-radius:10px;padding:8px">{extra}</div>' if extra else '')
            + '</div></div>')


def _where_html() -> str:
    items = [("📡", "Live data", "Odds and data feeds, and the compute behind live predictions."),
             ("☁️", "Hosting", "Keeping the site up and fast when a big game kicks off."),
             ("🧪", "Research time", "Retraining and testing the engine so its numbers stay honest."),
             ("🚀", "New features", "Everything on the roadmap; supporters help decide what comes first.")]
    cells = "".join(f'<div style="background:#f8fafc;border-radius:12px;padding:14px 16px"><div style="font-size:22px">{i}</div>'
                    f'<div style="font-weight:800;color:#1a1a2e;font-size:14px">{t}</div>'
                    f'<div style="font-size:12px;color:#64748b;margin-top:2px;line-height:1.5">{d}</div></div>' for i, t, d in items)
    return ('<div style="max-width:780px;margin:30px auto 0;padding:0 8px"><h2 style="text-align:center;font-size:1.15rem;'
            'font-weight:800;color:#1a1a2e;margin:0 0 12px">Where support goes</h2>'
            f'<div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:12px">{cells}</div></div>')


def _share_html() -> str:
    msg = "Free live scores, odds and an NFL simulation engine that grades itself on every play: TrulySporting"
    from urllib.parse import quote
    links = [("𝕏 Post", f"https://twitter.com/intent/tweet?text={quote(msg)}&url={quote(SITE_URL)}"),
             ("Reddit", f"https://www.reddit.com/submit?url={quote(SITE_URL)}&title={quote(msg)}"),
             ("Text a friend", f"sms:?&body={quote(msg + ' ' + SITE_URL)}"),
             ("⭐ Star on GitHub", REPO_URL)]
    btns = "".join(f'<a href="{u}" target="_blank" rel="noopener noreferrer" style="text-decoration:none;display:inline-block;'
                   f'background:#f1f5f9;border:1px solid #e2e8f0;border-radius:50px;padding:8px 18px;margin:4px;color:#1a1a2e;'
                   f'font-weight:700;font-size:13px">{t}</a>' for t, u in links)
    return ('<div style="max-width:780px;margin:30px auto 0;padding:0 8px;text-align:center">'
            '<h2 style="font-size:1.15rem;font-weight:800;color:#1a1a2e;margin:0 0 4px">Can\'t give right now? Spread the word</h2>'
            '<p style="color:#64748b;font-size:.92rem;margin:0 0 8px">Every new visitor helps the project grow, and costs you nothing.</p>'
            f'{btns}</div>')


def _roadmap_html() -> str:
    rows = [("🔔 Game alerts", "Alerts when a tracked team scores or a game starts", 40, 100),
            ("🤖 AI game summaries", "Plain-English recap for every game from play-by-play and box score", 50, 250),
            ("📊 Fantasy points engine", "Auto-calculate fantasy scores from box scores, any scoring format", 60, 500),
            ("📈 Betting edge tracker", "Line movement over time from crawled odds, surfacing value spots", 70, 500),
            ("🌍 Multi-language support", "UI in Spanish, French and Portuguese", 45, 1000),
            ("🗄 Shared database", "Optional cloud sync so teams share views", 120, 1000),
            ("📦 One-click installer", "A packaged app so non-developers can run it locally", 55, 1000)]
    body = ""
    for i, (name, desc, cost, unlock) in enumerate(rows):
        status = ("SHIPPED ✅" if name.startswith("🔔") else "FUNDED · BUILDING 🔨" if RAISED_USD >= unlock else f"~${cost}")
        color = "#059669" if RAISED_USD >= unlock else "#0c4a6e"
        body += (f'<tr style="background:{"#f8fafc" if i % 2 else "#fff"}"><td style="padding:10px 14px;font-weight:700;color:#1a1a2e">{name}</td>'
                 f'<td style="padding:10px 14px;color:#333">{desc}</td>'
                 f'<td style="padding:10px 14px;text-align:right;font-weight:700;color:{color};white-space:nowrap">{status}</td></tr>')
    return ('<div style="max-width:780px;margin:34px auto 0;padding:0 8px"><h2 style="font-size:1.15rem;font-weight:800;color:#1a1a2e;'
            'margin:0 0 6px;text-align:center">🗺 What is on the roadmap</h2>'
            '<p style="text-align:center;color:#666;font-size:.9rem;margin:0 0 14px">Estimated development cost. Supporters help decide the order: '
            'more interest means it ships sooner.</p><table style="width:100%;border-collapse:collapse;font-size:.92rem"><thead>'
            '<tr style="background:#1a1a2e;color:#fff"><th style="padding:10px 14px;text-align:left">Feature</th>'
            '<th style="padding:10px 14px;text-align:left">What it means for you</th>'
            '<th style="padding:10px 14px;text-align:right">Status</th></tr></thead><tbody>' + body + '</tbody></table></div>')


def render_support_page() -> None:
    st.html("""
    <div style="text-align:center;padding:36px 20px 8px">
      <div style="font-size:58px;margin-bottom:8px">💚</div>
      <h1 style="font-size:2.2rem;font-weight:900;color:#1a1a2e;margin:0 0 10px">Support TrulySporting</h1>
      <p style="color:#555;font-size:1.05rem;max-width:620px;margin:0 auto;line-height:1.75">
        A <strong>free, open-source</strong> sports analytics platform built by one developer. No paywalls, no data selling,
        and nothing locked behind a donation.</p></div>""")
    st.html(_progress_html())
    st.html(_tiers_html())
    st.html(_free_html())
    st.html(_where_html())
    st.html(_roadmap_html())
    st.html(_share_html())
    st.html(f"""
    <div style="max-width:780px;margin:30px auto 8px;background:linear-gradient(135deg,#1a1a2e,#16213e);border-radius:16px;
                padding:26px 28px;text-align:center">
      <div style="font-size:34px">🛠</div>
      <h2 style="font-size:1.1rem;font-weight:800;color:#fff;margin:6px 0">Prefer to code? Contribute.</h2>
      <p style="color:rgba(255,255,255,.75);font-size:.92rem;line-height:1.7;max-width:540px;margin:0 auto 14px">
        TrulySporting is fully open source. Every roadmap item is a viable pull request, and bug reports and ideas are welcome.</p>
      <a href="{REPO_URL}" target="_blank" rel="noopener noreferrer" style="display:inline-block;background:#16a34a;color:#fff;
         font-weight:800;font-size:14px;border-radius:50px;padding:10px 32px;text-decoration:none">⭐ View on GitHub →</a></div>
    <p style="text-align:center;font-size:11px;color:#9aa;margin:18px 0 0;line-height:1.8">
      100% of donations go directly to the developer. No obligation. TrulySporting stays free and open source.</p>""")


# ── the occasional nudge ─────────────────────────────────────────────────────

MIN_ACTIONS = 3        # real button presses before we ever ask
MIN_SECONDS = 150      # and at least this long into the visit
NUDGE_KEY = "_sn"


def support_nudge(trigger: str = "") -> None:
    """Call after a user finishes a meaningful action (ran a sync, a simulation...).

    Shows one small, friendly card per visit, only after the visitor has actually used the site for a few minutes,
    never blocks anything and never repeats.  Safe to call anywhere; it does nothing most of the time.
    """
    try:
        s = st.session_state.setdefault(NUDGE_KEY, {"n": 0, "t0": time.time(), "shown": False})
        s["n"] += 1
        if s["shown"] or s["n"] < MIN_ACTIONS or time.time() - s["t0"] < MIN_SECONDS:
            return
        s["shown"] = True
        st.html(
            '<div style="background:#f0fdf4;border:1px solid #bbf7d0;border-radius:12px;padding:12px 16px;margin:10px 0;'
            'display:flex;flex-wrap:wrap;align-items:center;gap:10px;justify-content:space-between">'
            '<div style="font-size:13px;color:#14532d;line-height:1.5;flex:1;min-width:220px">'
            '💚 <strong>Enjoying TrulySporting?</strong> It is free and built by one person. If it has been useful, '
            'a small tip keeps the live data and new features coming. This note only appears once per visit.</div>'
            f'<a href="{_cash(5)}" target="_blank" rel="noopener noreferrer" style="background:#15803d;color:#fff;font-weight:800;'
            'font-size:13px;border-radius:50px;padding:8px 18px;text-decoration:none;white-space:nowrap">Tip $5</a>'
            f'<a href="{_cash()}" target="_blank" rel="noopener noreferrer" style="color:#166534;font-weight:700;font-size:12px;'
            'text-decoration:none;white-space:nowrap">other amount</a></div>')
    except Exception:
        pass

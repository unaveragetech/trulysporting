import re

import theme


def test_dark_css_has_valid_selectors_and_palette():
    c = theme.css("dark")
    assert "--ts-bg:#0b101a" in c.replace(" ", "")
    # every attribute selector must have balanced quotes or the browser drops the rest of the stylesheet
    assert not [m for m in re.findall(r"\[style[^\]]*\]", c) if m.count('"') % 2 or m.count("'") % 2]
    assert "[style$=\"color:#1a1a2e\"]" in c  # catches a colour that ends an inline style


def test_auto_mode_uses_media_query_and_light_has_no_legacy_remap():
    assert "@media (prefers-color-scheme: dark)" in theme.css("auto")
    assert "[style$=" not in theme.css("light")


def test_league_accent_and_logo():
    assert theme.league_accent("football/nfl")[0] == "#1d4ed8"
    assert theme.league_accent("basketball/nba")[0] == "#ea580c"
    assert theme.LOGO_SVG.startswith('<img class="ts-logo"') and "data:image/svg+xml;base64," in theme.LOGO_SVG

import time

import support


def test_progress_and_next_goal_from_config(monkeypatch):
    monkeypatch.setattr(support, "RAISED_USD", 365)
    html = support._progress_html()
    assert "$365" in html and "SHIPPED" in html and "FUNDED" in html
    assert support._next_unfunded().startswith("$135")  # 500 - 365
    assert support._cash(5).endswith("/slightlysigh/5") or support._cash(5).endswith("$slightlysigh/5")


def test_nudge_waits_for_real_use_and_shows_once(monkeypatch):
    import streamlit as st
    shown = []
    state = {}
    monkeypatch.setattr(st, "session_state", state, raising=False)
    monkeypatch.setattr(st, "html", lambda h: shown.append(h))
    support.support_nudge("a")
    support.support_nudge("b")
    support.support_nudge("c")  # third action but visit is brand new -> still quiet
    assert not shown
    state[support.NUDGE_KEY]["t0"] = time.time() - support.MIN_SECONDS - 1
    support.support_nudge("d")
    assert len(shown) == 1 and "$5" in shown[0]
    for _ in range(5):
        support.support_nudge("e")
    assert len(shown) == 1  # never repeats within a visit

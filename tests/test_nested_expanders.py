import glob
import re

from streamlit.testing.v1 import AppTest


def test_nested_expanders_do_not_raise_and_keep_content():
    script = '''
import streamlit as st
import nestsafe
with nestsafe.expander("outer"):
    st.write("a")
    with nestsafe.expander("inner"):
        st.write("b")
        with nestsafe.expander("innermost"):
            st.write("c")
with nestsafe.expander("second outer"):
    with nestsafe.expander("inner again"):
        st.write("d")
'''
    at = AppTest.from_string(script).run(timeout=60)
    assert not at.exception
    assert [e.label for e in at.expander] == ["outer", "second outer"]       # only top-level ones are real expanders
    assert {"a", "b", "c", "d"} <= {m.value for m in at.markdown}           # nothing inside is lost


def test_nesting_state_resets_when_a_block_raises():
    import nestsafe
    try:
        with nestsafe.expander("x"):
            raise ValueError
    except ValueError:
        pass
    assert nestsafe.depth() == 0


def test_no_raw_st_expander_anywhere():
    bad = []
    for p in glob.glob("**/*.py", recursive=True):
        if p.startswith(("tests", "_patch")) or p == "nestsafe.py":
            continue
        for i, line in enumerate(open(p, encoding="utf-8", errors="ignore"), 1):
            if re.search(r"\bst\.expander\(", line) and not line.lstrip().startswith("#"):
                bad.append(f"{p}:{i}")
    assert not bad, bad

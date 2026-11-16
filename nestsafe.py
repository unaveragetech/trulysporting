"""An expander that is safe to use anywhere.

Streamlit raises "Expanders may not be nested inside other expanders".  Our pages build cards out of helper functions that each
open an expander, so what is nested depends on who calls whom.  ``expander`` keeps a per-script-run depth: the outermost one is a
normal expander; any inside it becomes a bordered section with a bold title (same content, always visible), so nothing can raise.
Use this instead of ``st.expander`` everywhere.
"""
import threading
from contextlib import contextmanager

import streamlit as st

_STATE = threading.local()


def depth() -> int:
    return getattr(_STATE, 'depth', 0)


@contextmanager
def expander(label: str, expanded: bool = False, **kw):
    if depth() > 0:
        with st.container(border=True):
            st.markdown(f'**{label}**')
            yield
        return
    _STATE.depth = 1
    try:
        with st.expander(label, expanded=expanded, **kw):
            yield
    finally:
        _STATE.depth = 0

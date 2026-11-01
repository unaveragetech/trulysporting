"""Helpers needed by modules that cannot import the sporting.py app script."""
from datetime import date, datetime, tzinfo
from typing import Tuple
from zoneinfo import ZoneInfo

import streamlit as st


def viewer_tz() -> tzinfo:
    """The browser's timezone; falls back to the server's."""
    try:
        if st.context.timezone:
            return ZoneInfo(st.context.timezone)
    except Exception:
        pass
    return datetime.now().astimezone().tzinfo


def viewer_today() -> date:
    return datetime.now(viewer_tz()).date()


def season_bounds(category: str, season_year: int) -> Tuple[str, str]:
    """(start, end) dates of an ESPN season year; mirrors SportsDB.season_bounds."""
    yr, cat = int(season_year), category.lower()
    if cat == 'football':
        return f'{yr}-08-01', f'{yr + 1}-03-01'
    if cat in ('basketball', 'hockey'):
        return f'{yr - 1}-09-01', f'{yr}-07-01'
    if cat == 'baseball':
        return f'{yr}-02-01', f'{yr}-11-30'
    return f'{yr - 1}-07-01', f'{yr}-07-01'

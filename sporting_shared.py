"""Helpers needed by modules that cannot import the sporting.py app script."""
from typing import Tuple


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

# Sports engine backtest

Trained on seasons through **2023**; every game below was **unseen** by the model (ratings use only pre-kickoff information).

## Held-out games (687 games, 400 simulations each)

| Metric | Sim (raw) | Sim (calibrated) | Sim + team-residual stage | Closing market |
|---|---|---|---|---|
| Winner accuracy | 62.9% | 64.0% | 65.1% | 67.8% |
| Brier score | 0.2267 | 0.2265 | 0.2224 | 0.2093 |
| Log loss | 0.6458 | 0.6453 | 0.6363 | 0.6057 |
| Margin MAE (pts) | 10.18 | 10.15 | 10.05 | 9.66 |
| Margin RMSE (pts) | 13.23 | 13.21 | 13.03 | 12.43 |
| Total MAE (pts) | 10.49 | 10.49 | 10.39 | 10.18 |

Margin correlation sim vs actual: 0.384; total correlation: 0.275. Bias (pred − actual) margin +0.24, total -0.52.

## By season

| Season | Games | Win acc | Margin MAE | Total MAE | Market win acc | Market MAE |
|---|---|---|---|---|---|---|
| 2024 | 285 | 66.7% | 10.16 | 9.97 | 70.5% | 9.70 |
| 2025 | 284 | 64.1% | 10.09 | 10.46 | 65.8% | 9.68 |
| 2026 | 118 | 63.6% | 9.71 | 11.24 | 66.1% | 9.52 |

## Win-probability calibration (held-out)

| Predicted | Actual | Games |
|---|---|---|
| 32.6% | 29.1% | 86 |
| 41.9% | 37.2% | 86 |
| 46.8% | 38.4% | 86 |
| 51.7% | 46.5% | 86 |
| 57.0% | 61.2% | 85 |
| 61.7% | 66.3% | 86 |
| 67.5% | 74.4% | 86 |
| 76.3% | 76.7% | 86 |

## Box-score realism (simulated vs real team stat lines, held-out)

| Stat | Sim avg | Real avg | Per-game correlation |
|---|---|---|---|
| plays | 60.82 | 60.79 | 0.08 |
| db | 35.49 | 36.74 | 0.22 |
| to | 1.04 | 1.10 | 0.08 |
| pen | 4.35 | 4.69 | 0.04 |

## Sim vs the closing spread (held-out)

Share of games where the side the sim preferred covered. 50% is break-even before vig; ~52.4% is break-even at −110.

| Edge threshold | Games | Sim side covered |
|---|---|---|
| edge>=0.0 | 678 | 50.4% |
| edge>=1.0 | 506 | 49.8% |
| edge>=2.0 | 347 | 49.6% |
| edge>=3.0 | 213 | 48.8% |
| edge>=4.0 | 113 | 50.4% |

## Fitted levers

```json
{
  "tuning": {
    "dev_scale": 1.0,
    "qb_scale": 1.0,
    "hfa": 1.4670236144963442,
    "eff": 1.3358912899700246,
    "rest_pts": 0.0
  },
  "ratings": {
    "half_life": 16.0,
    "carry": 0.8,
    "k_scale": 1.0,
    "qb_k_scale": 0.5,
    "qb_carry": 1.0,
    "coach_carry": 0.8,
    "base_half_life": 800.0
  },
  "residual": {
    "half_life": 15.0,
    "k": 120.0,
    "carry": 0.7,
    "gain": 2.4285771093663477
  }
}
```

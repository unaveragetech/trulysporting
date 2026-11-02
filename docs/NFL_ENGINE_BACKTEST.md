# Sports engine backtest

Trained on seasons through **2023**; every game below was **unseen** by the model (ratings use only pre-kickoff information).

## Held-out games (684 games, 400 simulations each)

| Metric | Sim (raw) | Sim (calibrated) | Sim + team-residual stage | Closing market |
|---|---|---|---|---|
| Winner accuracy | 63.0% | 64.2% | 65.6% | 67.7% |
| Brier score | 0.2258 | 0.2244 | 0.2221 | 0.2097 |
| Log loss | 0.6435 | 0.6403 | 0.6353 | 0.6066 |
| Margin MAE (pts) | 10.18 | 10.18 | 10.12 | 9.69 |
| Margin RMSE (pts) | 13.12 | 13.12 | 13.03 | 12.46 |
| Total MAE (pts) | 10.43 | 10.41 | 10.37 | 10.18 |

Margin correlation sim vs actual: 0.388; total correlation: 0.281. Bias (pred − actual) margin +0.26, total -0.34.

## By season

| Season | Games | Win acc | Margin MAE | Total MAE | Market win acc | Market MAE |
|---|---|---|---|---|---|---|
| 2024 | 285 | 69.1% | 10.09 | 9.99 | 70.5% | 9.70 |
| 2025 | 284 | 65.1% | 10.15 | 10.40 | 65.8% | 9.68 |
| 2026 | 115 | 58.3% | 10.11 | 11.24 | 65.2% | 9.66 |

## Win-probability calibration (held-out)

| Predicted | Actual | Games |
|---|---|---|
| 31.0% | 26.7% | 86 |
| 40.6% | 41.2% | 85 |
| 46.1% | 37.2% | 86 |
| 51.8% | 54.1% | 85 |
| 57.8% | 58.8% | 85 |
| 62.8% | 60.5% | 86 |
| 68.3% | 71.8% | 85 |
| 76.9% | 79.1% | 86 |

## Box-score realism (simulated vs real team stat lines, held-out)

| Stat | Sim avg | Real avg | Per-game correlation |
|---|---|---|---|
| plays | 60.91 | 60.80 | 0.07 |
| db | 36.35 | 36.75 | 0.20 |
| to | 1.07 | 1.11 | 0.09 |
| pen | 4.54 | 4.69 | 0.04 |

## Sim vs the closing spread (held-out)

Share of games where the side the sim preferred covered. 50% is break-even before vig; ~52.4% is break-even at −110.

| Edge threshold | Games | Sim side covered |
|---|---|---|
| edge>=0.0 | 675 | 49.3% |
| edge>=1.0 | 501 | 49.3% |
| edge>=2.0 | 342 | 50.3% |
| edge>=3.0 | 223 | 48.9% |
| edge>=4.0 | 121 | 55.4% |

## Fitted levers

```json
{
  "tuning": {
    "dev_scale": 0.9299113638324004,
    "qb_scale": 1.0,
    "hfa": 1.2768189495179079,
    "eff": 1.4208610348316297,
    "rest_pts": 0.0
  },
  "ratings": {
    "half_life": 16.0,
    "carry": 0.6,
    "k_scale": 0.25,
    "qb_k_scale": 2.0,
    "qb_carry": 0.85,
    "coach_carry": 0.8,
    "base_half_life": 800.0
  },
  "residual": {
    "half_life": 15.0,
    "k": 120.0,
    "carry": 0.7,
    "gain": 1.7220471470270706
  }
}
```

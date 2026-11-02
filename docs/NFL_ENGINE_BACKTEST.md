# Sports engine backtest

Trained on seasons through **2023**; every game below was **unseen** by the model (ratings use only pre-kickoff information).

## Held-out games (684 games, 400 simulations each)

| Metric | Sim (raw) | Sim (calibrated) | Sim + team-residual stage | Closing market |
|---|---|---|---|---|
| Winner accuracy | 61.3% | 62.6% | 64.9% | 67.7% |
| Brier score | 0.2253 | 0.2253 | 0.2221 | 0.2097 |
| Log loss | 0.6426 | 0.6422 | 0.6352 | 0.6066 |
| Margin MAE (pts) | 10.16 | 10.17 | 10.07 | 9.69 |
| Margin RMSE (pts) | 13.16 | 13.17 | 13.03 | 12.46 |
| Total MAE (pts) | 10.53 | 10.50 | 10.43 | 10.18 |

Margin correlation sim vs actual: 0.390; total correlation: 0.267. Bias (pred − actual) margin +0.31, total -0.32.

## By season

| Season | Games | Win acc | Margin MAE | Total MAE | Market win acc | Market MAE |
|---|---|---|---|---|---|---|
| 2024 | 285 | 68.4% | 10.12 | 9.94 | 70.5% | 9.70 |
| 2025 | 284 | 64.1% | 10.04 | 10.52 | 65.8% | 9.68 |
| 2026 | 115 | 58.3% | 10.02 | 11.44 | 65.2% | 9.66 |

## Win-probability calibration (held-out)

| Predicted | Actual | Games |
|---|---|---|
| 32.9% | 26.7% | 86 |
| 41.9% | 41.2% | 85 |
| 47.0% | 39.5% | 86 |
| 52.2% | 45.9% | 85 |
| 57.0% | 58.8% | 85 |
| 61.6% | 62.8% | 86 |
| 67.6% | 76.5% | 85 |
| 76.3% | 77.9% | 86 |

## Box-score realism (simulated vs real team stat lines, held-out)

| Stat | Sim avg | Real avg | Per-game correlation |
|---|---|---|---|
| plays | 60.89 | 60.80 | 0.08 |
| db | 36.35 | 36.75 | 0.20 |
| to | 1.06 | 1.11 | 0.09 |
| pen | 4.34 | 4.69 | 0.07 |

## Sim vs the closing spread (held-out)

Share of games where the side the sim preferred covered. 50% is break-even before vig; ~52.4% is break-even at −110.

| Edge threshold | Games | Sim side covered |
|---|---|---|
| edge>=0.0 | 675 | 52.0% |
| edge>=1.0 | 508 | 50.2% |
| edge>=2.0 | 361 | 49.9% |
| edge>=3.0 | 224 | 50.0% |
| edge>=4.0 | 116 | 50.0% |

## Fitted levers

```json
{
  "tuning": {
    "dev_scale": 1.1831853925388554,
    "qb_scale": 1.0,
    "hfa": 1.2884986852275904,
    "eff": 1.3938679824238414,
    "rest_pts": 0.0
  },
  "ratings": {
    "half_life": 32.0,
    "carry": 0.39999999999999997,
    "k_scale": 1.0,
    "qb_k_scale": 1.0,
    "qb_carry": 0.85,
    "coach_carry": 0.8,
    "base_half_life": 800.0
  },
  "residual": {
    "half_life": 15.0,
    "k": 120.0,
    "carry": 0.7,
    "gain": 2.2288458607436286
  }
}
```

# In-game win probability backtest

Held-out seasons after the calibrator's training window: 1795 checkpoint states from 359 games. Brier: lower is better; acc = share of states whose leader went on to win.

| checkpoint   |   states |   engine brier |   engine acc |   engine+cal brier |   engine+cal acc |   nflfastR brier |   nflfastR acc |
|:-------------|---------:|---------------:|-------------:|-------------------:|-----------------:|-----------------:|---------------:|
| 300          |      359 |         0.0914 |        0.877 |             0.0914 |            0.877 |           0.0901 |          0.877 |
| 900          |      359 |         0.1265 |        0.821 |             0.126  |            0.816 |           0.1288 |          0.824 |
| 1800         |      359 |         0.1619 |        0.768 |             0.1587 |            0.774 |           0.1637 |          0.765 |
| 2700         |      359 |         0.2087 |        0.698 |             0.2016 |            0.693 |           0.2186 |          0.648 |
| 3300         |      359 |         0.2161 |        0.659 |             0.2067 |            0.687 |           0.2346 |          0.606 |
| all          |     1795 |         0.1609 |        0.765 |             0.1569 |            0.769 |           0.1672 |          0.744 |

Calibrator (per clock checkpoint): a=['-0.18', '-0.22', '-0.24', '-0.14', '-0.11'], b=['0.74', '0.86', '0.97', '0.95', '0.81'], market weight c=['0.79', '0.72', '0.72', '1.05', '1.47']
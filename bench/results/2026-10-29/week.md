| endpoints | round | checkpoint age | helios sync s | helios CPU s | helios RSS MB | leanlight sync s (net / verify) | leanlight CPU s | leanlight RSS MB | = helios at block N | = endpoint at N | leanlight errors | helios not at N |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| nimbus+publicnode | 0 | 6 periods | 2.29 | 0.17 | 24 | 1.10 (0.68 / 0.42) | 2.56 | 82 | 11/11 | 14/14 | 0 | 3 |
| nimbus+publicnode | 1 | 6 periods | 0.97 | 0.18 | 24 | 1.29 (0.65 / 0.64) | 2.63 | 82 | 11/11 | 14/14 | 0 | 3 |
| nimbus+publicnode | 2 | 6 periods | 0.82 | 0.13 | 23 | 4.48 (4.02 / 0.46) | 2.56 | 82 | 0/0 | 14/14 | 0 | 14 |

Read set of 14 reads, median over 3 rounds:

| leanlight (one batch + checks) ms | helios, one call each ms | helios, one batch ms |
|---|---|---|
| 87 | 447 | 1 |

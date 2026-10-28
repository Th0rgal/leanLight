| endpoints | round | checkpoint age | helios sync s | helios CPU s | helios RSS MB | leanlight sync s (net / verify) | leanlight CPU s | leanlight RSS MB | = helios at block N | = endpoint at N | leanlight errors | helios not at N |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| nimbus+publicnode | 0 | 0 periods | 0.68 | 0.07 | 22 | 0.28 (0.18 / 0.10) | 0.80 | 79 | 11/11 | 14/14 | 0 | 3 |
| nimbus+publicnode | 1 | 0 periods | 1.22 | 0.12 | 24 | 0.29 (0.19 / 0.10) | 0.92 | 79 | 9/9 | 14/14 | 0 | 5 |
| nimbus+publicnode | 2 | 0 periods | 0.76 | 0.16 | 24 | 0.29 (0.18 / 0.11) | 0.82 | 82 | 8/8 | 14/14 | 0 | 6 |
| nimbus+drpc | 0 | 0 periods | 2.44 | 0.20 | 24 | 0.69 (0.53 / 0.15) | 1.18 | 82 | 13/13 | 14/14 | 0 | 1 |
| nimbus+drpc | 1 | 0 periods | 1.03 | 0.15 | 24 | 0.28 (0.18 / 0.10) | 1.00 | 82 | 13/13 | 14/14 | 0 | 1 |
| nimbus+drpc | 2 | 0 periods | 1.08 | 0.14 | 24 | 0.29 (0.18 / 0.11) | 1.09 | 82 | 13/13 | 14/14 | 0 | 1 |
| lodestar+publicnode | 0 | 0 periods | 0.56 | 0.09 | 24 | 0.28 (0.15 / 0.12) | 0.80 | 82 | 0/0 | 14/14 | 0 | 14 |
| lodestar+publicnode | 1 | 0 periods | helios not ready after 120.0 s: eth_bloc | 0.00 | 0 | 0.26 (0.16 / 0.10) | 0.80 | 82 | 0/0 | 0/0 | 0 | 0 |
| lodestar+publicnode | 2 | 0 periods | helios not ready after 120.0 s: eth_bloc | 0.00 | 0 | 0.35 (0.19 / 0.16) | 0.82 | 82 | 0/0 | 0/0 | 0 | 0 |

Read set of 14 reads, median over 7 rounds:

| leanlight (one batch + checks) ms | helios, one call each ms | helios, one batch ms |
|---|---|---|
| 388 | 1732 | 1 |

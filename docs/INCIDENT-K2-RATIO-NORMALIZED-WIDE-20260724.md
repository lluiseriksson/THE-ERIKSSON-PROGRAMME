# Incident — ratio-factorized K2 remains too wide after normalization (2026-07-24)

An exploratory (non-preregistered) normalization used the exact ratio
factorization for the numerator and the independent nominal `KD` series for
the denominator.  At `t=2.90`, `delta=[0,1/80]`, 140-bit Arb:

| spatial grid | `KD_0` enclosure | `Y` lane radius | order-3 coefficient radius |
|---:|---|---:|---:|
| 96 | `[3 +/- 0.633]` | `0.406` | `441.42` |
| 192 | `[3 +/- 0.525]` | `0.198` | `115.14` |

The target fourth-coefficient budget at this stress cell is approximately
`Theta_3=2.85`; the order-3 interval is therefore not close to a terminal
sign margin.  This confirms that finer spatial partitioning alone is not a
closure proof.  The computation was exploratory, has no manifest, and carries
no K2/G2/G6 or manuscript promotion.

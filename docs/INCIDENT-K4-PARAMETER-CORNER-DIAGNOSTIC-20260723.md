# K4 parameter-corner diagnostic — 2026-07-23

**Status:** diagnostic only; no K4, S1'''/S2''', G2, or G6 promotion.

The low-z weighted candidate was evaluated independently at the centre and
four nearby parameter points.  The fixed spatial budget was 4096 cells and
only the main ``nuD_main`` lane was used.  The reproducible driver is
`scripts/probe_surface_k4_lowz_parameter_corners.py`.

The resulting absolute totals and budget fractions were:

| point | `nuD_main` | fraction |
|---|---:|---:|
| centre `(δ,t)=(1/15,2.9)` | 1.06036282737 | 1.12661930893 |
| `δ=0.06665` | 1.06033240006 | 1.12658698037 |
| `δ=0.0666833333333333` | 1.06039325281 | 1.12665163549 |
| `t=2.8999` | 1.06020285392 | 1.12644933958 |
| `t=2.9001` | 1.06052283227 | 1.12678931169 |

These pointwise values vary by only about `3.4e-4` in fraction across the
tested offsets, while a direct interval hull over a comparable tiny box had
previously produced a fraction near `31`.  This is consistent with interval
dependency/wrapping dominating the hull failure, but it is not a proof: the
4096-cell partition is not the 16384-cell production partition, and no
derivative enclosure has been computed.

The next admissible experiment is therefore a centred parameter-jet or
regular-ball majorant on the frozen 16384-cell partition.  Acceptance must use
an explicit value-mean budget: if `m=1-0.9846732229353782` is the production
margin, certify

```text
rho_delta * sup|∂_delta nuD_main|
+ rho_t * sup|∂_t nuD_main| < m - safety_margin.
```

Until those derivative/tail bounds and an independent replay exist, this
incident remains a blocker, not evidence for the theorem.

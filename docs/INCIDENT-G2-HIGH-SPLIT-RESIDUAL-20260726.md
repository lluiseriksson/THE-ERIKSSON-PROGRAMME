# G2 high-split residual failure — 2026-07-26

## Scope

This is a diagnostic record for the exact residual beta interval
`[3409/32,6819/64]` inside the current authoritative G2 gap
`[3409/32,1000/9]`.  It is not a theorem certificate and carries no G2/G6
promotion.

## Reproduction

The registered high-order split driver was run with the unchanged contract
(180-bit Arb, beta Taylor order 30, t order 37, `CWIN=3/2`, minimum t width
`1/100000`):

```text
python scripts/run_surface_scaled_bulk_cwin3p2_high_split.py \
  --unit gap106p53125_106p546875 \
  --lo 3409/32 --hi 6819/64
```

After 537 seconds the run failed at the contract's minimum width:

```text
RuntimeError: bulk failure near t=3.0594051819551003
```

The complete traceback is retained in
`scripts/surface_scaled_bulk_gap106p53125_106p546875_split.failed.txt`.

## Local width probe

At the failing t-cell, direct Arb evaluation with the same orders gives an
upper bound that changes sign when the beta box is subdivided:

| beta width | upper bound sign |
|---:|---:|
| `1/256` | positive (`~5.78e-112`) |
| `1/512` | negative (`~-5.54e-111`) |
| `1/1024` | negative (`~-9.95e-111`) |

This shows that finer beta subdivision may reduce interval loss, but it is not
a closure: the full t cover, all beta cells, production/replay equality, and
the relay contract are still missing.  The number of cells required over the
remaining gap would also be large, so no promotion is made from this probe.

## Decision

The split route remains a candidate engineering direction only.  The
authoritative status stays `G2=BLOCKED`, `G6=BLOCKED`, and the manuscript stays
`DO_NOT_SUBMIT`.

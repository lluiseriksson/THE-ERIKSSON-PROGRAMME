# Low-z dispatcher and absolute weighted smoke — 2026-07-23

## Result

An isolated candidate route combines the already-regressed entire-series
low-z Bessel majorant (`surface_bessel_entire_lowz.py`) with the exact positive-
`z` recurrence.  At the registered stress point

```text
delta = 1/15,  t = 29/10,
seed grid = 4,  adaptive terminal cells per lane = 16384,
Arb precision = 100 bits,  low-z series terms = 96
```

the literal partition sums are formed from `abs_upper()` per cell, so signed
cell cancellation is impossible.  All seven fractions are strictly below
one; the worst is

```text
nuD_main = 0.9846732229353782...
```

The production and replay transcripts are byte-identical and pass the
independent validator.  The manifest is
`run-manifests/surface-k4-lowz-dispatch-weighted-smoke-20260723.json`.

## Scope boundary

This is a single stress point with an isolated dispatcher.  It does **not**
provide the global delta/t partition, the outer-tail or moving-boundary
charges, the regular-ball overlap, or the literal global S1'''/S2''' union.
It therefore remains quarantined and carries no K4, G2, or G6 promotion.

The first 4096-cell run was intentionally rejected: it accumulated signed
intervals and left `nuD_main` at `1.1266193...` of budget.  The driver was
corrected to accumulate per-cell absolute upper bounds before the 16384-cell
production/replay pair was accepted.  This correction is recorded here to
prevent the earlier false-green interpretation from returning.

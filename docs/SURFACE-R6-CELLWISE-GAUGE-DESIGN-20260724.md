# R6 cellwise gauge diagnostic (2026-07-24)

This isolated probe applies the exact determinant gauge before spatial-cell
aggregation.  It is intended to test the structural repair identified in
`SURFACE-R6-GAUGE-CANCELLATION-DESIGN-20260724.md`, not to create evidence for
K2 or `(H_tail)`.

The probe compares the fifth normalized coefficient from the raw cell sum and
the cellwise-gauged sum on a born `t` box.  It records the exact scalar
`lambda`, an identity-difference check, and both interval radii.  The annulus,
outer tail, Bessel companion remainder, and S1'''/S2''' accounting are absent;
all output must remain `DESIGN ONLY`.

The first current-hash run on born box 0 (`t=[0,1/50]`) at grid 64 gave

```text
KD0             [1 +/- 0.482]
RAW_Y5          [+/- 1.85e5]
GAUGED_Y5       [+/- 1.95e5]
IDENTITY_DIFF   [+/- 3.80e5]
```

The identity check contains zero, but the fixed scalar gauge increased rather
than reduced the interval radius.  This falsifies the simplest aggregate
implementation of the proposed repair; a viable successor must use a paired
double-integral or a genuinely signed cell partition, not merely subtract one
global lambda after summing.

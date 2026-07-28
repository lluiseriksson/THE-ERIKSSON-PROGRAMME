# Incident — delta-zero Y assembler applied `H0/K0` twice

**Date:** 2026-07-28

**Impact:** every endpoint number produced through
`surface_remainder_delta0_series_design.assemble_y_derivatives` used the
wrong normalization.  No positive-delta order-eight transcript is affected.

The dimensionless Gaussian calculation removes the leading kernel constants.
For those dimensionless moments,

```text
H0/K0 = 1/(8c),
Y = B_dimensionless/(2c delta KD_dimensionless^2).
```

The executable endpoint moment integrator, however, stores the *full*
moments, including both `K0` and `H0`.  Therefore

```text
B_full/KD_full^2
  = (H0/K0) B_dimensionless/KD_dimensionless^2,
```

and the physical target is

```text
Y = 4 B_full/(delta KD_full^2).
```

The historical assembler used `B_full/(2c delta KD_full^2)`, applying
`H0/K0` a second time.  Its output was smaller than the physical target by
the exact factor `8c`.

The absolute normalization is independently anchored by
`surface_remainder_delta0_first_coefficient.py`: exact symbolic Gaussian
moments give

```text
Y(0,t) = (4c^2-1)/(8c^3)
```

from the dimensionless formula above, together with the registered closed
forms for the next two coefficients.  Thus the correction is not inferred
only by comparing two numerical quadratures or by taking the incident report
itself as an oracle.

The assembler is corrected and regression-tested.  All earlier endpoint
design values and any manifest whose dependency hash names the old file are
quarantined pending regeneration.  This incident does not alter the
positive-delta S1/S2 delta-eight campaign, whose independent assembler has
always used `4 B/(delta^4 KD^2)`.

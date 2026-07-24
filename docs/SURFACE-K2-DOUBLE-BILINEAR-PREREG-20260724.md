# K2 double-bilinear identity microtest — preregistration (2026-07-24)

## Scope

This is a cheap design audit for the K2 endpoint lane.  It does not certify
the endpoint, the companion remainder, the outer tails, the relay, or any
part of the Surface Theorem.  It exists to prevent the cell-diagonal quantity
from being mistaken for the production bilinear.

## Objects under test

For spatial cells `c`, let `M_c=(KD_c,KF_c,HDD_c,HDF_c)` be the nominal cell
moments.  The production object is

```
B_prod = (sum_c KD_c)(sum_c HDF_c) - (sum_c KF_c)(sum_c HDD_c),
```

whereas the existing signed probe computes

```
B_diag = sum_c (KD_c*HDF_c - KF_c*HDD_c).
```

The two expressions coincide only under an additional identity; no such
identity is assumed here.

## Frozen microtest

Run `scripts/probe_surface_remainder_double_bilinear_identity.py` with Arb
precision 120, midpoint spatial samples on a `2x2` grid, and

```
t in {2.90, 3.13},  delta in {0, 1/1000, 1/80}.
```

The test records the coefficient-0 difference `B_diag-B_prod`.  Acceptance is
diagnostic only:

* at `delta=0`, both expressions must contain zero (the exact endpoint
  cancellation);
* at `delta=1/1000` and `delta=1/80`, at least one case must show a nonzero
  midpoint difference.  If all differences vanish, stop and audit the
  implementation before any production run.

The output is a falsification record, not a theorem certificate.  In
particular, no result from the diagonal probe may be promoted to K2 evidence.

## Next gate (not run here)

Only after this identity audit passes may a centered-in-`delta` or explicitly
factorized double-bilinear implementation be designed.  It must preserve the
full product-of-sums object and separately charge companion and outer-tail
errors.

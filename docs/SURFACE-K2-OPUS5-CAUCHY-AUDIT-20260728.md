# K2 Opus 5 Cauchy architecture audit

**Date:** 2026-07-28

**State:** independent design consultation plus local verification; no K2,
K4, S1/S2, gate, or manuscript promotion.

Claude Opus 5 Max was invoked with the explicitly selected local profile
`masterythief`, no tools, `--model claude-opus-5`, and `--effort max`.
The JSON reports `is_error=false` and `modelUsage` contains exactly
`claude-opus-5` as the principal model, with a small auxiliary Haiku entry.
The raw prompt and JSON are committed beside this note.

## Independently accepted

For a holomorphic `Y` with `|Y|<=M` on `|delta|=rho`, subtraction of the
exact head through order five gives

```text
|Y(delta)-sum_{k=0}^5 Y_k delta^k|
  <= M*q^6/(1-q),  q=delta_max/rho.
```

This is the standard Cauchy coefficient estimate and requires no derivative
of an absolute-value bound.

The suggested fixed-square radius `rho=7/1000` was checked independently,
not accepted from the model.  The Arb certificate
`certify_surface_k2_fixed_square_complex_geometry.py` proves strict nominal
floors for `D`, the square-root radicand/branch, `1+root`, and both finite
companion polynomials on `[0,12]^2`.

The model also highlighted the zero-order companion cancellation.  The exact
repository coefficients independently prove
`A_N(0)=B_N(0)=1` and
`B_N*D-2*root*A_N` divisible by `delta` for every truncation.  This is
executable in `verify_surface_k2_companion_zero_cancellation.py`.

## Not accepted / still blocked

- The statement that the tail is “not hard” is a heuristic.  No circle
  supremum `M` has been supplied.
- The claim that `M` needs no complex integration is valid only for the fixed
  square after suitable pointwise majorants.  The repository's moving
  exterior is not yet shown to define a holomorphic complex-delta integral;
  complex sine growth can destroy the real Gaussian tail argument.
- The true Bessel companion remainder is not covered by the finite-polynomial
  zero-freeness certificate.
- The proposed weighted affine `L^2` projection may improve the real
  covariance enclosure, but no positive cell-moment-matrix lower bound or
  Hessian residual certificate has been built.

Thus the consultation identifies a viable *fixed-square* Cauchy component,
not a complete K2 remainder.  A terminal route must either prove a separate
real-axis exterior Taylor remainder or construct a genuine holomorphic
exterior majorant and true-companion circle bound.

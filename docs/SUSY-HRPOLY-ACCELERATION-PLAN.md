# SUSY-STYLE CANCELLATION PLAN FOR `hRpoly`

**Date:** 2026-06-19.  **Status:** algebraic Ward-to-polymer bridge CLOSED.

This plan records the useful part of the supersymmetry audit without changing
the mathematical target.  Clay asks for pure four-dimensional Yang--Mills, not
a supersymmetric theory.  Supersymmetry is therefore **not** imported as a
physical shortcut.  The potentially useful idea is narrower:

`cancel Q-exact local contributions before applying norms`.

The repository's current `hRpoly` consumer needs a scalar activity profile such
as

`exp(t) * ‖z(X)‖ * exp(|X|) ≤ A * q^(d_M(X)+1)`.

A cohomological/Ward layer can feed that consumer if a local activity has a
decomposition

`H_X = Q B_X + R_X`

and the integration functional satisfies an exact or approximate Ward identity.
Then

* exact Ward: `expect (Q B_X) = 0`, so `z(X) = expect R_X`;
* approximate Ward:
  `‖expect (Q B_X)‖ ≤ defect * ‖B_X‖`, so
  `‖z(X)‖ ≤ defect * ‖B_X‖ + ‖expect R_X‖`.

The rule is: **integrate/cancel first; take absolute values afterwards.**

## Closed substrate

`YangMills/SUSY/WardComplex.lean` now provides the abstract interface

* `ApproxWardComplex`;
* `expect_Q_eq_zero_of_defect_eq_zero`;
* `expect_eq_expect_remainder_of_defect_eq_zero`;
* `expect_decomposition_bound`;
* `expect_decomposition_profile_bound`;
* `expect_profile_bound_of_exact_ward`.

The profile theorem states that if every activity decomposes as
`H X = Q(B X) + R X`, and `B` and `expect R` obey the same profile `w X`, then
the integrated activity obeys that profile with amplitude
`defect * Bamp + Ramp`.

`YangMills/RG/ActivityLimit.lean` also provides
`activity_profile_bound_of_tendsto`: a pointwise limit of uniformly
profile-bounded complex activities obeys the same profile bound.  This is the
abstract consumer for decoupling or regulator-removal arguments.

`YangMills/SUSY/WardPolymer.lean` now connects the Ward layer to the literal
`Ω`-active with-holes skeleton-tail consumer:

* `norm_finset_sum_expect_Q_le` proves the finite defect-sum estimate
  `‖∑ expect(Q B_k)‖ ≤ ∑ defect_k * ‖B_k‖`;
* `wardActivity` packages the integrated complex polymer activity
  `X ↦ expect(H_X)`;
* `wardActivity_metric_bound_of_decomposition` and
  `wardActivity_metric_bound_of_exact` produce the pointwise modified-metric
  activity bound from approximate/exact Ward decompositions;
* `omegaClusterSkeletonRemainderSum_tsum_le_of_ward` and
  `omegaClusterSkeletonRemainderSum_tsum_le_of_exact_ward` feed those
  Ward-cancelled activities directly into
  `omegaClusterSkeletonRemainderSum_tsum_le_metric_bound`.

## What remains open

The following are **not** proved by this substrate:

* a lattice `N=1` super-Yang--Mills construction;
* Grassmann/Berezin integration;
* a Pfaffian/determinant cancellation theorem;
* a heavy-gluino decoupling theorem to pure Yang--Mills;
* the Yang--Mills fluctuation-integral activity bound `hRpoly`;
* continuum limit or OS/Wightman reconstruction.

## Next useful bricks

1. Construct the model-specific decomposition
   `raw X = Q (primitive X) + remainder X` for the actual fluctuation
   integral.
2. Bound the regulator/Ward defect and primitive norm in the same
   modified-metric profile consumed by `WardPolymer`.
3. Bound the surviving cohomological remainder.
4. `ActivityLimit.lean` telescopic variant: if
   `‖z_{n+1}(X)-z_n(X)‖ ≤ B_n * q^(d X+1)` and `∑ B_n < ∞`, prove the limiting
   activity obeys `(A + ∑ B_n) * q^(d X+1)`.
5. A finite super-Gaussian/Berezin toy model can be useful only if it produces
   one of the three concrete inputs above; it is not a physical shortcut to
   pure Yang--Mills by itself.

**Honest Clay scope:** this may reorganize the lattice `hRpoly` proof
obligation into smaller Ward-defect/cohomology estimates.  It does not by
itself move the continuum Clay problem; M4/M5 remain untouched.

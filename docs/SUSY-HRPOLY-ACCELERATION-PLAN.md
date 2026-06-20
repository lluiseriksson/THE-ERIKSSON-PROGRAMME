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
It also provides the telescopic variant
`activity_profile_bound_of_tendsto_telescope`: if
`‖z_{n+1}(X)-z_n(X)‖ ≤ B_n * profile X` and `∑' B_n ≤ S`, then the limiting
activity has amplitude `amp + S`.

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

`YangMills/SUSY/FiniteBerezin.lean` now starts the finite Berezin substrate:

* `finiteExteriorBasis n` is the canonical basis of the complex exterior
  algebra over `Fin n → ℂ`, indexed by subsets of `Fin n`;
* `finiteBerezinTop n` is the coefficient functional of the top exterior
  monomial;
* `finiteBerezinTop_basis`, `finiteBerezinTop_top_basis`, and
  `finiteBerezinTop_basis_of_ne_top` prove the usual algebraic rule: top
  monomial integrates to `1`, all other basis monomials integrate to `0`;
* `finiteBerezinTop_one_of_pos` records that constants have zero Berezin
  integral in positive fermionic dimension;
* `finiteBerezinTop_algebraMap_of_pos` packages the same rule for arbitrary
  scalar constants;
* `FiniteBerezinExactWard`, `finiteBerezin_expect_Q_eq_zero`, and
  `finiteBerezin_eq_expect_remainder_of_exactWard` give the exact algebraic
  Ward-cancellation rule for this concrete finite Berezin functional.
* `finiteBerezinWeighted n weight` is the algebraic weighted Berezin
  functional `F ↦ finiteBerezinTop n (weight * F)`;
* `finiteBerezinWeighted_one` proves that unit weight recovers
  `finiteBerezinTop`;
* `FiniteBerezinWeightedExactWard`,
  `finiteBerezinWeighted_expect_Q_eq_zero`, and
  `finiteBerezinWeighted_eq_expect_remainder_of_exactWard` give the same exact
  cancellation rule for weighted finite Berezin integrals.
* `finiteBerezinTopWeight n a = 1 + a • topBasis` is the first concrete
  top-degree density seed; in positive fermionic dimension,
  `finiteBerezinWeighted_topWeight_one_of_pos` integrates `1` to `a`, and
  `finiteBerezinWeighted_topWeight_algebraMap_of_pos` integrates a scalar
  constant `z` to `a * z`.
* `finiteExteriorBasis_singleton_mul_self` proves the generator-level
  Grassmann nilpotence rule `e_i * e_i = 0` for every finite exterior basis
  generator.
* `finiteExteriorBasis_mul_of_not_disjoint` and
  `finiteBerezinTop_basis_mul_of_not_disjoint` provide the corresponding
  monomial and Berezin-top-coefficient zero rules whenever two basis monomials
  share a generator.  The disjoint `powersetCard` wrapper keeps the
  orientation sign explicit for later Pfaffian work, and
  `finiteBerezinTop_powersetCard_mul_of_disjoint_top` extracts exactly that
  sign when the disjoint union is top-degree.
* The weighted top-density seed is now computed on basis monomials:
  `finiteBerezinWeighted_topWeight_basis_empty_of_pos`,
  `finiteBerezinWeighted_topWeight_top_basis_of_pos`, and
  `finiteBerezinWeighted_topWeight_basis_of_nonempty_ne_top` isolate the
  empty, top, and nonempty non-top cases in positive fermionic dimension.
* The same seed is also available as a global coefficient functional:
  `finiteBerezinWeighted_topWeight_eq_top_add_empty_of_pos` says that
  integration against `1 + a • topBasis` equals top-coefficient extraction plus
  `a` times empty-coefficient extraction.  This is the finite linear API needed
  before expanding honest Gaussian/Pfaffian weights.
* Product-facing top-density rules are now available too:
  `finiteBerezinWeighted_topWeight_basis_mul_of_not_disjoint` kills products
  with repeated generators, while the disjoint cardinality-indexed rules
  extract the explicit orientation sign in the positive top-degree case and
  give zero in the nonempty non-top case.

This is the first concrete finite Grassmann/Berezin layer underneath the
abstract Ward interface.  The weighted functional is the algebraic slot into
which a finite Gaussian Berezin weight can later be inserted.  It is not yet a
constructed Gaussian Berezin weight with covariance, a Pfaffian/determinant
cancellation identity, or a physical SUSY/YM construction.

## What remains open

The following are **not** proved by this substrate:

* a lattice `N=1` super-Yang--Mills construction;
* Gaussian Berezin integration with a covariance and determinant/Pfaffian
  evaluation;
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
4. A finite super-Gaussian/Berezin toy model can be useful only if it produces
   one of the three concrete inputs above; it is not a physical shortcut to
   pure Yang--Mills by itself.

**Honest Clay scope:** this may reorganize the lattice `hRpoly` proof
obligation into smaller Ward-defect/cohomology estimates.  It does not by
itself move the continuum Clay problem; M4/M5 remain untouched.

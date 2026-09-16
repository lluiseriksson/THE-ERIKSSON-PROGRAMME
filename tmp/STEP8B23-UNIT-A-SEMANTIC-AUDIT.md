# Step 8b.23 Unit A — static semantic audit

Status: **STATIC ONLY — NOT COMPILER-VERIFIED**.

Scope:

- `BalabanCMP89CenteredBrillouinAffineSlice.draft.lean`
- `BalabanCMP89CenteredUnitCubeTorusQuotient.draft.lean`
- `BalabanCMP89CenteredTorusFourierPhase.draft.lean`
- `BalabanCMP89NormalizedBrillouinToTorusMeasure.draft.lean`

This audit checks the four source-facing acceptance gates for Unit A. It does
not assert elaboration, axiom cleanliness, a Green-function identity, a `B0`
bound, window-15 attainment, or any terminal field.

## Gate A1 — centered fundamental domain and quotient

**PASS (static).**

- `CMP89CenteredUnitInterval` is the closed interval
  `[-1/2, 1/2]`, used for the topological quotient.
- `cmp89CenteredUnitCube_factorsThrough_of_faceSeam` constructs
  `Function.FactorsThrough` internally from the coordinate face-seam laws.
  No preselected factorization witness is accepted by the public lift.
- `cmp89CenteredUnitCubeLift` consumes continuity plus the coordinate seam and
  builds the quotient lift internally.
- The measure transport deliberately uses the half-open representative
  `(−1/2, 1/2]` (`Set.Ioc`), avoiding double counting of the identified face.

Live hypotheses are the intended ones: continuity of the lifted function and
the coordinate seam. There is no free periodic function or free
`FactorsThrough` input.

## Gate A2 — exact physical-to-torus measure transport

**PASS (static).**

- `cmp89OneDimensionalNormalizedBrillouinMeasure` contains exactly one scalar
  `(2*pi)^-1` multiplying the physical interval measure.
- `measurePreserving_cmp89NormalizedBrillouinScale` transports this normalized
  measure to the unit half-open fundamental-domain measure.
- `measurePreserving_cmp89PhysicalBrillouinToUnitAddCircle` composes scaling,
  quotient, negation, and translation. It does not assume a symmetry of the
  physical integrand.
- `measurePreserving_cmp89PhysicalBrillouinToUnitAddTorus` takes the finite
  product in four coordinates.

The use of closed `Icc` for topology and half-open `Ioc` for measure is
intentional and separated by the API.

## Gate A3 — normalization `(2*pi)^-4` exactly once

**PASS (static).**

- `cmp89Measure_pi_const_smul` proves that a constant scalar in every factor
  becomes `c ^ card` in the finite product.
- `cmp89NormalizedBrillouinProductMeasure_eq` specializes this to `Fin 4`,
  yielding `ENNReal.ofReal ((2*pi)^-1) ^ 4` times the repository's literal
  four-dimensional Brillouin measure.
- `integral_unitAddTorus_eq_cmp89NormalizedBrillouin` rewrites that scalar to
  the existing source definition
  `cmp89Eq249NormalizedFourDimensionalBrillouinIntegral`, whose literal
  coefficient is `((2*pi)^4)^-1`.

No second Jacobian or compensating cardinality appears in the endpoint.

## Gate A4 — negative momentum and Fourier sign

**PASS (static).**

- `cmp89Eq248NegativeTwoPiTorusMomentum` names the negative torus momentum.
- `cmp89Eq248NegativeTwoPiTorusMomentum_physicalBrillouin` identifies it with
  the repository's literal translated physical Brillouin parameter.
- `cmp89CenteredTorus_mFourier_neg_eq_physicalPhase` uses the literal Mathlib
  coefficient `UnitAddTorus.mFourier (-n)`.
- The affine residue identity and the product-phase theorem keep the sign
  visible; no unnamed symmetry under `n -> -n` is used.

## Static verdict

Unit A is source-faithful at the level of public contracts and definitions.
All four acceptance gates pass statically. Promotion remains blocked on Lean
elaboration and axiom audit in the sanctioned remote validation path.


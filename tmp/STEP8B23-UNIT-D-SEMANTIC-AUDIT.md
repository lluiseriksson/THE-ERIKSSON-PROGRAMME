# Step 8b.23 Unit D — static semantic audit

Status: **STATIC ONLY — NOT COMPILER-VERIFIED**.

Scope:

- `BalabanCMP89Eq248GreenOneCoordinateContourShift.draft.lean`
- `BalabanCMP89Eq248GreenProductContourTelescope.draft.lean`
- `BalabanCMP89Eq248MassUniformGreenBound.draft.lean`
- `BalabanCMP89Eq248MassUniformNormalizedGreenBound.draft.lean`

## Gate D1 — one-coordinate shift uses the proved seam and full strip

**PASS (static).**

The one-coordinate theorem constructs the vertical-rectangle boundary
identity from the Green-specific physical fine-lattice seam. Holomorphy on
the rectangle is derived from the complete-polydisc producer after checking
the real Brillouin bound and all coordinate imaginary bounds. No caller
supplies a slice equality, boundary cancellation, or holomorphic family.

The shift height is an explicit `eta` with `abs eta <= rho`; therefore both
endpoint-dependent signs are covered without asserting a single globally
valid contour direction.

## Gate D2 — four-coordinate telescope is internal

**PASS (static).**

- Every partial stage is proved integrable from continuity on the compact
  physical cube.
- Each stage transition invokes the Green-specific one-coordinate theorem.
- The four transitions are instantiated explicitly at coordinates 0–3.
- The endpoint is the fully signed contour determined by the literal
  fine-lattice displacement.

No integrability premise, per-coordinate contour equality, or endpoint
family is accepted from the caller.

## Gate D3 — pointwise Green majorant keeps its physical accounting

**PASS (static).**

- Noncentral aliases retain two inverse radial powers.
- Redistribution uses the explicit source choice `alpha = -1`, hence the
  summable exponent `cmp89Eq251AliasSeriesExponent 4 (-1)`.
- The complete alias contribution is bounded by the one-dimensional tsum to
  the fourth power; no finite-alias cardinality factor is inserted.
- Every alias phase remains inside the finite sum until its exact signed
  contour norm is used.
- The zero alias is separated and the central/noncentral numerator
  decomposition is stated as an exact equality.
- The denominator reciprocal is supplied by the named joint central window,
  not by a free `B0` hypothesis.

The resulting amplitude is the explicit expression
`cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho`. It is a
pointwise Fourier-integrand constant, not yet the regional/operator `B0`.

## Gate D4 — source normalization cancels volume exactly

**PASS (static).**

`cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_eq_signed_massUniform_draft`
combines the literal source-normalized Green definition with the internal
four-stage contour equality. The final norm theorem applies the normalized
integral majorant, so the `(2*pi)^-4` coefficient cancels the physical cube
volume exactly. No additional volume or Jacobian constant appears.

## Live boundary conditions

The conclusions remain conditional on the common scalar package:

- `rho * exp rho <= 1/6`;
- the uniform noncentral-radius condition;
- the central stabilized window;
- `mass^2 <= 1`;
- `0 <= a`, `0 <= rho`.

Positive exponential decay requires a later strictly positive choice of
`rho`; this unit permits `rho = 0` and therefore does not itself prove a
positive decay rate. It also does not identify the Fourier integral with a
regional Green operator, construct regional `B0`, or attain window 15.

## Static verdict

All four Unit-D gates pass statically. The contour equality, summability and
normalization are constructed rather than accepted as renamed obligations.
Promotion remains blocked on Lean elaboration and axiom audit in the
sanctioned remote validation path.


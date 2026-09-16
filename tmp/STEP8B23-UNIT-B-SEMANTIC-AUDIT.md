# Step 8b.23 Unit B — static semantic audit

Status: **STATIC ONLY — NOT COMPILER-VERIFIED**.

Scope:

- `BalabanCMP89Eq248GreenMassUniformHolomorphy.draft.lean`
- `BalabanCMP89Eq248DisplayedGreenVectorPeriodicity.draft.lean`
- `BalabanCMP89Eq248CenteredGreenTorus.draft.lean`

## Gate B1 — one common polydisc, mass-uniform nonvanishing

**PASS (static, conditional on named scalar windows).**

`differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_of_commonRadius_massUniform_draft`
derives differentiability of the literal stabilized Green endpoint throughout
the complete four-dimensional polydisc. The imaginary hypothesis is
coordinatewise and simultaneous:

`forall nu, abs ((z nu).im) <= rho`.

Thus successive contour shifts do not rely on a one-coordinate-only gap.
Fine aliases and the central stabilized denominator are proved nonzero
internally from the common scalar inputs.

The remaining hypotheses are visible and material:

- `rho * exp rho <= 1/6`;
- `CMP89Eq249UniformNoncentralComplexRadiusCondition rho`;
- `CMP89Eq249CentralStabilizedComplexWindow a rho`;
- `CMP89Eq251UniformMassWindow mass`, literally `mass^2 <= 1`;
- `0 <= a` and `0 <= rho`.

This unit does not prove that an RG mass flow stays inside the mass window.

## Gate B2 — periodicity at the physical fine-lattice endpoint

**PASS (static).**

- The bare numerator uses the literal displacement `endpointU / (L^j)`.
- The centered-alias wrap is cancelled by the integer endpoint; it is not
  replaced by a unit-lattice endpoint.
- The displayed Green obtains one-coordinate, arbitrary-integer, and then
  integer-vector `2*pi` periodicity without borrowing nonvanishing outside
  the centered strip.
- The vector theorem is assembled from the one-coordinate theorem using
  finite addition and `Function.Periodic.int_mul_eq`/integer scalar periods.

The stabilized Green inherits only the periodicity justified on its explicit
non-singular domain. No global stabilized periodicity is asserted.

## Gate B3 — centered torus Green is constructed, not supplied

**PASS (static).**

- `cmp89Eq248CenteredCubeMomentum` fixes the negative physical convention
  `-2*pi*t`.
- `continuous_cmp89Eq248CenteredGreenCube` derives continuity from the
  complete-polydisc differentiability producer.
- `cmp89Eq248CenteredGreenCube_faceSeam` derives the seam from the physical
  boundary-period theorem. The proof starts at the upper centered-cube face,
  whose negative momentum is `-pi`, and shifts it to `+pi`.
- `cmp89Eq248CenteredGreenTorus` calls the quotient lift with the internally
  derived continuous function and seam; it accepts no arbitrary torus Green,
  periodic family, or factorization witness.
- `cmp89Eq248CenteredGreenTorus_covering_apply` records the exact pullback to
  the literal cube endpoint.

## Delimitation

Unit B produces the analytic domain and the source-faithful torus object. It
does **not** produce a uniform Green magnitude `B0`, exponential decay, finite
sampling/aliasing, window-15 attainment, or a terminal field. The mass window
remains a flow-facing dictionary obligation rather than a freely chosen
smallness parameter.

## Static verdict

All three Unit-B acceptance gates pass statically. The design precludes the
two main vacuity routes: a caller-supplied holomorphic Green family and a
caller-supplied periodic/seam witness. Promotion remains blocked on Lean
elaboration and axiom audit in the sanctioned remote validation path.


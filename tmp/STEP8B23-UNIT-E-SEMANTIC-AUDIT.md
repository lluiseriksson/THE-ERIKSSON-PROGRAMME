# Step 8b.23 Unit E — static semantic audit

Status: **STATIC ONLY — NOT COMPILER-VERIFIED**.

Scope:

- `BalabanCMP89CenteredTorusGreenCoefficientPhase.draft.lean`
- `BalabanCMP89CenteredTorusGreenCoefficientDictionary.draft.lean`
- `BalabanCMP89SignedLatticeL1TotalSum.draft.lean`
- `BalabanCMP89CenteredGreenFourierSummability.draft.lean`
- `BalabanCMP99PhysicalGreenFiniteGridAliasing.draft.lean`

## Gate E1 — coefficient phase has the correct orientation

**PASS (static).**

- Reciprocal aliases `2*pi*m` are proved invisible at an integer lattice
  displacement by a named theorem.
- Mathlib's negative Fourier mode `mFourier (-n)` combines with every literal
  alias branch to produce the **positive** affine displacement `u + M*n`.
- The phase identity is lifted through the actual bare numerator, the finite
  noncentral alias sum, the complete stabilized numerator, and finally the
  endpoint-independent denominator.

No reflection symmetry or synthetic endpoint family is introduced.

## Gate E2 — torus coefficient equals the literal normalized Green

**PASS (static).**

The coefficient dictionary constructs a centered representative only on the
literal translated Brillouin cube, proves the pointwise identity there, then
promotes it to an almost-everywhere identity for the restricted source
measure. Boundary or off-cube values are not promoted to a global identity.

`cmp89_mFourierCoeff_centeredGreen_eq_normalizedFineGreen` combines that
pointwise dictionary with the exact normalized measure transport. Its
endpoint is the literal normalized fine-lattice stabilized Green at
`u + (L^j)*n`.

## Gate E3 — exact signed-`l1` summability, without a volume loss

**PASS (static).**

- The full lattice weight factorizes exactly, giving
  `((1 + exp(-delta)) / (1 - exp(-delta)))^d`.
- The residue parametrization `n -> u + M*n` is proved injective for `M > 0`.
- Fine-to-owner scale conversion is exposed by the named equality
  `length(M*n) = M*length(n)` and a reverse-triangle estimate.
- At fine rate `rho/M`, a residue fibre is bounded by the owner-rate weight
  at `rho` with one explicit representative prefactor.
- In dimension four and for a centered representative, the complete fibre is
  bounded by `exp(2*rho)` times the exact owner-lattice geometric mass.

No spurious `M^4` or ball-counting `delta^-5` factor enters this route.

## Gate E4 — summability belongs to the actual Green coefficients

**PASS (static).**

`summable_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_draft` majorizes
the literal normalized physical coefficients by the exact residue weight.
The G23.4 dictionary then rewrites the actual torus `mFourierCoeff`; no
summable coefficient family is accepted from the caller. A strictly positive
`rho` is required at this point, as it must be for genuine summability.

## Gate E5 — finite-grid aliasing reaches literal CMP99 samples

**PASS (static).**

- Fourier reconstruction is derived from summability of the actual torus
  coefficients.
- The positive torus sample is identified with the finite `ZMod` character.
- The sealed Step-8b.22 selector then returns the exact integer residue fibre.
- The final source-specific theorem specializes to zero mass and positive
  stabilizing coefficient, replaces every torus sample by the literal
  uncentered CMP99 physical Green sample, and removes the centered torus from
  the public conclusion.

The zero-mode safety established in Unit C is therefore consumed rather than
silently bypassed.

## Delimitation

Unit E proves coefficient summability and the physical finite-grid aliasing
identity. It does not yet convert the selected residue sum into the periodic
endpoint/owner bound, construct regional `B0`, prove the full CMP99 operator
dictionary, attain window 15, or discharge a terminal field.

## Static verdict

All five Unit-E gates pass statically. The chain is sign-explicit,
source-normalized, and scale-accounted through the exact `l1` product sum.
Promotion remains blocked on Lean elaboration and axiom audit in the
sanctioned remote validation path.


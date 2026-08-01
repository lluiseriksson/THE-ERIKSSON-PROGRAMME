# (16) Repair criteria for PR #43

Status: **PRE-REGISTERED BEFORE REPAIR BUILDS, ORACLES, AND MUTATION RUNS**

This is a manufacturer repair record for the adversarial failure of the
SU(2) theta-prism artefact.  It is not an audit verdict and cannot certify the
repair.  The source branch was verified at
`0ac9b18c98cf12b305611fd74087816a3b5f1e32`; the audited base is
`26306b8f30e826b0bcb7c4caf6a5a42473ab5fd8`.

## Fixed acceptance criteria

1. Define the Borel measurable space on `CellConfiguration` and a normalized
   eight-coordinate product of the concrete SU(2) Haar probability measure.
   Prove mass one and finiteness.  Keep ordinary product-measure Fubini
   separate from Haar-invariant coordinate changes.
2. Replace the arbitrary `TwiceSpin -> SU2 -> Real` family at the public
   endpoint by explicitly indexed, representation-backed SU(2) character
   data.  State exactly which spins are constructed.
3. Classify each original field (`traceReality`, `characterBound`,
   `haarSchur`, `fubiniCoordinates`, `normMoments`, `coefficientSeries`, and
   `weightMeasurability`) as proved, genuinely loaded, or open.  Exhibit a
   concrete `ManufacturingTechnicalInputs` value at `beta = 1`; do not claim a
   uniform endpoint unless a value is constructed for every `BetaDomain`.
4. Provide a front-door theorem that supplies the concrete cell Haar measure
   and concrete character data itself.  Preserve the established
   combinatorics, witness, singlet `1/2`, and formal arithmetic unless a
   connection proof requires a localized edit.
5. Replace Python `assert` checks by explicit nonzero-exit checks.  Mutation
   tests must reject both `1/2 -> 1/3` and an attempted all-beta domain under
   ordinary Python and `python -O`.  The syntactic validator must reject
   headline-bearing fields, including spacing/name variants of
   `witnessNormSq = 3/4` and `CompleteUOrthogonality`; it will be described as
   a syntactic guard, not semantic honesty.
6. Build every theta-prism target and `YangMillsCore`; run the complete axiom
   oracle; require no project axioms, `sorry`, `admit`, or `sorryAx`, and allow
   only `propext`, `Classical.choice`, and `Quot.sound` in oracle headlines.
   Record exact commands, measured jobs, stdout/stderr, toolchain, EOL policy,
   source hashes, binary hashes, and all measured failures.
7. Re-run validation from a fresh checkout of the published refs.  Keep PR #43
   draft, update only its existing remote branch by explicit fast-forward,
   and stop for a new blind external audit.  No merge, paper claim, programme
   Gate 7 claim, or manufacturer self-certification is permitted.

## Pre-registered direct spin-one route

Before any build of the remaining coefficient obligation, the candidate route
is fixed as follows.

1. Prove the normalized Haar fourth moment
   `integral (fun g => (chi g).re ^ 4) haarSU2 = 2` using only explicit
   quaternion-basis matrices in `SU2`, ordinary left/right Haar invariance,
   and finite polynomial identities.  A full SU(2)-to-sphere measure
   equivalence, a Weyl integration formula, Peter--Weyl completeness, and the
   general tensor-power multiplicity formula are not inputs to this route.
   Concretely, write the four trace coordinates associated with
   `1, i, j, k` as `x_1, ..., x_4`.  The checked matrix identities must give
   `sum x_i ^ 2 = 1`, equality of the four pure moments, and equality of the
   six mixed moments under explicit left/right quaternion-basis
   permutations.  Hence normalization gives `4 * A + 12 * B = 1`, where
   `A = integral (x_1 ^ 4)` and `B = integral (x_1 ^ 2 * x_2 ^ 2)`.
   Conjugation by the concrete `j` matrix must fix `x_1` and negate `x_2`,
   so the two odd mixed moments vanish by bi-invariance.  Left multiplication
   by
   `q = (1 + i) / sqrt 2 = exp (i * pi / 4)` must send `x_1` to
   `(x_1 - x_2) / sqrt 2` up to the fixed sign convention.  Expanding the
   fourth power then gives `A = 3 * B`, hence `A = 1 / 8` and the required
   trace moment.  The half-angle element `exp (i * pi / 8)` is not used: it
   rotates the `(x_1, x_2)` plane by only `pi / 8` under left multiplication;
   half angles belong instead to quaternion conjugation on the imaginary
   three-space.
2. First recover the second moment `1` from the same four-coordinate
   construction and compare it with `chi_re_sq_integral_one`.  A mismatch is
   a failed coordinate normalization and blocks use of the fourth moment.
3. Symmetrize the spin-one coefficient under the concrete central element
   `negIdentitySU2`, obtaining the integral of
   `(u ^ 2 - 1) * Real.cosh ((beta / 2) * u)` with
   `u = (chi g).re`.
4. Treat the signed Taylor remainder separately.  For
   `r t = Real.cosh t - 1 - t ^ 2 / 2`, prove that `r` is even and monotone on
   the nonnegative axis.  Compare `r ((beta / 2) * u)` with
   `r (beta / 2)` on the two regions `u ^ 2 <= 1` and `1 <= u ^ 2`.  After
   multiplication by `u ^ 2 - 1`, both regions give the same lower bound;
   its integral is zero by the normalized second moment.  The sign-changing
   region may not be discarded or justified by a bare pointwise
   `cosh t - 1 >= t ^ 2 / 2` bound.
5. Combine the constant, quadratic, and remainder terms only after steps
   1--4 check.  The intended conclusion is
   `beta ^ 2 / 8 <= alpha su2WeylPolynomial beta 2` for `0 <= beta`.  Only
   then may `SpinOneCoefficientRemainderStep beta` and the concrete
   `ManufacturingTechnicalInputs beta` inhabitant be constructed.

The pin-exact static inventory found
`Mathlib.MeasureTheory.Constructions.HaarToSphere`, but no ready theorem for
the radial/angular independence of a normalized Gaussian and no existing
SU(2)-Haar-to-sphere identification.  These APIs are therefore not silently
counted as discharged inputs.  Any failed attempt or change of route must be
recorded before a replacement campaign is run.

## Evidence labels

- **EXACTO**: proved directly by checked Lean terms over concrete definitions.
- **CERTIFICADO**: conditional on an explicitly named genuine analytic input.
- **VERIFICADO**: reproduced command/output evidence only.
- **ABIERTO**: not discharged by the published artefact.

Campaign results may not alter the constants `1/2`, `3/4`, `1/16`, or
`1/512`, weaken the three-branch witness, or enlarge the beta domain.  Every
measured failure remains in the final transcript or repair log.

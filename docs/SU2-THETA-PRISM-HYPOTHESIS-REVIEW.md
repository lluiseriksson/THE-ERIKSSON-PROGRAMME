# (16) PR #43 repair: loaded-hypothesis participation review

Status: **MANUFACTURER PARTICIPATION REVIEW UPDATED; NOT AN EXTERNAL AUDIT**

All seven original technical obligations now have concrete discharges.  The
public front door fixes `cellHaar` and `su2WeylPolynomial` and constructs its
technical record internally.

| Technical input | Current state | Artefact lemmas used | Headline derived |
|---|---|---|---|
| `traceReality` | PROVED | `traceRealityConcrete`, from determinant one and unitarity | `cellWeight_reflection_invariant` |
| `characterBound` | PROVED | `characterBoundConcrete`, `cellWeight_le_exp_three_abs` | `cellWeight_integrable` |
| `haarSchur` | PROVED | `haarSchurConcrete`, `sunHaarProb_fundamental_entry_orthogonality` | three conditional-zero identities |
| `fubiniCoordinates` | PROVED | `fubiniCoordinatesConcrete`, `relativeCoordinateEquiv_measurePreserving` | three complete orthogonalities |
| `normMoments` | PROVED | `normMomentsConcrete`, `witnessNormSq_eq_three_quarters` | `witnessNormSq = 3/4` |
| `coefficientSeries` | PROVED | `alpha_spinHalf_lower`, `chi_re_fourth_integral_two_quaternion`, `signed_coshRemainder_nonnegative`, `spinOneCoefficientRemainderStepConcrete` | concrete-probe local gate inequality |
| `weightMeasurability` | PROVED | `weightMeasurabilityConcrete`, `cellWeight_integrable` | concrete `cellHaar` weight integrability |

The retained internal field type does not contain the pairing equality, the
witness norm, an orthogonality headline, the proved spin-half remainder, or
the final gate inequality.  It is inhabited by
`manufacturingTechnicalInputsConcrete beta hbeta` for every
`hbeta : BetaDomain beta`; the separately named beta-one term is only a
specialization of this uniform constructor.

This document cannot assign an external audit verdict.

## Completed direct-coefficient repair route

The exact dependency pin is Mathlib
`07642720480157414db592fa85b626dafb71355b`.  A source search at that pin
found no SU(2) Weyl integration formula.  In particular,
`MeasureTheory/Constructions/HaarToSphere.lean` constructs angular measure
from additive Haar measure on a real normed space; it does not identify SU(2),
its normalized Haar measure, or the trace pushforward.

`QuaternionMoments.lean` obtains the fourth moment directly from explicit
quaternion-basis SU(2) matrices and left/right Haar invariance.  It first
reproduces `integral chi^2 = 1` as the required normalization gate, then proves
`integral chi^4 = 2`; it uses neither a Weyl formula nor Peter--Weyl.

The independent spin-half estimate
`beta / 2 <= alpha su2WeylPolynomial beta 1` is now proved using left-Haar
invariance under the explicit central element `-I`, the oddness of the
fundamental trace, and `Real.self_le_sinh_iff`.  The general tensor-power
multiplicity formula formerly present in the artefact was unused and has been
removed.  No Peter--Weyl completeness was introduced.  The signed remainder
is controlled by monotonicity of
`cosh t - 1 - t^2/2` separately on the sign-changing regions, and
`spinOneCoefficientRemainderStepConcrete` discharges `coefficientSeries`.

Colab verification at source
`3c198717e1b53b016803e3db76fda88f99314f89` and the pin above built
`Coefficients` and `Endpoint` and elaborated the uniform inhabitant type.  A
terminal complete oracle, two-clone reproduction, and fresh blind external
audit remain required.

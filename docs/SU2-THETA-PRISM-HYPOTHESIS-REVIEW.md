# (16) PR #43 repair: loaded-hypothesis participation review

Status: **MANUFACTURER PARTIAL REVIEW; NOT AN EXTERNAL AUDIT**

Six of the seven original fields of `ManufacturingTechnicalInputs` are no
longer loaded.  The public front door fixes both `cellHaar` and
`su2WeylPolynomial`; its only remaining input is the genuine coefficient
series obligation.

| Technical input | Current state | Artefact lemmas used | Headline derived |
|---|---|---|---|
| `traceReality` | PROVED | `traceRealityConcrete`, from determinant one and unitarity | `cellWeight_reflection_invariant` |
| `characterBound` | PROVED | `characterBoundConcrete`, `cellWeight_le_exp_three_abs` | `cellWeight_integrable` |
| `haarSchur` | PROVED | `haarSchurConcrete`, `sunHaarProb_fundamental_entry_orthogonality` | three conditional-zero identities |
| `fubiniCoordinates` | PROVED | `fubiniCoordinatesConcrete`, `relativeCoordinateEquiv_measurePreserving` | three complete orthogonalities |
| `normMoments` | PROVED | `normMomentsConcrete`, `witnessNormSq_eq_three_quarters` | `witnessNormSq = 3/4` |
| `coefficientSeries` | OPEN / MINIMIZED TO SPIN ONE | `alpha_spinHalf_lower` proves the spin-half remainder; only `SpinOneCoefficientRemainderStep` is loaded | concrete-probe local gate inequality |
| `weightMeasurability` | PROVED | `weightMeasurabilityConcrete`, `cellWeight_integrable` | concrete `cellHaar` weight integrability |

The remaining field does not contain the pairing equality, the witness norm,
an orthogonality headline, the proved spin-half remainder, or the final gate
inequality.  Nevertheless no
closed inhabitant of `ManufacturingTechnicalInputs 1` has yet been built, so
the beta-one anti-vacuity criterion and the uniform gate remain **OPEN**.

This document cannot assign an external audit verdict.

## Preregistered direct-coefficient repair route

The exact dependency pin is Mathlib
`07642720480157414db592fa85b626dafb71355b`.  A source search at that pin
found no SU(2) Weyl integration formula.  In particular,
`MeasureTheory/Constructions/HaarToSphere.lean` constructs angular measure
from additive Haar measure on a real normed space; it does not identify SU(2),
its normalized Haar measure, or the trace pushforward.

The repository proves the second moment
`sunHaarProb_trace_normSq_integral_eq_one`.  It does not prove the fourth
moment `integral (chi ^ 4) = 2`.  The generic Schur API applies to constructed
irreducible representations, while the current label-two bridge is only the
pointwise character-ring identity `chi_1 + 1 = chi_fund ^ 2`.  Therefore the
missing brick for the proposed spin-one estimate is one of:

- an SU(2) Haar/Weyl trace-pushforward formula with its normalization; or
- a concrete irreducible spin-one representation together with a proved
  decomposition of the fundamental tensor square and the resulting fourth
  moment.

The independent spin-half estimate
`beta / 2 <= alpha su2WeylPolynomial beta 1` is now proved using left-Haar
invariance under the explicit central element `-I`, the oddness of the
fundamental trace, and `Real.self_le_sinh_iff`.  The general tensor-power
multiplicity formula formerly present in the artefact was unused and has been
removed.  No Peter--Weyl completeness was introduced, and `coefficientSeries`
remains open exactly at `SpinOneCoefficientRemainderStep`.

Colab verification at source `fcbe7194fc9eadaa0e6a35e61c7a59fe4ecade58`
and the pin above built the expanded oracle with 8186 jobs, two requested jobs
on two host CPUs, in 96 seconds.  All 38 printed declarations used only
`propext`, `Classical.choice`, and `Quot.sound`.  This is manufacturer
verification, not the required fresh blind external audit.

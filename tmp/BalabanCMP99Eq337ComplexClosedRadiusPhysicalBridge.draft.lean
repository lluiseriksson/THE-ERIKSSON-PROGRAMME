import YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusScalar
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius

/-!
PRE-VALIDATION: scratch physical adapter. This file has no materialized
`.olean` and no compiler or axiom-oracle verdict.

It identifies the proof-free closed scalar recursion with the literal
Eq. (3.37) four-Wilson-line radius and with the canonical no-winding record.
No per-scale gate, radius family or free deviation estimate is introduced.
-/

namespace YangMills.RG

noncomputable section

/-- The proof-free deviation radius is definitionally the common four-path
Eq. (3.37) envelope after fixing the printed path length. -/
theorem cmp99ComplexClosedRadiusDeviation_eq_eq337Uniform
    (d M : ℕ) (r : ℝ) :
    cmp99ComplexClosedRadiusDeviation (d * (M - 1)) r =
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r := by
  simp only [cmp99ComplexClosedRadiusDeviation,
    cmp99ComplexClosedRadiusFactorEnvelope,
    cmp99Eq337SourceComplexUbarUniformDeviationRadius,
    cmp99ComplexFourWilsonUniformDeviationBudget,
    cmp99ComplexFourFactorDeviationBudget]
  ring

/-- The proof-free logarithmic radius is the literal logarithmic radius of
the canonical no-winding budget carrying the same deviation. -/
theorem cmp99ComplexClosedRadiusLog_eq_ubarLogRadius
    {Nc : ℕ} [NeZero Nc] (delta : ℝ)
    (hnoWinding : delta < cmp99UbarNoWindingThreshold Nc) :
    cmp99ComplexClosedRadiusLog delta =
      cmp99UbarLogRadius
        (cmp99PhysicalNoWindingBudget (Nc := Nc) delta hnoWinding) := by
  rfl

/-- The proof-free exponential radius is the literal exponential radius of
the same canonical no-winding budget. -/
theorem cmp99ComplexClosedRadiusExp_eq_ubarExpRadius
    {Nc : ℕ} [NeZero Nc] (delta : ℝ)
    (hnoWinding : delta < cmp99UbarNoWindingThreshold Nc) :
    cmp99ComplexClosedRadiusExp delta =
      cmp99UbarExpRadius
        (cmp99PhysicalNoWindingBudget (Nc := Nc) delta hnoWinding) := by
  rfl

end

end YangMills.RG

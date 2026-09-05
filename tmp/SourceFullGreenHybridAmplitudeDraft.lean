import YangMills.RG.BalabanCMP85SourceFullGreenScalarFoundations
import YangMills.RG.BalabanCMP99PhysicalFullGreenOwnerResidueBound

/-!
# PRE-VALIDATION: draft hybrid coefficient bound for the complete full G

Source present; no `.olean` has been materialized for this draft and its
proofs have not been checked by Lean. Not a root import or physical B0.

Use the lower coefficient only for the antitone moment. Positive coefficient
factors use the upper coefficient. The complete amplitude is not claimed
antitone. The bare diagonal scale loss remains a separate exact summand.
-/

namespace YangMills.RG
noncomputable section

/-- Both ends of the coefficient interval have distinct roles. -/
def cmp85SourceFullGreenHybridAmplitudeConstantDraft
    (lower upper rho : ℝ) : ℝ :=
  cmp89Eq246CentralAverageRowReciprocalBound rho *
      (cmp89Eq246FinePointSourceMomentAmplitudeBound lower rho +
        cmp89Eq248ComplexNoncentralGreenSumBound_draft rho +
        upper * cmp89Eq246FinePointSourceMomentAmplitudeBound lower rho *
          cmp89Eq249ComplexNoncentralAliasSumBound rho) +
    (upper * cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
      cmp89Eq246FinePointSourceMomentAmplitudeBound lower rho) *
        (∑' n : ℤ, cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4

private theorem fullGreenMoment_nonneg_draft {a rho : ℝ}
    (hrho : 0 ≤ rho)
    (hw : CMP89Eq249CentralStabilizedComplexWindow a rho) :
    0 ≤ cmp89Eq246FinePointSourceMomentAmplitudeBound a rho := by
  have hgap : 0 < cmp89Eq249CentralStabilizedLowerConstant 4 a -
      cmp89Eq249CentralStabilizedDenominatorVariationBound a rho :=
    sub_pos.mpr hw
  unfold cmp89Eq246FinePointSourceMomentAmplitudeBound
    cmp89Eq249CentralStabilizedComplexReciprocalBound
    cmp89Eq251CentralFineSymbolStripUpperBound
    cmp89Eq249CentralFineSymbolVerticalBound cmp89Eq249CentralFineSymbolRealBound
    cmp89Eq248ComplexNoncentralGreenSumBound_draft
    cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft
    cmp89Eq248ComplexNoncentralGreenRadialConstant_draft
  positivity

/-- Literal full budget on a coefficient interval. No replacement of the
full operator by its averaged particular solution occurs here. -/
theorem cmp85SourceFullGreen_fullBudget_le_hybrid_draft
    {lower current upper rho : ℝ} (hlower : 0 < lower)
    (hlc : lower ≤ current) (hcu : current ≤ upper)
    (hrho : 0 ≤ rho)
    (hw : CMP89Eq249CentralStabilizedComplexWindow lower rho)
    (hpair : CMP89Eq249CentralAveragePairComplexWindow rho) (K : ℕ) :
    cmp89Eq246DirectedFullSolutionSumBound K 1 current rho ≤
      cmp85SourceFullGreenHybridAmplitudeConstantDraft lower upper rho +
        cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
          (256 * ((K + 1 : ℕ) : ℝ) ^ 2) := by
  have hc : 0 < current := hlower.trans_le hlc
  have hu : 0 < upper := hc.trans_le hcu
  have hwc := CMP89Eq249CentralStabilizedComplexWindow_mono
    hlower hlc hrho hw
  have hPc := fullGreenMoment_nonneg_draft hrho hwc
  have hmoment := cmp85SourceFullGreen_momentBudget_antitone
    hlower hlc hrho hw
  have hcoef : current * cmp89Eq246FinePointSourceMomentAmplitudeBound current rho ≤
      upper * cmp89Eq246FinePointSourceMomentAmplitudeBound lower rho :=
    mul_le_mul hcu hmoment hPc hu.le
  have hrow : 0 ≤ cmp89Eq246CentralAverageRowReciprocalBound rho := by
    have hgap : 0 < cmp89Eq249CentralAveragePairLowerConstant -
        cmp89Eq249CentralAveragePairVerticalBound rho := sub_pos.mpr hpair
    unfold cmp89Eq246CentralAverageRowReciprocalBound
    positivity
  have hT : 0 ≤ cmp89Eq249ComplexNoncentralAliasSumBound rho := by
    unfold cmp89Eq249ComplexNoncentralAliasSumBound
      cmp89Eq249ComplexNoncentralAliasQuotientConstant
      cmp89Eq249ComplexNoncentralAliasRadialConstant
    positivity
  have hQ : 0 ≤ cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho := by
    unfold cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft
      cmp89Eq248ComplexNoncentralGreenRadialConstant_draft
    positivity
  have hcentral := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hmoment (le_refl _))
      (mul_le_mul_of_nonneg_right hcoef hT)) hrow
  have hcorrection :
      (current * cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
        cmp89Eq246FinePointSourceMomentAmplitudeBound current rho) ≤
      (upper * cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
        cmp89Eq246FinePointSourceMomentAmplitudeBound lower rho) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left hcoef hQ)
  have hZ : 0 ≤ (∑' n : ℤ, cmp89Eq251OneDimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4 := by positivity
  have hsum := add_le_add hcentral
    (mul_le_mul_of_nonneg_right hcorrection hZ)
  unfold cmp89Eq246DirectedFullSolutionSumBound
    cmp89Eq246FinePointSourceCentralComponentAmplitudeBound
    cmp89Eq246DirectedNoncentralSolutionSumBound
    cmp89Eq246FinePointSourceNoncentralCorrectionAmplitudeBound
    cmp85SourceFullGreenHybridAmplitudeConstantDraft
  rw [abs_of_pos hc, pow_one]
  linarith

#print axioms cmp85SourceFullGreen_fullBudget_le_hybrid_draft

end
end YangMills.RG

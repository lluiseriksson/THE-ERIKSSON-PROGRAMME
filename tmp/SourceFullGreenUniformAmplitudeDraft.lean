import tmp.SourceFullGreenHybridAmplitudeDraft
import tmp.FullGreenNormalizedBudgetRepro
import YangMills.RG.BalabanCMP99GeneratedFullPointSourceOwnerBound

/-!
# PRE-VALIDATION: full-G uniform scalar amplitude, with inverse-square scale

Source present; `.olean` not materialized and result not compiler-verified.
This draft is not part of the running F4 repro queue. It consumes the hybrid
interval bound, not antitonicity of the whole coefficient. The generated
module is imported only for its scalar amplitude definition; its physical
coefficient is never identified with the source-flow coefficient.

The result is uniform in depth for fixed initial a and RG ratio L. It is
not a regional/derivative estimate, physical B0, or window-15 producer.
-/

namespace YangMills.RG
noncomputable section

def cmp85SourceFullGreenContourFactorDraft (rho : ℝ) : ℝ :=
  (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho)

theorem cmp85SourceFullGreenContourFactorDraft_pos {rho : ℝ}
    (hrho : 0 < rho) : 0 < cmp85SourceFullGreenContourFactorDraft rho := by
  have he : Real.exp (-rho) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd : 0 < 1 - Real.exp (-rho) := sub_pos.mpr he
  unfold cmp85SourceFullGreenContourFactorDraft
  positivity

theorem cmp85SourceFullGreenHybridAmplitudeConstantDraft_nonneg
    {lower upper rho : ℝ} (hupper : 0 ≤ upper) (hrho : 0 ≤ rho)
    (hw : CMP89Eq249CentralStabilizedComplexWindow lower rho)
    (hp : CMP89Eq249CentralAveragePairComplexWindow rho) :
    0 ≤ cmp85SourceFullGreenHybridAmplitudeConstantDraft lower upper rho := by
  have hg : 0 < cmp89Eq249CentralStabilizedLowerConstant 4 lower -
      cmp89Eq249CentralStabilizedDenominatorVariationBound lower rho := sub_pos.mpr hw
  have hp' : 0 < cmp89Eq249CentralAveragePairLowerConstant -
      cmp89Eq249CentralAveragePairVerticalBound rho := sub_pos.mpr hp
  unfold cmp85SourceFullGreenHybridAmplitudeConstantDraft
    cmp89Eq246CentralAverageRowReciprocalBound
    cmp89Eq246FinePointSourceMomentAmplitudeBound
    cmp89Eq249CentralStabilizedComplexReciprocalBound
    cmp89Eq251CentralFineSymbolStripUpperBound
    cmp89Eq249CentralFineSymbolVerticalBound cmp89Eq249CentralFineSymbolRealBound
    cmp89Eq248ComplexNoncentralGreenSumBound_draft
    cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft
    cmp89Eq248ComplexNoncentralGreenRadialConstant_draft
    cmp89Eq249ComplexNoncentralAliasSumBound
    cmp89Eq249ComplexNoncentralAliasQuotientConstant
    cmp89Eq249ComplexNoncentralAliasRadialConstant
  positivity

/-- The sharper split retains the central inverse-fourth term separately. -/
theorem cmp85SourceFullGreen_ownerAmplitude_split_draft
    {lower current upper rho : ℝ} (hlower : 0 < lower)
    (hlc : lower ≤ current) (hcu : current ≤ upper) (hrho : 0 < rho)
    (hw : CMP89Eq249CentralStabilizedComplexWindow lower rho)
    (hp : CMP89Eq249CentralAveragePairComplexWindow rho)
    {R : ℕ} (hR : 1 ≤ R) :
    cmp99PhysicalFullGreenOwnerAmplitude R current rho ≤
      cmp85SourceFullGreenContourFactorDraft rho *
        (((R : ℝ) ^ 4)⁻¹ *
            cmp85SourceFullGreenHybridAmplitudeConstantDraft lower upper rho +
          1024 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
            ((R : ℝ) ^ 2)⁻¹) := by
  have hb := cmp85SourceFullGreen_fullBudget_le_hybrid_draft
    hlower hlc hcu hrho.le hw hp R
  have hD : 0 ≤ 256 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound := by
    unfold cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound
    positivity
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hnorm := FullGreenNormalizedBudgetRepro.split
    (C := cmp85SourceFullGreenHybridAmplitudeConstantDraft lower upper rho)
    hRreal hD
  have hb' : cmp89Eq246DirectedFullSolutionSumBound R 1 current rho ≤
      cmp85SourceFullGreenHybridAmplitudeConstantDraft lower upper rho +
        (256 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound) *
          ((R : ℝ) + 1) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using hb
  have hn := (mul_le_mul_of_nonneg_left hb'
    (inv_nonneg.mpr (by positivity : 0 ≤ (R : ℝ) ^ 4))).trans hnorm
  have hf := mul_le_mul_of_nonneg_left hn
    (cmp85SourceFullGreenContourFactorDraft_pos hrho).le
  unfold cmp99PhysicalFullGreenOwnerAmplitude
  change ((R : ℝ) ^ 4)⁻¹ *
      (cmp89Eq246DirectedFullSolutionSumBound R 1 current rho *
        cmp85SourceFullGreenContourFactorDraft rho) ≤ _
  convert hf using 1 <;> ring

/-- Keep R^-2: replacing it by one would lose the later R^4-fibre/R^2 action scale. -/
theorem cmp85SourceFullGreen_ownerAmplitude_inverse_square_draft
    {lower current upper rho : ℝ} (hlower : 0 < lower)
    (hlc : lower ≤ current) (hcu : current ≤ upper) (hrho : 0 < rho)
    (hw : CMP89Eq249CentralStabilizedComplexWindow lower rho)
    (hp : CMP89Eq249CentralAveragePairComplexWindow rho)
    {R : ℕ} (hR : 1 ≤ R) :
    cmp99PhysicalFullGreenOwnerAmplitude R current rho ≤
      (cmp85SourceFullGreenContourFactorDraft rho *
        (cmp85SourceFullGreenHybridAmplitudeConstantDraft lower upper rho +
          1024 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound)) *
        ((R : ℝ) ^ 2)⁻¹ := by
  have hupper : 0 ≤ upper := (hlower.trans_le (hlc.trans hcu)).le
  have hC := cmp85SourceFullGreenHybridAmplitudeConstantDraft_nonneg
    hupper hrho.le hw hp
  have hD : 0 ≤ 256 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound := by
    unfold cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound
    positivity
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hn := FullGreenNormalizedBudgetRepro.retain_inverse_square hRreal hC hD
  have hb := cmp85SourceFullGreen_fullBudget_le_hybrid_draft
    hlower hlc hcu hrho.le hw hp R
  have hb' : cmp89Eq246DirectedFullSolutionSumBound R 1 current rho ≤
      cmp85SourceFullGreenHybridAmplitudeConstantDraft lower upper rho +
        (256 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound) *
          ((R : ℝ) + 1) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using hb
  have hfinal := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hb'
      (inv_nonneg.mpr (by positivity : 0 ≤ (R : ℝ) ^ 4))).trans hn)
    (cmp85SourceFullGreenContourFactorDraft_pos hrho).le
  unfold cmp99PhysicalFullGreenOwnerAmplitude
  change ((R : ℝ) ^ 4)⁻¹ *
      (cmp89Eq246DirectedFullSolutionSumBound R 1 current rho *
        cmp85SourceFullGreenContourFactorDraft rho) ≤ _
  convert hfinal using 1 <;> ring

/-- The radius and amplitude are chosen once, before the universal depth. -/
theorem exists_cmp85SourceFullGreen_uniformOwnerAmplitude_draft
    {a : ℝ} {L : ℕ} (ha : 0 < a) (hL : 2 ≤ L) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧
      rho * Real.exp rho ≤ 1 / 6 ∧
      CMP89Eq249UniformNoncentralComplexRadiusCondition rho ∧
      CMP89Eq249CentralAveragePairComplexWindow rho ∧
      ∀ j : ℕ,
        CMP89Eq249CentralStabilizedComplexWindow
            (cmp99SourceMassParameter a (L : ℝ) j) rho ∧
          cmp99PhysicalFullGreenOwnerAmplitude (L ^ (j + 1))
              (cmp99SourceMassParameter a (L : ℝ) j) rho ≤
            C * (((L ^ (j + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
  obtain ⟨rho, hrho, hamp, hrad, hp, hw, hj⟩ :=
    exists_cmp85SourceFullGreen_uniformRadiusAndMoment ha hL
  let lower := cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (show 1 < L by omega)
  have hlower : 0 < lower := cmp85Eq215SourceAveragingCoefficientFloor_pos ha hLreal
  let C := cmp85SourceFullGreenContourFactorDraft rho *
    (cmp85SourceFullGreenHybridAmplitudeConstantDraft lower a rho +
      1024 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound)
  have hC : 0 < C := by
    have hhybrid := cmp85SourceFullGreenHybridAmplitudeConstantDraft_nonneg
      ha.le hrho.le hw hp
    have hbare : 0 < cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound := by
      unfold cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound
      positivity
    exact mul_pos (cmp85SourceFullGreenContourFactorDraft_pos hrho)
      (add_pos_of_nonneg_of_pos hhybrid (mul_pos (by norm_num) hbare))
  refine ⟨rho, C, hrho, hC, hamp, hrad, hp, ?_⟩
  intro j
  refine ⟨(hj j).1, ?_⟩
  have hR : 1 ≤ L ^ (j + 1) := one_le_pow_of_le (by omega) _
  exact cmp85SourceFullGreen_ownerAmplitude_inverse_square_draft hlower
    (cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter ha hLreal j)
    (cmp85SourceFullGreen_massParameter_le_initial ha (by linarith) j)
    hrho hw hp hR

#print axioms cmp85SourceFullGreenContourFactorDraft_pos
#print axioms cmp85SourceFullGreenHybridAmplitudeConstantDraft_nonneg
#print axioms cmp85SourceFullGreen_ownerAmplitude_split_draft
#print axioms cmp85SourceFullGreen_ownerAmplitude_inverse_square_draft
#print axioms exists_cmp85SourceFullGreen_uniformOwnerAmplitude_draft

end
end YangMills.RG

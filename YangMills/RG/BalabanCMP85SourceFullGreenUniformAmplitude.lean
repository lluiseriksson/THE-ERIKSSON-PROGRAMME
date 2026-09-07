import YangMills.RG.BalabanCMP85SourceFullGreenHybridAmplitude
import YangMills.RG.BalabanCMP85FullGreenNormalizedBudget
import YangMills.RG.BalabanCMP99GeneratedFullPointSourceOwnerBound

/-!
# A common positive radius and scalar owner-amplitude bound, chosen before depth.

Compiler-verified and materialized in the fresh Colab F4 graph at source
5138e9bd4bc88797c91c21df5bb5c630c71600ca on 2026-09-05.
Downloaded evidence independently verified; see ledger Addendum 1116.
The earlier draft diagnostic is preserved separately, not used as this seal.

Only names, imports and audit placement change in this promotion. The
mathematical statements, constants and hypotheses are preserved. No
regional/derivative B0, window-15 attainment or terminal obligation is claimed.
-/

namespace YangMills.RG
noncomputable section

def cmp85SourceFullGreenContourFactor (rho : ℝ) : ℝ :=
  (2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho)

theorem cmp85SourceFullGreenContourFactor_pos {rho : ℝ}
    (hrho : 0 < rho) : 0 < cmp85SourceFullGreenContourFactor rho := by
  have he : Real.exp (-rho) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd : 0 < 1 - Real.exp (-rho) := sub_pos.mpr he
  unfold cmp85SourceFullGreenContourFactor
  positivity

theorem cmp85SourceFullGreenHybridAmplitudeConstant_nonneg
    {lower upper rho : ℝ} (hupper : 0 ≤ upper) (hrho : 0 ≤ rho)
    (hw : CMP89Eq249CentralStabilizedComplexWindow lower rho)
    (hp : CMP89Eq249CentralAveragePairComplexWindow rho) :
    0 ≤ cmp85SourceFullGreenHybridAmplitudeConstant lower upper rho := by
  have hg : 0 < cmp89Eq249CentralStabilizedLowerConstant 4 lower -
      cmp89Eq249CentralStabilizedDenominatorVariationBound lower rho := sub_pos.mpr hw
  have hp' : 0 < cmp89Eq249CentralAveragePairLowerConstant -
      cmp89Eq249CentralAveragePairVerticalBound rho := sub_pos.mpr hp
  unfold cmp85SourceFullGreenHybridAmplitudeConstant
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
theorem cmp85SourceFullGreen_ownerAmplitude_split
    {lower current upper rho : ℝ} (hlower : 0 < lower)
    (hlc : lower ≤ current) (hcu : current ≤ upper) (hrho : 0 < rho)
    (hw : CMP89Eq249CentralStabilizedComplexWindow lower rho)
    (hp : CMP89Eq249CentralAveragePairComplexWindow rho)
    {R : ℕ} (hR : 1 ≤ R) :
    cmp99PhysicalFullGreenOwnerAmplitude R current rho ≤
      cmp85SourceFullGreenContourFactor rho *
        (((R : ℝ) ^ 4)⁻¹ *
            cmp85SourceFullGreenHybridAmplitudeConstant lower upper rho +
          1024 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound *
            ((R : ℝ) ^ 2)⁻¹) := by
  have hb := cmp85SourceFullGreen_fullBudget_le_hybrid
    hlower hlc hcu hrho.le hw hp R
  have hD : 0 ≤ 256 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound := by
    unfold cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound
    positivity
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hnorm := CMP85FullGreenNormalizedBudget.split
    (C := cmp85SourceFullGreenHybridAmplitudeConstant lower upper rho)
    hRreal hD
  have hb' : cmp89Eq246DirectedFullSolutionSumBound R 1 current rho ≤
      cmp85SourceFullGreenHybridAmplitudeConstant lower upper rho +
        (256 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound) *
          ((R : ℝ) + 1) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using hb
  have hn := (mul_le_mul_of_nonneg_left hb'
    (inv_nonneg.mpr (by positivity : 0 ≤ (R : ℝ) ^ 4))).trans hnorm
  have hf := mul_le_mul_of_nonneg_left hn
    (cmp85SourceFullGreenContourFactor_pos hrho).le
  unfold cmp99PhysicalFullGreenOwnerAmplitude
  change ((R : ℝ) ^ 4)⁻¹ *
      (cmp89Eq246DirectedFullSolutionSumBound R 1 current rho *
        cmp85SourceFullGreenContourFactor rho) ≤ _
  convert hf using 1 <;> ring

/-- Keep R^-2: replacing it by one would lose the later R^4-fibre/R^2 action scale. -/
theorem cmp85SourceFullGreen_ownerAmplitude_inverse_square
    {lower current upper rho : ℝ} (hlower : 0 < lower)
    (hlc : lower ≤ current) (hcu : current ≤ upper) (hrho : 0 < rho)
    (hw : CMP89Eq249CentralStabilizedComplexWindow lower rho)
    (hp : CMP89Eq249CentralAveragePairComplexWindow rho)
    {R : ℕ} (hR : 1 ≤ R) :
    cmp99PhysicalFullGreenOwnerAmplitude R current rho ≤
      (cmp85SourceFullGreenContourFactor rho *
        (cmp85SourceFullGreenHybridAmplitudeConstant lower upper rho +
          1024 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound)) *
        ((R : ℝ) ^ 2)⁻¹ := by
  have hupper : 0 ≤ upper := (hlower.trans_le (hlc.trans hcu)).le
  have hC := cmp85SourceFullGreenHybridAmplitudeConstant_nonneg
    hupper hrho.le hw hp
  have hD : 0 ≤ 256 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound := by
    unfold cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound
    positivity
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hn := CMP85FullGreenNormalizedBudget.retain_inverse_square hRreal hC hD
  have hb := cmp85SourceFullGreen_fullBudget_le_hybrid
    hlower hlc hcu hrho.le hw hp R
  have hb' : cmp89Eq246DirectedFullSolutionSumBound R 1 current rho ≤
      cmp85SourceFullGreenHybridAmplitudeConstant lower upper rho +
        (256 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound) *
          ((R : ℝ) + 1) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using hb
  have hfinal := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hb'
      (inv_nonneg.mpr (by positivity : 0 ≤ (R : ℝ) ^ 4))).trans hn)
    (cmp85SourceFullGreenContourFactor_pos hrho).le
  unfold cmp99PhysicalFullGreenOwnerAmplitude
  change ((R : ℝ) ^ 4)⁻¹ *
      (cmp89Eq246DirectedFullSolutionSumBound R 1 current rho *
        cmp85SourceFullGreenContourFactor rho) ≤ _
  convert hfinal using 1 <;> ring

/-- The radius and amplitude are chosen once, before the universal depth. -/
theorem exists_cmp85SourceFullGreen_uniformOwnerAmplitude
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
  let C := cmp85SourceFullGreenContourFactor rho *
    (cmp85SourceFullGreenHybridAmplitudeConstant lower a rho +
      1024 * cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound)
  have hC : 0 < C := by
    have hhybrid := cmp85SourceFullGreenHybridAmplitudeConstant_nonneg
      ha.le hrho.le hw hp
    have hbare : 0 < cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound := by
      unfold cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound
      positivity
    exact mul_pos (cmp85SourceFullGreenContourFactor_pos hrho)
      (add_pos_of_nonneg_of_pos hhybrid (mul_pos (by norm_num) hbare))
  refine ⟨rho, C, hrho, hC, hamp, hrad, hp, ?_⟩
  intro j
  refine ⟨(hj j).1, ?_⟩
  have hR : 1 ≤ L ^ (j + 1) := Left.one_le_pow_of_le (by omega) _
  exact cmp85SourceFullGreen_ownerAmplitude_inverse_square hlower
    (cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter ha hLreal j)
    (cmp85SourceFullGreen_massParameter_le_initial ha (by linarith) j)
    hrho hw hp hR


end
end YangMills.RG

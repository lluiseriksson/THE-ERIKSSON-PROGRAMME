import YangMills.RG.BalabanCMP89SourceNeumannPhysicalGateWitness

/-!
# Monotone consumption of the physical Neumann gate witness

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

The exact `27/512` witness is useful only after the two physical deviation
coefficients are compared with its common target `4^-8`.  This leaf performs
that monotone comparison and then rewrites the coefficient bounds as literal
fine- and coarse-radius inequalities.  It does not prove those two radius
bounds for the source flow.
-/

namespace YangMills.RG

noncomputable section

/-- The physical one-step defect coefficient is monotone in both nonnegative
deviation coefficients. -/
theorem cmp89SourceNeumannPhysicalOneStepDefectCoefficient_mono
    {d M : ℕ} [NeZero d] [NeZero M]
    {etaFine etaCoarse etaFine' etaCoarse' : ℝ}
    (etaFine_nonneg : 0 ≤ etaFine)
    (etaCoarse_nonneg : 0 ≤ etaCoarse)
    (hfine : etaFine ≤ etaFine')
    (hcoarse : etaCoarse ≤ etaCoarse') :
    cmp89SourceNeumannPhysicalOneStepDefectCoefficient
        d M etaFine etaCoarse ≤
      cmp89SourceNeumannPhysicalOneStepDefectCoefficient
        d M etaFine' etaCoarse' := by
  unfold cmp89SourceNeumannPhysicalOneStepDefectCoefficient
  have hsum_nonneg :
      0 ≤ (((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine) +
        (M : ℝ) * etaCoarse := by
    positivity
  have hsum :
      (((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine) +
          (M : ℝ) * etaCoarse ≤
        (((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine') +
          (M : ℝ) * etaCoarse' := by
    gcongr <;> positivity
  have htwice_nonneg :
      0 ≤ 2 *
        ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine) +
          (M : ℝ) * etaCoarse) := mul_nonneg (by norm_num) hsum_nonneg
  have htwice :
      2 * ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine) +
            (M : ℝ) * etaCoarse) ≤
        2 * ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine') +
            (M : ℝ) * etaCoarse') :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hsquare :
      (2 * ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine) +
        (M : ℝ) * etaCoarse)) ^ 2 ≤
      (2 * ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine') +
        (M : ℝ) * etaCoarse')) ^ 2 := by
    nlinarith [sq_nonneg
      (2 * ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine') +
        (M : ℝ) * etaCoarse') -
      2 * ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine) +
        (M : ℝ) * etaCoarse))]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsquare (sq_nonneg _))
    (Nat.cast_nonneg d)

/-- The exact source witness dominates every nonnegative coefficient pair
below `4^-8`. -/
theorem cmp89SourceNeumannPhysicalOneStepGate_lt_one_of_le_d4_M4_q8
    {etaFine etaCoarse : ℝ}
    (etaFine_nonneg : 0 ≤ etaFine)
    (etaCoarse_nonneg : 0 ≤ etaCoarse)
    (hfine : etaFine ≤ ((4 : ℝ)⁻¹) ^ 8)
    (hcoarse : etaCoarse ≤ ((4 : ℝ)⁻¹) ^ 8) :
    cmp99OneScaleBlockPoincareConstant 4 4 *
        cmp89SourceNeumannPhysicalOneStepDefectCoefficient
          4 4 etaFine etaCoarse < 1 := by
  calc
    cmp99OneScaleBlockPoincareConstant 4 4 *
        cmp89SourceNeumannPhysicalOneStepDefectCoefficient
          4 4 etaFine etaCoarse ≤
      cmp99OneScaleBlockPoincareConstant 4 4 *
        cmp89SourceNeumannPhysicalOneStepDefectCoefficient 4 4
          (((4 : ℝ)⁻¹) ^ 8) (((4 : ℝ)⁻¹) ^ 8) := by
            exact mul_le_mul_of_nonneg_left
              (cmp89SourceNeumannPhysicalOneStepDefectCoefficient_mono
                etaFine_nonneg etaCoarse_nonneg hfine hcoarse)
              (le_of_lt cmp99OneScaleBlockPoincareConstant_pos)
    _ < 1 := cmp89SourceNeumannPhysicalOneStepGate_d4_M4_q8_lt_one

/-- Literal radius form of the same gate.  The two radius inequalities are
the remaining source-flow obligations. -/
theorem cmp89SourceNeumannPhysicalOneStepGate_lt_one_of_radius_bounds_d4_M4
    {spacing epsilon nextRadius : ℝ}
    (hspacing : 0 < spacing)
    (epsilon_nonneg : 0 ≤ epsilon)
    (nextRadius_nonneg : 0 ≤ nextRadius)
    (hfine : epsilon ≤ spacing * (((4 : ℝ)⁻¹) ^ 8))
    (hcoarse : nextRadius ≤
      ((4 : ℝ) * spacing) * (((4 : ℝ)⁻¹) ^ 8)) :
    cmp99OneScaleBlockPoincareConstant 4 4 *
        cmp89SourceNeumannPhysicalOneStepDefectCoefficient 4 4
          (epsilon / spacing) (nextRadius / ((4 : ℝ) * spacing)) < 1 := by
  have hcoarseSpacing : 0 < (4 : ℝ) * spacing := mul_pos (by norm_num) hspacing
  apply cmp89SourceNeumannPhysicalOneStepGate_lt_one_of_le_d4_M4_q8
  · exact div_nonneg epsilon_nonneg hspacing.le
  · exact div_nonneg nextRadius_nonneg hcoarseSpacing.le
  · exact (div_le_iff₀ hspacing).2 (by simpa [mul_comm] using hfine)
  · exact (div_le_iff₀ hcoarseSpacing).2
      (by simpa [mul_comm] using hcoarse)

end

end YangMills.RG

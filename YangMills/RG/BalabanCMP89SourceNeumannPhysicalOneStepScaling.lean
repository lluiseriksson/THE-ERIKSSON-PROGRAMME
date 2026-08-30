import YangMills.RG.BalabanCMP89SourceNeumannQuantitativeOneScalePoincare
import YangMills.RG.BalabanCMP89SourceNeumannRecursiveAbsorptionStep

/-!
# Physical scaling of one CMP89 Neumann absorption step

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

The normalized derivative contributes `((M * spacing)⁻¹)²`.  Physical link
deviations at the fine and coarse scales carry respectively `spacing` and
`M * spacing`.  This leaf proves that those factors cancel exactly, rather
than hiding the convention in a generic constant.  If the next lattice
spacing has absolute value at most one, the quantitative one-scale Poincare
constant introduces no further spacing factor.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M : ℕ}
variable [NeZero d] [NeZero M]

/-- The dimensionless defect coefficient after the physical lattice-spacing
factors have been cancelled exactly. -/
noncomputable def cmp89SourceNeumannPhysicalOneStepDefectCoefficient
    (d M : ℕ) (etaFine etaCoarse : ℝ) : ℝ :=
  ‖((M : ℝ)⁻¹)‖ ^ 2 *
    (2 * ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine) +
      (M : ℝ) * etaCoarse)) ^ 2 * (d : ℝ)

/-- Exact cancellation of the fine lattice spacing in the one-step defect
coefficient.  The two deviation radii retain their different physical
units in the statement. -/
theorem cmp89SourceNeumannOneStepDefectCoefficient_physical_scaling
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (etaFine etaCoarse : ℝ) :
    cmp89SourceNeumannOneStepDefectCoefficient
        (d := d) (M := M) spacing (spacing * etaFine)
          (((M : ℝ) * spacing) * etaCoarse) =
      cmp89SourceNeumannPhysicalOneStepDefectCoefficient
        d M etaFine etaCoarse := by
  unfold cmp89SourceNeumannOneStepDefectCoefficient
    cmp89SourceNeumannPhysicalOneStepDefectCoefficient
    cmp99SourceTripleHolonomyRadius
  have hfactor :
      (((2 * d * (M - 1) + M : ℕ) : ℝ) * (spacing * etaFine) +
          (M : ℝ) * spacing * etaCoarse) =
        spacing *
          ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine) +
            (M : ℝ) * etaCoarse) := by
    ring
  rw [hfactor, mul_pow, mul_inv_rev, norm_mul]
  have hinv : ‖spacing⁻¹‖ ^ 2 * spacing ^ 2 = 1 := by
    rw [Real.norm_eq_abs, sq_abs, inv_pow]
    field_simp
  calc
    (‖(M : ℝ)⁻¹‖ * ‖spacing⁻¹‖) ^ 2 *
          (2 ^ 2 *
            (spacing ^ 2 *
              ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine +
                (M : ℝ) * etaCoarse) ^ 2)) *
          (d : ℝ) =
        ‖(M : ℝ)⁻¹‖ ^ 2 *
          (‖spacing⁻¹‖ ^ 2 * spacing ^ 2) *
          (2 *
            ((((2 * d * (M - 1) + M : ℕ) : ℝ) * etaFine) +
              (M : ℝ) * etaCoarse)) ^ 2 *
          (d : ℝ) := by ring
    _ = _ := by rw [hinv]; ring

/-- Under the next-scale spacing window, the full Poincare-times-defect
budget is exactly dimensionless. -/
theorem cmp89SourceNeumannOneScalePoincare_mul_defect_physical_scaling
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (hnext : |(M : ℝ) * spacing| ≤ 1)
    (etaFine etaCoarse : ℝ) :
    cmp89SourceNeumannOneScalePoincareConstant
        d M ((M : ℝ) * spacing) *
      cmp89SourceNeumannOneStepDefectCoefficient
        (d := d) (M := M) spacing (spacing * etaFine)
          (((M : ℝ) * spacing) * etaCoarse) =
      cmp99OneScaleBlockPoincareConstant d M *
        cmp89SourceNeumannPhysicalOneStepDefectCoefficient
          d M etaFine etaCoarse := by
  have hsq : ((M : ℝ) * spacing) ^ 2 ≤ 1 := by
    nlinarith [sq_abs ((M : ℝ) * spacing)]
  rw [cmp89SourceNeumannOneStepDefectCoefficient_physical_scaling
    (d := d) (M := M) hspacing]
  unfold cmp89SourceNeumannOneScalePoincareConstant
  rw [max_eq_right hsq]
  ring

/-- The physical smallness gate is literally the spacing-free scalar gate. -/
theorem cmp89SourceNeumannOneScalePoincare_mul_defect_lt_one_iff
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (hnext : |(M : ℝ) * spacing| ≤ 1)
    (etaFine etaCoarse : ℝ) :
    cmp89SourceNeumannOneScalePoincareConstant
          d M ((M : ℝ) * spacing) *
        cmp89SourceNeumannOneStepDefectCoefficient
          (d := d) (M := M) spacing (spacing * etaFine)
            (((M : ℝ) * spacing) * etaCoarse) < 1 ↔
      cmp99OneScaleBlockPoincareConstant d M *
        cmp89SourceNeumannPhysicalOneStepDefectCoefficient
          d M etaFine etaCoarse < 1 := by
  rw [cmp89SourceNeumannOneScalePoincare_mul_defect_physical_scaling
    (d := d) (M := M) hspacing hnext]

end

end YangMills.RG

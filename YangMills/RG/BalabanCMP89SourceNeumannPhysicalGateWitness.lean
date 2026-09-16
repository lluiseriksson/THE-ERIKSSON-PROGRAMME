import YangMills.RG.BalabanCMP89SourceNeumannPhysicalOneStepScaling

/-!
# A concrete source-regime witness for the physical Neumann gate

At the source dimension `d = 4`, block ratio `M = 4`, and the printed lower
power `q = 8`, choose both dimensionless deviation coefficients to be
`M^-q`.  The explicit one-scale Poincare constant times the spacing-free
defect coefficient then equals `27/512`, strictly below one.

This is a scalar compatibility witness.  It does not prove that a physical
RG background attains these deviation coefficients and does not attain
window 15 by itself.
-/

namespace YangMills.RG

noncomputable section

/-- Exact value of the physical absorption gate at the source witness
`d = 4`, `M = 4`, `q = 8`. -/
theorem cmp89SourceNeumannPhysicalOneStepGate_d4_M4_q8_eq :
    cmp99OneScaleBlockPoincareConstant 4 4 *
        cmp89SourceNeumannPhysicalOneStepDefectCoefficient 4 4
          (((4 : ℝ)⁻¹) ^ 8) (((4 : ℝ)⁻¹) ^ 8) =
      (27 : ℝ) / 512 := by
  norm_num [cmp99OneScaleBlockPoincareConstant,
    cmp89SourceNeumannPhysicalOneStepDefectCoefficient, max_eq_left]

/-- The concrete source-regime physical absorption gate is inhabited. -/
theorem cmp89SourceNeumannPhysicalOneStepGate_d4_M4_q8_lt_one :
    cmp99OneScaleBlockPoincareConstant 4 4 *
        cmp89SourceNeumannPhysicalOneStepDefectCoefficient 4 4
          (((4 : ℝ)⁻¹) ^ 8) (((4 : ℝ)⁻¹) ^ 8) < 1 := by
  rw [cmp89SourceNeumannPhysicalOneStepGate_d4_M4_q8_eq]
  norm_num

end

end YangMills.RG

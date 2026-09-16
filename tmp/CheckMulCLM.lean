import YangMills.RG.BalabanCMP102AmbientOrientedEdgeThirdJetBound
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
example (n : ℕ) : ‖ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro B
  exact norm_mul_le A B

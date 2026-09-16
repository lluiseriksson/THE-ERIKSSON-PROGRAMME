import YangMills.RG.BalabanCMP102AmbientLocalNearLogBudget
open YangMills YangMills.RG Matrix
open scoped Matrix.Norms.L2Operator
variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
local instance test : NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]; simp
#synth Norm (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ)
#synth SeminormedAddCommGroup (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ)

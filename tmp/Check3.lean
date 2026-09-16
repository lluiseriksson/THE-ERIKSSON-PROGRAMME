import YangMills.RG.BalabanCMP102AmbientLocalNearLogBudget
open YangMills YangMills.RG Matrix
open scoped Matrix.Norms.L2Operator
variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
#synth Norm (Matrix (Fin Nc) (Fin Nc) ℂ)
#synth SeminormedAddCommGroup (Matrix (Fin Nc) (Fin Nc) ℂ)
#synth NormedSpace ℝ (Matrix (Fin Nc) (Fin Nc) ℂ)
#synth Norm (PhysicalAmbientMatrixTangent d (M * N') Nc)
#synth SeminormedAddCommGroup (PhysicalAmbientMatrixTangent d (M * N') Nc)
#synth NormedSpace ℝ (PhysicalAmbientMatrixTangent d (M * N') Nc)

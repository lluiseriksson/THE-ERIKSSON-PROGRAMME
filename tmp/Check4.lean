import YangMills.RG.BalabanCMP102AmbientLocalNearLogBudget
open YangMills YangMills.RG Matrix
open scoped Matrix.Norms.L2Operator
variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
local instance clmNorm : Norm (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ) := ContinuousLinearMap.hasOpNorm
local instance clmSemi : SeminormedAddCommGroup (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ) := ContinuousLinearMap.toSeminormedAddCommGroup
#synth Norm (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ)
#synth SeminormedAddCommGroup (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ)

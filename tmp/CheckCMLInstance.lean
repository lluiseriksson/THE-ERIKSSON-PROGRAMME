import YangMills.RG.BalabanCMP102AmbientOrientedEdgeThirdJetBound
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
variable {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
#synth SeminormedAddCommGroup (Matrix (Fin Nc) (Fin Nc) ℂ)
#synth SeminormedAddCommGroup (YangMills.RG.PhysicalAmbientMatrixTangent d (M*N') Nc →L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ)
#synth SeminormedAddCommGroup (YangMills.RG.PhysicalAmbientMatrixTangent d (M*N') Nc [×2]→L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ)

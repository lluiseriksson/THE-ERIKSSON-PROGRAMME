import YangMills.RG.BalabanCMP102AmbientOrientedEdgeFDerivBound

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

#synth NormedAddCommGroup (Matrix (Fin Nc) (Fin Nc) ℂ)
#synth NormedSpace ℝ (Matrix (Fin Nc) (Fin Nc) ℂ)
#synth NormedAddCommGroup (PhysicalAmbientMatrixTangent d N Nc)
#synth NormedSpace ℝ (PhysicalAmbientMatrixTangent d N Nc)
#check ContinuousLinearMap.hasOpNorm
#synth Norm
  (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ]
    Matrix (Fin Nc) (Fin Nc) ℂ)
#synth Norm
  (PhysicalAmbientMatrixTangent d N Nc →L[ℝ]
    Matrix (Fin Nc) (Fin Nc) ℂ)

end YangMills.RG

import YangMills.RG.BalabanCMP102PhysicalIntrinsicCorrectionAnalytic
open scoped Matrix.Norms.L2Operator
open YangMills Matrix
namespace YangMills.RG
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup F] [NormedSpace ℝ F]
 (L : E →L[ℝ] F) (x:E) : iteratedFDeriv ℝ 3 L x = 0 := by
  ext m
  rw [iteratedFDeriv_succ_apply_right]
  simp only [L.fderiv, iteratedFDeriv_const_of_ne (by omega : 2 ≠ 0)]
  simp
end YangMills.RG

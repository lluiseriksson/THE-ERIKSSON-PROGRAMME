import YangMills.RG.BalabanCMP116WilsonHessianOperator
import YangMills.RG.PhysicalGramKernel

/-!
# Exact finite range of the literal Wilson-Hessian operator

The plaquette-support theorem gives vanishing of the literal bilinear Hessian
between distant bond probes.  The canonical Riesz operator turns that
statement into the source-facing `PhysicalCovarianceFiniteRange` interface
used by the repository's Combes--Thomas machinery.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- **Operator-level WIL-H4 locality.** At every physical background, the
literal Wilson-Hessian operator has exact physical bond range two. -/
theorem physicalWilsonHessianCLM_finiteRange
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalCovarianceFiniteRange
      (physicalWilsonHessianCLM U) physicalBondDist 2 := by
  intro source target v hfar
  apply ext_inner_right ℝ
  intro w
  rw [inner_zero_left]
  rw [← inner_singlePhysicalBondCochain_right]
  rw [inner_physicalWilsonHessianCLM]
  exact physicalWilsonHessian_single_eq_zero_of_dist_gt_two
    U source target v w hfar

end

end YangMills.RG

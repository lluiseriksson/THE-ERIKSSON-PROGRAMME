import YangMills.RG.BalabanCMP89NeumannRectangularPhysicalGreenInsertion

/-!
# Compiler-verified summability of the real-slice CMP89 reflection series

Cold-sealed at source checkpoint `cdd859ba99671e83a1ef2b3d8119a4e376a97ced`;
see Verification Ledger Addendum 1003.

This module transports the already sealed complex full-space Green
summability to the literal real scalar used by the regional real-fibre
action. No reflection identity or inverse law is asserted.
-/

namespace YangMills.RG

noncomputable section

/-- The real part of the literal complex CMP89 (2.48) Green retains absolute
summability over every positive-side Neumann image family. -/
theorem summable_cmp89Eq248PhysicalRealNeumannReflection_sum
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {m x n : Fin 4 → ℤ} (hm : ∀ mu, 0 < m mu) :
    Summable (fun k : Fin 4 → ℤ =>
      ∑ branch : CMP89NeumannReflectionBranch 4,
        (cmp89Eq248PhysicalFullLatticeGreen L j mass a x
          (cmp89NeumannReflectionImage m n k branch)).re) := by
  have hcomplex : Summable (fun k : Fin 4 → ℤ =>
      ∑ branch : CMP89NeumannReflectionBranch 4,
        cmp89Eq248PhysicalFullLatticeGreen L j mass a x
          (cmp89NeumannReflectionImage m n k branch)) :=
    summable_cmp89NeumannRectangularFullGreen_sum
      (cmp89Eq248PhysicalFullLatticeGreenDecayCertificate_draft
        ha hrho hamplitude hradius hwindow hmass)
      hm
  apply Summable.of_norm_bounded hcomplex.norm
  intro k
  rw [Real.norm_eq_abs]
  rw [← Complex.re_sum]
  exact Complex.abs_re_le_norm _

end

end YangMills.RG

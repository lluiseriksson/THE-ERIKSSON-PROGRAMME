import YangMills.RG.BalabanCMP116RadialTaylorSupport
import YangMills.RG.BalabanCMP116Eq220PhysicalPotential

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

noncomputable def testPhysicalRadialQuadratic
    {d N Nc : ℕ} [NeZero N]
    (f : PhysicalGaugeOneCochain d N Nc → ℝ)
    (hf : ContDiff ℝ 2 f)
    (B : PhysicalGaugeOneCochain d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  cmp116RadialTaylorOperator f B hf

theorem testPhysicalRadialQuadratic_eq_activity
    {d N Nc : ℕ} [NeZero N]
    (f : PhysicalGaugeOneCochain d N Nc → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0)
    (B : PhysicalGaugeOneCochain d N Nc) :
    (1 / 2 : ℝ) * inner ℝ B (testPhysicalRadialQuadratic f hf B B) = f B := by
  exact (cmp116RadialTaylorOperator_eq_of_normalized f B hf hf0 hdf0).symm

theorem testEq142PhysicalPotentialTerm_radial
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (potential remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2 (potential y))
    (hzero : ∀ y, potential y 0 = 0)
    (hlinear : ∀ y, fderiv ℝ (potential y) 0 = 0)
    (y : Y) (B : PhysicalGaugeOneCochain d N Nc) :
    cmp116Eq142PhysicalPotentialTerm
        (fun y B => testPhysicalRadialQuadratic (potential y) (hsmooth y) B)
        remainder y B =
      potential y B + remainder y B := by
  unfold cmp116Eq142PhysicalPotentialTerm
  rw [testPhysicalRadialQuadratic_eq_activity
    (potential y) (hsmooth y) (hzero y) (hlinear y) B]

end

end YangMills.RG

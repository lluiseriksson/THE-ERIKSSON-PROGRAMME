import YangMills.RG.BalabanCMP116RadialTaylorSupport
import YangMills.RG.BalabanCMP116Eq220PhysicalPotential

/-!
# Radial Taylor dictionary for CMP116 equation (1.42)

This file specializes the radial Taylor operator to the finite physical gauge
one-cochain space.  For a normalized `C^2` localized potential it constructs
the field-dependent operator `Q(Y,B)` internally and proves the literal
equation-(1.42) decomposition

`V_k(Y,B) = (1/2) <B,Q(Y,B)B>`.

Consequently, the existing two-piece Lean potential term reduces exactly to

`V_k(Y,B) + V''_k(Y,B)`.

Honest scope: the localized physical potential, its `C^2` regularity, and the
normalizations at the origin remain inputs.  This module removes an arbitrary
quadratic operator from the interface; it does not manufacture the potential
or the residual term from a synthetic summand.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

/-- The physical field-dependent quadratic operator built from the radial
Taylor average of a real localized potential. -/
noncomputable def cmp116Eq142PhysicalRadialQuadratic
    {d N Nc : ℕ} [NeZero N]
    (f : PhysicalGaugeOneCochain d N Nc → ℝ)
    (hf : ContDiff ℝ 2 f)
    (B : PhysicalGaugeOneCochain d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  cmp116RadialTaylorOperator f B hf

/-- Exact equation-(1.42) quadratic identity on the physical field space. -/
theorem inner_cmp116Eq142PhysicalRadialQuadratic_eq_activity
    {d N Nc : ℕ} [NeZero N]
    (f : PhysicalGaugeOneCochain d N Nc → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0)
    (B : PhysicalGaugeOneCochain d N Nc) :
    (1 / 2 : ℝ) * inner ℝ B
        (cmp116Eq142PhysicalRadialQuadratic f hf B B) = f B := by
  exact (cmp116RadialTaylorOperator_eq_of_normalized f B hf hf0 hdf0).symm

/-- The literal two-piece potential term from equation (1.42), with its
quadratic operator constructed rather than supplied. -/
theorem cmp116Eq142PhysicalPotentialTerm_radial
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (potential remainder : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2 (potential y))
    (hzero : ∀ y, potential y 0 = 0)
    (hlinear : ∀ y, fderiv ℝ (potential y) 0 = 0)
    (y : Y) (B : PhysicalGaugeOneCochain d N Nc) :
    cmp116Eq142PhysicalPotentialTerm
        (fun y B =>
          cmp116Eq142PhysicalRadialQuadratic (potential y) (hsmooth y) B)
        remainder y B =
      potential y B + remainder y B := by
  unfold cmp116Eq142PhysicalPotentialTerm
  rw [inner_cmp116Eq142PhysicalRadialQuadratic_eq_activity
    (potential y) (hsmooth y) (hzero y) (hlinear y) B]

end

end YangMills.RG

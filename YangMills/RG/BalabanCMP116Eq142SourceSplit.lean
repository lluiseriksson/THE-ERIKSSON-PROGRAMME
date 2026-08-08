import YangMills.RG.BalabanCMP116Eq142RadialDictionary

/-!
# Source-faithful split in CMP116 equation (1.42)

The printed source identity is

`V_k(Y,B) = (1/2) <Q(Y,B) B, B> + V''_k(Y,B)`.

Consequently, the function to which the radial Taylor construction applies is
not the complete localized activity `V_k`, but the specified quadratic core

`F_Y(B) = V_k(Y,B) - V''_k(Y,B)`.

This file fixes that dictionary in the interface.  Given the total localized
activity and the separately specified source residual, it constructs `Q` from
the radial Hessian average of `F_Y` and reconstructs the total activity
exactly.  In particular, the residual cannot silently be chosen to be zero by
instantiating the radial construction with the full activity.

Honest scope: identifying the concrete CMP116 functions `V_k` and `V''_k`,
proving the core normalizations, the matrix-element estimate (1.43), and the
residual estimate (1.36) remain explicit source-facing obligations.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

/-- The source quadratic core `F_Y = V_k - V''_k`. -/
noncomputable def cmp116Eq142PhysicalQuadraticCore
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (total residual : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (y : Y) (B : PhysicalGaugeOneCochain d N Nc) : ℝ :=
  total y B - residual y B

/-- The field-dependent operator constructed from the radial Taylor average
of the source quadratic core, rather than from the complete activity. -/
noncomputable def cmp116Eq142PhysicalSourceQuadratic
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (total residual : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore total residual y))
    (y : Y) (B : PhysicalGaugeOneCochain d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  cmp116Eq142PhysicalRadialQuadratic
    (cmp116Eq142PhysicalQuadraticCore total residual y) (hsmooth y) B

/-- Exact reconstruction of the quadratic core from its source-faithful
radial operator. -/
theorem inner_cmp116Eq142PhysicalSourceQuadratic_eq_core
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (total residual : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore total residual y))
    (hzero : ∀ y, cmp116Eq142PhysicalQuadraticCore total residual y 0 = 0)
    (hlinear : ∀ y,
      fderiv ℝ (cmp116Eq142PhysicalQuadraticCore total residual y) 0 = 0)
    (y : Y) (B : PhysicalGaugeOneCochain d N Nc) :
    (1 / 2 : ℝ) * inner ℝ B
        (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth y B B) =
      cmp116Eq142PhysicalQuadraticCore total residual y B := by
  exact inner_cmp116Eq142PhysicalRadialQuadratic_eq_activity
    (cmp116Eq142PhysicalQuadraticCore total residual y)
    (hsmooth y) (hzero y) (hlinear y) B

/-- Source-faithful equation-(1.42): the quadratic operator is generated from
`V_k - V''_k`, the specified residual is restored, and the result is exactly
the original total localized activity. -/
theorem cmp116Eq142PhysicalPotentialTerm_sourceSplit
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (total residual : Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore total residual y))
    (hzero : ∀ y, cmp116Eq142PhysicalQuadraticCore total residual y 0 = 0)
    (hlinear : ∀ y,
      fderiv ℝ (cmp116Eq142PhysicalQuadraticCore total residual y) 0 = 0)
    (y : Y) (B : PhysicalGaugeOneCochain d N Nc) :
    cmp116Eq142PhysicalPotentialTerm
        (cmp116Eq142PhysicalSourceQuadratic total residual hsmooth)
        residual y B = total y B := by
  unfold cmp116Eq142PhysicalPotentialTerm
  rw [inner_cmp116Eq142PhysicalSourceQuadratic_eq_core
    total residual hsmooth hzero hlinear y B]
  unfold cmp116Eq142PhysicalQuadraticCore
  ring

end

end YangMills.RG

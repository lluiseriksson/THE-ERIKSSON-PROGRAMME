/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RadialTaylorResidual

/-!
# Absorbing the radial cubic residual into the quadratic budget

The radial Taylor residual is cubic.  On literal small-field cutoff support
the norm of its argument is bounded, so one power is paid by the cutoff
radius and the remaining two powers enter the quadratic interaction rate.

This is the scalar bridge needed to place the interpolation-center part of
the residual in `potentialRate`, leaving the contour displacement for the
equation-(2.20) domain ledger.  No source-specific jet estimate or cutoff
radius is manufactured here.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- A nonnegative cubic coefficient becomes a quadratic coefficient on a
norm ball. -/
theorem cubic_le_threshold_mul_sq
    {E : Type*} [Norm E]
    (B : E) {threshold c : ℝ}
    (hc : 0 ≤ c) (hB : ‖B‖ ≤ threshold) :
    c * ‖B‖ ^ 3 ≤ c * threshold * ‖B‖ ^ 2 := by
  calc
    c * ‖B‖ ^ 3 = c * (‖B‖ * ‖B‖ ^ 2) := by ring
    _ ≤ c * (threshold * ‖B‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact mul_le_mul_of_nonneg_right hB (sq_nonneg _)
    _ = c * threshold * ‖B‖ ^ 2 := by ring

/-- The exact `Λ/6` radial residual estimate becomes a quadratic interaction
rate `Λ * threshold / 6` on cutoff support. -/
theorem abs_half_inner_cmp116RadialTaylorResidualOperator_le_quadratic_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f)
    (Λ threshold : ℝ) (hΛ : 0 ≤ Λ)
    (hlip : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |cmp116FDerivHessian f (t • B) B B -
        cmp116FDerivHessian f 0 B B| ≤
          Λ * t * ‖B‖ * ‖B‖ * ‖B‖)
    (hB : ‖B‖ ≤ threshold) :
    |(1 / 2 : ℝ) *
      inner ℝ B (cmp116RadialTaylorResidualOperator f B hf B)| ≤
        (Λ * threshold / 6) * ‖B‖ ^ 2 := by
  calc
    |(1 / 2 : ℝ) *
        inner ℝ B (cmp116RadialTaylorResidualOperator f B hf B)| ≤
      (Λ / 6) * ‖B‖ ^ 3 :=
        abs_half_inner_cmp116RadialTaylorResidualOperator_le_one_sixth
          f B hf Λ hlip
    _ ≤ (Λ / 6) * threshold * ‖B‖ ^ 2 :=
      cubic_le_threshold_mul_sq B (div_nonneg hΛ (by norm_num)) hB
    _ = (Λ * threshold / 6) * ‖B‖ ^ 2 := by ring

end

end YangMills.RG

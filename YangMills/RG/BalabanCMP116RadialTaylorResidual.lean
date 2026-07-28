/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RadialTaylorBound

/-!
# The genuine residual of the radial Taylor operator

For a normalized `C²` functional,

`f(B) = (1 / 2) ⟪B, Q_f(B) B⟫`.

This identity alone does **not** make `f` a fixed quadratic functional:
`Q_f(B)` depends on the field.  The fixed quadratic part is `Q_f(0)` and
the genuine higher-order radial residual is therefore

`Q_f(B) - Q_f(0)`.

This file constructs that difference, proves the exact split, and identifies
its matrix elements with the radial average of the Hessian difference
`D²f(tB) - D²f(0)`.  It does not claim an equation-(1.36) bound; such a bound
must come from a quantitative modulus of continuity for the physical
Hessian.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

open MeasureTheory Set
open scoped Interval

namespace YangMills.RG

noncomputable section

/-- The field-dependent part of the radial Taylor operator. -/
noncomputable def cmp116RadialTaylorResidualOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) : E →L[ℝ] E :=
  cmp116RadialTaylorOperator f B hf -
    cmp116RadialTaylorOperator f 0 hf

/-- Pure algebra behind the fixed-plus-residual split.  Keeping this lemma
independent of the physical producer prevents large source expressions from
being normalized by `ring` downstream. -/
theorem eq_fixedQuadratic_add_residual_of_eq_radial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (Q : E → E →L[ℝ] E) (B : E)
    (h : f B = (1 / 2 : ℝ) * inner ℝ B (Q B B)) :
    f B =
      (1 / 2 : ℝ) * inner ℝ B (Q 0 B) +
        (1 / 2 : ℝ) * inner ℝ B ((Q B - Q 0) B) := by
  rw [h, ContinuousLinearMap.sub_apply, inner_sub_right]
  ring

/-- At the origin, the radial Taylor operator is exactly the Fréchet
Hessian, not merely an averaged surrogate. -/
theorem inner_cmp116RadialTaylorOperator_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (A A' : E) (hf : ContDiff ℝ 2 f) :
    inner ℝ A (cmp116RadialTaylorOperator f 0 hf A') =
      cmp116FDerivHessian f 0 A' A := by
  rw [inner_cmp116RadialTaylorOperator]
  simp only [smul_zero]
  rw [intervalIntegral.integral_mul_const]
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - t) t := by
    intro t ht
    convert (hasDerivAt_id t).sub
      (((hasDerivAt_id t).pow 2).div_const 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hint : IntervalIntegrable (fun t : ℝ => 1 - t) volume 0 1 :=
    (continuous_const.sub continuous_id).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- Exact matrix-element formula for the residual operator. -/
theorem inner_cmp116RadialTaylorResidualOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 2 f) :
    inner ℝ A (cmp116RadialTaylorResidualOperator f B hf A') =
      2 * ∫ t in (0 : ℝ)..1,
        (1 - t) *
          (cmp116FDerivHessian f (t • B) A' A -
            cmp116FDerivHessian f 0 A' A) := by
  unfold cmp116RadialTaylorResidualOperator
  rw [ContinuousLinearMap.sub_apply, inner_sub_right,
    inner_cmp116RadialTaylorOperator,
    inner_cmp116RadialTaylorOperator]
  have hB := cmp116RadialHessian_intervalIntegrable f B A' A hf
  have h0 := cmp116RadialHessian_intervalIntegrable f (0 : E) A' A hf
  have heq0 :
      (fun t : ℝ =>
        (1 - t) * cmp116FDerivHessian f (t • (0 : E)) A' A) =
      (fun t : ℝ =>
        (1 - t) * cmp116FDerivHessian f 0 A' A) := by
    funext t
    simp
  rw [heq0] at h0
  rw [heq0]
  calc
    2 * (∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) A' A) -
        2 * (∫ t in (0 : ℝ)..1,
          (1 - t) * cmp116FDerivHessian f 0 A' A) =
        2 * ((∫ t in (0 : ℝ)..1,
          (1 - t) * cmp116FDerivHessian f (t • B) A' A) -
          ∫ t in (0 : ℝ)..1,
            (1 - t) * cmp116FDerivHessian f 0 A' A) := by ring
    _ = 2 * ∫ t in (0 : ℝ)..1,
        ((1 - t) * cmp116FDerivHessian f (t • B) A' A -
          (1 - t) * cmp116FDerivHessian f 0 A' A) := by
      rw [intervalIntegral.integral_sub hB h0]
    _ = 2 * ∫ t in (0 : ℝ)..1,
        (1 - t) *
          (cmp116FDerivHessian f (t • B) A' A -
            cmp116FDerivHessian f 0 A' A) := by
      congr 2
      funext t
      ring

/-- A uniform bound on the Hessian variation along the radial segment passes
to the residual operator with no loss.  This is the correct quantitative
interface for a future equation-(1.36) producer: it bounds
`D²f(tB) - D²f(0)`, not `D²f(tB)` itself. -/
theorem abs_inner_cmp116RadialTaylorResidualOperator_le_of_hessian_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 2 f)
    (C : ℝ)
    (hhess : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |cmp116FDerivHessian f (t • B) A' A -
        cmp116FDerivHessian f 0 A' A| ≤ C) :
    |inner ℝ A (cmp116RadialTaylorResidualOperator f B hf A')| ≤ C := by
  rw [inner_cmp116RadialTaylorResidualOperator]
  have hmajorInt :
      IntervalIntegrable (fun t : ℝ => (1 - t) * C) volume 0 1 :=
    ((continuous_const.sub continuous_id).mul continuous_const)
      |>.intervalIntegrable 0 1
  have hnorm : ‖∫ t in (0 : ℝ)..1,
      (1 - t) *
        (cmp116FDerivHessian f (t • B) A' A -
          cmp116FDerivHessian f 0 A' A)‖ ≤
      ∫ t in (0 : ℝ)..1, (1 - t) * C := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall ?_) hmajorInt
    intro t ht
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left
      (hhess t ⟨le_of_lt ht.1, ht.2⟩) ht0
  have hweight : (∫ t in (0 : ℝ)..1, (1 - t) * C) = C / 2 := by
    rw [intervalIntegral.integral_mul_const]
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - t) t := by
      intro t ht
      convert (hasDerivAt_id t).sub
        (((hasDerivAt_id t).pow 2).div_const 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hint : IntervalIntegrable (fun t : ℝ => 1 - t) volume 0 1 :=
      (continuous_const.sub continuous_id).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    ring
  rw [hweight] at hnorm
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2 * |∫ t in (0 : ℝ)..1,
        (1 - t) *
          (cmp116FDerivHessian f (t • B) A' A -
            cmp116FDerivHessian f 0 A' A)| =
        2 * ‖∫ t in (0 : ℝ)..1,
          (1 - t) *
            (cmp116FDerivHessian f (t • B) A' A -
              cmp116FDerivHessian f 0 A' A)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ 2 * (C / 2) :=
      mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = C := by ring

/-- A radial Lipschitz estimate for the Hessian produces the genuine
third-order gain.  The factor `1 / 3` is exact:

`2 * integral t in 0..1, (1 - t) * t = 1 / 3`.

The parameter `Λ` is deliberately not identified with a domain-independent
constant here.  A physical equation-(1.36) producer must supply a
domain-dependent `Λ(Y)` with the required source-metric decay. -/
theorem abs_inner_cmp116RadialTaylorResidualOperator_le_one_third
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 2 f)
    (Λ : ℝ)
    (hlip : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |cmp116FDerivHessian f (t • B) A' A -
        cmp116FDerivHessian f 0 A' A| ≤
          Λ * t * ‖B‖ * ‖A‖ * ‖A'‖) :
    |inner ℝ A (cmp116RadialTaylorResidualOperator f B hf A')| ≤
      (Λ / 3) * ‖B‖ * ‖A‖ * ‖A'‖ := by
  rw [inner_cmp116RadialTaylorResidualOperator]
  have hmajorInt : IntervalIntegrable
      (fun t : ℝ => (1 - t) * (Λ * t * ‖B‖ * ‖A‖ * ‖A'‖))
      volume 0 1 := by
    have hproduct : Continuous (fun t : ℝ =>
        Λ * t * ‖B‖ * ‖A‖ * ‖A'‖) :=
      (((continuous_const.mul continuous_id).mul continuous_const).mul
        continuous_const).mul continuous_const
    exact ((continuous_const.sub continuous_id).mul hproduct).intervalIntegrable 0 1
  have hnorm : ‖∫ t in (0 : ℝ)..1,
      (1 - t) *
        (cmp116FDerivHessian f (t • B) A' A -
          cmp116FDerivHessian f 0 A' A)‖ ≤
      ∫ t in (0 : ℝ)..1,
        (1 - t) * (Λ * t * ‖B‖ * ‖A‖ * ‖A'‖) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall ?_) hmajorInt
    intro t ht
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left
      (hlip t ⟨le_of_lt ht.1, ht.2⟩) ht0
  have hweight : (∫ t in (0 : ℝ)..1,
      (1 - t) * (Λ * t * ‖B‖ * ‖A‖ * ‖A'‖)) =
      (Λ * ‖B‖ * ‖A‖ * ‖A'‖) / 6 := by
    have heq : (fun t : ℝ =>
        (1 - t) * (Λ * t * ‖B‖ * ‖A‖ * ‖A'‖)) =
        fun t : ℝ =>
          (t - t ^ 2) * (Λ * ‖B‖ * ‖A‖ * ‖A'‖) := by
      funext t
      ring
    rw [heq, intervalIntegral.integral_mul_const]
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => s ^ 2 / 2 - s ^ 3 / 3)
          (t - t ^ 2) t := by
      intro t ht
      convert (((hasDerivAt_id t).pow 2).div_const 2).sub
        (((hasDerivAt_id t).pow 3).div_const 3) using 1 <;>
        simp only [id_eq] <;> ring
    have hint : IntervalIntegrable (fun t : ℝ => t - t ^ 2)
        volume 0 1 :=
      (continuous_id.sub (continuous_id.pow 2)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    ring
  rw [hweight] at hnorm
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2 * |∫ t in (0 : ℝ)..1,
        (1 - t) *
          (cmp116FDerivHessian f (t • B) A' A -
            cmp116FDerivHessian f 0 A' A)| =
        2 * ‖∫ t in (0 : ℝ)..1,
          (1 - t) *
            (cmp116FDerivHessian f (t • B) A' A -
              cmp116FDerivHessian f 0 A' A)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ 2 * ((Λ * ‖B‖ * ‖A‖ * ‖A'‖) / 6) :=
      mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = (Λ / 3) * ‖B‖ * ‖A‖ * ‖A'‖ := by ring

/-- Diagonal specialization of the preceding estimate.  The scalar radial
residual is third order in the field with the exact coefficient `Λ / 6`. -/
theorem abs_half_inner_cmp116RadialTaylorResidualOperator_le_one_sixth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f)
    (Λ : ℝ)
    (hlip : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |cmp116FDerivHessian f (t • B) B B -
        cmp116FDerivHessian f 0 B B| ≤
          Λ * t * ‖B‖ * ‖B‖ * ‖B‖) :
    |(1 / 2 : ℝ) *
      inner ℝ B (cmp116RadialTaylorResidualOperator f B hf B)| ≤
        (Λ / 6) * ‖B‖ ^ 3 := by
  have hinner :=
    abs_inner_cmp116RadialTaylorResidualOperator_le_one_third
      f B B B hf Λ hlip
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]
  calc
    (1 / 2 : ℝ) *
        |inner ℝ B (cmp116RadialTaylorResidualOperator f B hf B)| ≤
      (1 / 2 : ℝ) * ((Λ / 3) * ‖B‖ * ‖B‖ * ‖B‖) :=
        mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ = (Λ / 6) * ‖B‖ ^ 3 := by ring

/-- Exact source-normalized split into the fixed quadratic operator `Q_f(0)`
and the genuine field-dependent residual `Q_f(B) - Q_f(0)`. -/
theorem cmp116RadialTaylorOperator_eq_fixed_add_residual_of_normalized
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0) :
    f B =
      (1 / 2 : ℝ) *
          inner ℝ B (cmp116RadialTaylorOperator f 0 hf B) +
        (1 / 2 : ℝ) *
          inner ℝ B (cmp116RadialTaylorResidualOperator f B hf B) := by
  rw [cmp116RadialTaylorOperator_eq_of_normalized f B hf hf0 hdf0]
  unfold cmp116RadialTaylorResidualOperator
  rw [ContinuousLinearMap.sub_apply, inner_sub_right]
  ring

/-- The scalar residual after subtracting the fixed quadratic term is exactly
the diagonal value of the residual operator. -/
theorem cmp116RadialTaylor_scalarResidual_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0) :
    f B -
        (1 / 2 : ℝ) *
          inner ℝ B (cmp116RadialTaylorOperator f 0 hf B) =
      (1 / 2 : ℝ) *
        inner ℝ B (cmp116RadialTaylorResidualOperator f B hf B) := by
  rw [cmp116RadialTaylorOperator_eq_fixed_add_residual_of_normalized
    f B hf hf0 hdf0]
  ring

end

end YangMills.RG

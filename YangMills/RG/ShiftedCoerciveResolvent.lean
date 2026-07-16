/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.CoerciveCovariance

/-!
# Shifted resolvents of coercive precision operators

For a finite-dimensional real Hilbert space and a coercive precision `K`,
this module constructs the exact shifted resolvent

`R_K(t) = (K + t I)⁻¹`,  `t ≥ 0`,

from the existing coercive inverse.  It proves:

* coercivity of `K + t I` with margin `c + t`;
* both exact inverse identities;
* the uniform bound `‖R_K(t)‖ ≤ (c + t)⁻¹`;
* both noncommutative second-resolvent factorizations;
* the two-margin norm estimate
  `‖R₁(t)-R₀(t)‖ ≤ (c₁+t)⁻¹ ‖K₀-K₁‖ (c₀+t)⁻¹`.

This is the resolvent layer needed for the future Bochner representation of
`K⁻¹ᐟ²`.  No square root or integral representation is claimed here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

/-- The positive real shift `K + t I` of a precision operator. -/
def shiftedPrecisionCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : E →L[ℝ] E) (t : ℝ) :
    E →L[ℝ] E :=
  K + t • ContinuousLinearMap.id ℝ E

@[simp]
theorem shiftedPrecisionCLM_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : E →L[ℝ] E) (t : ℝ) (x : E) :
    shiftedPrecisionCLM K t x = K x + t • x := by
  rfl

/-- A scalar shift raises the coercivity margin by exactly the same scalar. -/
theorem isCoerciveCLM_shiftedPrecisionCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : E →L[ℝ] E) {c t : ℝ}
    (hK : IsCoerciveCLM K c) :
    IsCoerciveCLM (shiftedPrecisionCLM K t) (c + t) := by
  intro x
  calc
    (c + t) * ‖x‖ ^ 2 =
        c * ‖x‖ ^ 2 + t * ‖x‖ ^ 2 := by ring
    _ ≤ inner ℝ x (K x) + t * ‖x‖ ^ 2 :=
      add_le_add (hK x) le_rfl
    _ = inner ℝ x (shiftedPrecisionCLM K t x) := by
      rw [shiftedPrecisionCLM_apply, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq]

/-- Shifts cancel in the precision defect. -/
theorem shiftedPrecisionCLM_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K₀ K₁ : E →L[ℝ] E) (t : ℝ) :
    shiftedPrecisionCLM K₀ t - shiftedPrecisionCLM K₁ t = K₀ - K₁ := by
  apply ContinuousLinearMap.ext
  intro x
  simp

/-- Exact shifted resolvent obtained from strict coercivity. -/
noncomputable def shiftedResolventOfIsCoerciveCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hK : IsCoerciveCLM K c) (t : ℝ) (ht : 0 ≤ t) :
    E →L[ℝ] E :=
  covarianceOfIsCoerciveCLM
    (shiftedPrecisionCLM K t)
    (add_pos_of_pos_of_nonneg hc ht)
    (isCoerciveCLM_shiftedPrecisionCLM K hK)

/-- The shifted resolvent is a left inverse. -/
@[simp]
theorem shiftedResolventOfIsCoerciveCLM_apply_precision
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hK : IsCoerciveCLM K c) (t : ℝ) (ht : 0 ≤ t) (x : E) :
    shiftedResolventOfIsCoerciveCLM K hc hK t ht
        (shiftedPrecisionCLM K t x) = x := by
  exact covarianceOfIsCoerciveCLM_apply_precision
    (shiftedPrecisionCLM K t)
    (add_pos_of_pos_of_nonneg hc ht)
    (isCoerciveCLM_shiftedPrecisionCLM K hK) x

/-- The shifted resolvent is a right inverse. -/
@[simp]
theorem shiftedPrecisionCLM_apply_shiftedResolvent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hK : IsCoerciveCLM K c) (t : ℝ) (ht : 0 ≤ t) (x : E) :
    shiftedPrecisionCLM K t
        (shiftedResolventOfIsCoerciveCLM K hc hK t ht x) = x := by
  exact precision_apply_covarianceOfIsCoerciveCLM
    (shiftedPrecisionCLM K t)
    (add_pos_of_pos_of_nonneg hc ht)
    (isCoerciveCLM_shiftedPrecisionCLM K hK) x

/-- Operator-level left-inverse identity. -/
theorem shiftedResolvent_comp_shiftedPrecision
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hK : IsCoerciveCLM K c) (t : ℝ) (ht : 0 ≤ t) :
    (shiftedResolventOfIsCoerciveCLM K hc hK t ht).comp
        (shiftedPrecisionCLM K t) =
      ContinuousLinearMap.id ℝ E := by
  ext x
  exact shiftedResolventOfIsCoerciveCLM_apply_precision
    K hc hK t ht x

/-- Operator-level right-inverse identity. -/
theorem shiftedPrecision_comp_shiftedResolvent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hK : IsCoerciveCLM K c) (t : ℝ) (ht : 0 ≤ t) :
    (shiftedPrecisionCLM K t).comp
        (shiftedResolventOfIsCoerciveCLM K hc hK t ht) =
      ContinuousLinearMap.id ℝ E := by
  ext x
  exact shiftedPrecisionCLM_apply_shiftedResolvent
    K hc hK t ht x

/-- Uniform shifted-resolvent estimate `‖(K+tI)⁻¹‖ ≤ (c+t)⁻¹`. -/
theorem norm_shiftedResolventOfIsCoerciveCLM_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hK : IsCoerciveCLM K c) (t : ℝ) (ht : 0 ≤ t) :
    ‖shiftedResolventOfIsCoerciveCLM K hc hK t ht‖ ≤ (c + t)⁻¹ := by
  exact norm_covarianceOfIsCoerciveCLM_le
    (shiftedPrecisionCLM K t)
    (add_pos_of_pos_of_nonneg hc ht)
    (isCoerciveCLM_shiftedPrecisionCLM K hK)

/-- Generic second-resolvent identity from one left and one right inverse. -/
theorem continuousLinearInverse_sub_eq_comp_sub_comp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K₀ K₁ C₀ C₁ : E →L[ℝ] E)
    (hC₁K₁ : C₁.comp K₁ = ContinuousLinearMap.id ℝ E)
    (hK₀C₀ : K₀.comp C₀ = ContinuousLinearMap.id ℝ E) :
    C₁ - C₀ = C₁.comp ((K₀ - K₁).comp C₀) := by
  apply ContinuousLinearMap.ext
  intro x
  have hright : K₀ (C₀ x) = x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun f => f x) hK₀C₀
  have hleft : C₁ (K₁ (C₀ x)) = C₀ x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun f => f (C₀ x)) hC₁K₁
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, hright, hleft]

/-- Exact shifted second-resolvent identity in the `C₁ R₂ C₀` order, where
`R₂ = K₀-K₁`. -/
theorem shiftedResolvent_sub_eq_comp_precision_sub_comp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K₀ K₁ : E →L[ℝ] E)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hK₀ : IsCoerciveCLM K₀ c₀)
    (hK₁ : IsCoerciveCLM K₁ c₁)
    (t : ℝ) (ht : 0 ≤ t) :
    shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht -
        shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht =
      (shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht).comp
        ((K₀ - K₁).comp
          (shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht)) := by
  rw [← shiftedPrecisionCLM_sub K₀ K₁ t]
  exact continuousLinearInverse_sub_eq_comp_sub_comp
    (shiftedPrecisionCLM K₀ t)
    (shiftedPrecisionCLM K₁ t)
    (shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht)
    (shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht)
    (shiftedResolvent_comp_shiftedPrecision K₁ hc₁ hK₁ t ht)
    (shiftedPrecision_comp_shiftedResolvent K₀ hc₀ hK₀ t ht)

/-- The flipped exact factorization `C₀ R₂ C₁`. -/
theorem shiftedResolvent_sub_eq_comp_precision_sub_comp_flip
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K₀ K₁ : E →L[ℝ] E)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hK₀ : IsCoerciveCLM K₀ c₀)
    (hK₁ : IsCoerciveCLM K₁ c₁)
    (t : ℝ) (ht : 0 ≤ t) :
    shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht -
        shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht =
      (shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht).comp
        ((K₀ - K₁).comp
          (shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht)) := by
  apply ContinuousLinearMap.ext
  intro x
  have hleft :
      shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht
          (shiftedPrecisionCLM K₀ t
            (shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht x)) =
        shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht x :=
    shiftedResolventOfIsCoerciveCLM_apply_precision
      K₀ hc₀ hK₀ t ht
        (shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht x)
  have hright :
      shiftedPrecisionCLM K₁ t
          (shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht x) = x :=
    shiftedPrecisionCLM_apply_shiftedResolvent
      K₁ hc₁ hK₁ t ht x
  rw [← shiftedPrecisionCLM_sub K₀ K₁ t]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, hleft, hright]

/-- Two-margin norm estimate for the shifted resolvent difference. -/
theorem norm_shiftedResolvent_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K₀ K₁ : E →L[ℝ] E)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hK₀ : IsCoerciveCLM K₀ c₀)
    (hK₁ : IsCoerciveCLM K₁ c₁)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht -
        shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht‖ ≤
      (c₁ + t)⁻¹ * ‖K₀ - K₁‖ * (c₀ + t)⁻¹ := by
  rw [shiftedResolvent_sub_eq_comp_precision_sub_comp
    K₀ K₁ hc₀ hc₁ hK₀ hK₁ t ht]
  calc
    ‖(shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht).comp
        ((K₀ - K₁).comp
          (shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht))‖
        ≤
          ‖shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht‖ *
            ‖(K₀ - K₁).comp
              (shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤
        ‖shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht‖ *
          (‖K₀ - K₁‖ *
            ‖shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (c₁ + t)⁻¹ * (‖K₀ - K₁‖ * (c₀ + t)⁻¹) := by
      gcongr
      · exact norm_shiftedResolventOfIsCoerciveCLM_le
          K₁ hc₁ hK₁ t ht
      · exact norm_shiftedResolventOfIsCoerciveCLM_le
          K₀ hc₀ hK₀ t ht
    _ = (c₁ + t)⁻¹ * ‖K₀ - K₁‖ * (c₀ + t)⁻¹ := by ring

end

end YangMills.RG

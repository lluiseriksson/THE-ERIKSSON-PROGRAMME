/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.QuantitativeFixedPointThirdDerivativeStability

/-!
# Second jet of the derived fixed-point map

The map used to generate the third derivative of a fixed point is

`(x,A) ↦ DT(x,g(x)) ∘ (id,A)`.

This file isolates its two factors and proves the exact quantitative
bilinear estimate.  The graph factor `(id,A)` is affine: its second
derivative vanishes and its first derivative has norm at most one.
Consequently the second jet of the derived map is controlled only by the
first and second jets of the coefficient `DT(x,g(x))`.

No derivative of `g` of order three is assumed or appears.
-/

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The coefficient of the derived fixed-point map. -/
noncomputable def fixedPointDerivativeCoefficient
    (T : E × F → F) (g : E → F) :
    E × (E →L[ℝ] F) → (E × F →L[ℝ] F) :=
  fun p => fderiv ℝ T (p.1, g p.1)

/-- The affine graph factor of the derived fixed-point map. -/
noncomputable def fixedPointGraphFactor :
    E × (E →L[ℝ] F) → (E →L[ℝ] E × F) :=
  fun p => fixedPointGraphDerivative p.2

/-- The linear part of the affine graph factor. -/
noncomputable def fixedPointGraphFactorLinear :
    E × (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E × F) :=
  (ContinuousLinearMap.compL ℝ E F (E × F)
      (ContinuousLinearMap.inr ℝ E F)).comp
    (ContinuousLinearMap.snd ℝ E (E →L[ℝ] F))

@[simp] theorem fixedPointGraphFactorLinear_apply
    (p : E × (E →L[ℝ] F)) :
    fixedPointGraphFactorLinear p =
      (ContinuousLinearMap.inr ℝ E F).comp p.2 := rfl

/-- Affine decomposition of the graph factor. -/
theorem fixedPointGraphFactor_eq_const_add_linear
    (p : E × (E →L[ℝ] F)) :
    fixedPointGraphFactor p =
      ContinuousLinearMap.inl ℝ E F +
        fixedPointGraphFactorLinear p := by
  apply ContinuousLinearMap.ext
  intro v
  simp [fixedPointGraphFactor, fixedPointGraphDerivative]

/-- The graph-factor linear part has operator norm at most one. -/
theorem norm_fixedPointGraphFactorLinear_le :
    ‖(fixedPointGraphFactorLinear :
      E × (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E × F))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  calc
    ‖fixedPointGraphFactorLinear p‖
        = ‖(ContinuousLinearMap.inr ℝ E F).comp p.2‖ := by
          rw [fixedPointGraphFactorLinear_apply]
    _ ≤ ‖ContinuousLinearMap.inr ℝ E F‖ * ‖p.2‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖p.2‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      simp
    _ ≤ 1 * ‖p‖ := by
      gcongr
      exact le_max_right ‖p.1‖ ‖p.2‖

/-- Smoothness of the affine graph factor. -/
theorem contDiff_fixedPointGraphFactor :
    ContDiff ℝ ⊤ (fixedPointGraphFactor :
      E × (E →L[ℝ] F) → (E →L[ℝ] E × F)) := by
  have heq :
      (fixedPointGraphFactor :
        E × (E →L[ℝ] F) → (E →L[ℝ] E × F)) =
        fun p =>
          ContinuousLinearMap.inl ℝ E F +
            fixedPointGraphFactorLinear p := by
    funext p
    exact fixedPointGraphFactor_eq_const_add_linear p
  rw [heq]
  fun_prop

/-- Exact derivative of the affine graph factor. -/
theorem fixedPointGraphFactor_hasFDerivAt
    (p : E × (E →L[ℝ] F)) :
    HasFDerivAt
      (fixedPointGraphFactor :
        E × (E →L[ℝ] F) → (E →L[ℝ] E × F))
      fixedPointGraphFactorLinear p := by
  have heq :
      (fixedPointGraphFactor :
        E × (E →L[ℝ] F) → (E →L[ℝ] E × F)) =
        fun q : E × (E →L[ℝ] F) =>
          ContinuousLinearMap.inl ℝ E F +
            fixedPointGraphFactorLinear q := by
    funext q
    exact fixedPointGraphFactor_eq_const_add_linear q
  rw [heq]
  simpa only [Pi.add_apply, zero_add] using
    (hasFDerivAt_const
      (x := p) (c := ContinuousLinearMap.inl ℝ E F)).add
        fixedPointGraphFactorLinear.hasFDerivAt

/-- The first jet of the affine graph factor has norm at most one. -/
theorem norm_iteratedFDeriv_one_fixedPointGraphFactor_le
    (p : E × (E →L[ℝ] F)) :
    ‖iteratedFDeriv ℝ 1
      (fixedPointGraphFactor :
        E × (E →L[ℝ] F) → (E →L[ℝ] E × F)) p‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_one,
    (fixedPointGraphFactor_hasFDerivAt p).fderiv]
  exact norm_fixedPointGraphFactorLinear_le

/-- The second jet of the affine graph factor vanishes. -/
theorem norm_iteratedFDeriv_two_fixedPointGraphFactor
    (p : E × (E →L[ℝ] F)) :
    ‖iteratedFDeriv ℝ 2
      (fixedPointGraphFactor :
        E × (E →L[ℝ] F) → (E →L[ℝ] E × F)) p‖ = 0 := by
  have hfderiv :
      fderiv ℝ
          (fixedPointGraphFactor :
            E × (E →L[ℝ] F) → (E →L[ℝ] E × F)) =
        fun _ : E × (E →L[ℝ] F) =>
          (fixedPointGraphFactorLinear (E := E) (F := F) :
            E × (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E × F)) := by
    funext q
    exact (fixedPointGraphFactor_hasFDerivAt q).fderiv
  calc
    ‖iteratedFDeriv ℝ 2
        (fixedPointGraphFactor :
          E × (E →L[ℝ] F) → (E →L[ℝ] E × F)) p‖ =
        ‖iteratedFDeriv ℝ 1
          (fderiv ℝ (fixedPointGraphFactor :
            E × (E →L[ℝ] F) → (E →L[ℝ] E × F))) p‖ := by
          simpa using
            (norm_iteratedFDeriv_fderiv
              (𝕜 := ℝ) (f := (fixedPointGraphFactor :
                E × (E →L[ℝ] F) → (E →L[ℝ] E × F)))
              (x := p) (n := 1)).symm
    _ = ‖iteratedFDeriv ℝ 1
          (fun _ : E × (E →L[ℝ] F) =>
            (fixedPointGraphFactorLinear (E := E) (F := F) :
              E × (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E × F))) p‖ := by
          rw [hfderiv]
    _ = 0 := by simp

/-- The derived fixed-point map is the bilinear composition of its
coefficient and affine graph factor. -/
theorem fixedPointFirstDerivativeMap_eq_bilinear
    (T : E × F → F) (g : E → F)
    (p : E × (E →L[ℝ] F)) :
    fixedPointFirstDerivativeMap T g p =
      ContinuousLinearMap.compL ℝ E (E × F) F
        (fixedPointDerivativeCoefficient T g p)
        (fixedPointGraphFactor p) := rfl

/-- **Derived-map second-jet bound.**  On `‖A‖ ≤ L₁`, the second
derivative is bounded by

`2 C₁ + C₂ max(1,L₁)`,

where `C₁,C₂` bound the first and second jets of the literal coefficient
`DT(x,g(x))`.  The coefficient value itself drops out because the graph
factor has zero second derivative. -/
theorem norm_iteratedFDeriv_two_fixedPointFirstDerivativeMap_le
    (T : E × F → F) (g : E → F)
    (p : E × (E →L[ℝ] F))
    {L₁ C₁ C₂ : ℝ}
    (hA : ‖p.2‖ ≤ L₁)
    (hcoeff :
      ContDiff ℝ 2 (fixedPointDerivativeCoefficient T g))
    (hC₁ : ‖iteratedFDeriv ℝ 1
      (fixedPointDerivativeCoefficient T g) p‖ ≤ C₁)
    (hC₂ : ‖iteratedFDeriv ℝ 2
      (fixedPointDerivativeCoefficient T g) p‖ ≤ C₂) :
    ‖iteratedFDeriv ℝ 2
      (fixedPointFirstDerivativeMap T g) p‖ ≤
        2 * C₁ + C₂ * max 1 L₁ := by
  have hmap :
      fixedPointFirstDerivativeMap T g =
        fun y =>
          ContinuousLinearMap.compL ℝ E (E × F) F
            (fixedPointDerivativeCoefficient T g y)
            (fixedPointGraphFactor y) := by
    funext y
    exact fixedPointFirstDerivativeMap_eq_bilinear T g y
  rw [hmap]
  have hraw :=
    ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one
      (ContinuousLinearMap.compL ℝ E (E × F) F)
      (f := fixedPointDerivativeCoefficient T g)
      (g := (fixedPointGraphFactor :
        E × (E →L[ℝ] F) → (E →L[ℝ] E × F)))
      (N := (2 : WithTop ℕ∞)) (n := 2)
      hcoeff
      ((contDiff_fixedPointGraphFactor (E := E) (F := F)).of_le
        (by norm_num))
      p le_rfl
      (ContinuousLinearMap.norm_compL_le ℝ E (E × F) F)
  have hgraph0 :
      ‖iteratedFDeriv ℝ 0
        (fixedPointGraphFactor :
          E × (E →L[ℝ] F) → (E →L[ℝ] E × F)) p‖ ≤
        max 1 L₁ := by
    simpa only [norm_iteratedFDeriv_zero] using
      (norm_fixedPointGraphDerivative_le p.2).trans
        (max_le_max le_rfl hA)
  have hgraph1 :=
    norm_iteratedFDeriv_one_fixedPointGraphFactor_le p
  have hgraph2 :
      ‖iteratedFDeriv ℝ 2
        (fixedPointGraphFactor :
          E × (E →L[ℝ] F) → (E →L[ℝ] E × F)) p‖ = 0 := by
    exact norm_iteratedFDeriv_two_fixedPointGraphFactor p
  have hC₁0 : 0 ≤ C₁ :=
    (norm_nonneg
      (iteratedFDeriv ℝ 1
        (fixedPointDerivativeCoefficient T g) p)).trans hC₁
  have hC₂0 : 0 ≤ C₂ :=
    (norm_nonneg
      (iteratedFDeriv ℝ 2
        (fixedPointDerivativeCoefficient T g) p)).trans hC₂
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
    Nat.choose_one_right, Nat.cast_ofNat, Nat.choose_self] at hraw
  calc
    ‖iteratedFDeriv ℝ 2
        (fun y =>
          ContinuousLinearMap.compL ℝ E (E × F) F
            (fixedPointDerivativeCoefficient T g y)
            (fixedPointGraphFactor y)) p‖
        ≤ 2 * ‖iteratedFDeriv ℝ 1
              (fixedPointDerivativeCoefficient T g) p‖ *
              ‖iteratedFDeriv ℝ 1 fixedPointGraphFactor p‖ +
            ‖iteratedFDeriv ℝ 2
              (fixedPointDerivativeCoefficient T g) p‖ *
              ‖iteratedFDeriv ℝ 0 fixedPointGraphFactor p‖ := by
          simpa [hgraph2] using hraw
    _ ≤ 2 * C₁ * 1 + C₂ * max 1 L₁ := by
      gcongr
    _ = 2 * C₁ + C₂ * max 1 L₁ := by ring

end

end YangMills.RG

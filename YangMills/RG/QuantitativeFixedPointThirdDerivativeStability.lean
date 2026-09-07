/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.QuantitativeFixedPointDerivativeStability
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative third derivative of a fixed point

For a smooth fixed-point equation

`g x = T (x, g x)`,

the first derivative is itself a fixed point:

`Dg x = DT (x, g x) ∘ (id, Dg x)`.

This file packages that *literal* derived fixed-point map and applies the
existing quantitative second-derivative theorem to it.  Thus a Lipschitz
bound for the derivative of the derived map produces a bound for `D³g`;
no estimate for `D³g` is assumed.

The remaining source-facing obligation is deliberately visible: one must
bound the derivative variation and the vertical derivative of the derived
map from the second and third jets of the original physical map `T`.
-/

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fixed-point map satisfied by the derivative of `g`, obtained by
differentiating `g x = T (x, g x)` once. -/
noncomputable def fixedPointFirstDerivativeMap
    (T : E × F → F) (g : E → F) :
    E × (E →L[ℝ] F) → (E →L[ℝ] F) :=
  fun p =>
    (fderiv ℝ T (p.1, g p.1)).comp
      (fixedPointGraphDerivative p.2)

/-- The actual derivative of a differentiable fixed point satisfies the
derived fixed-point equation. -/
theorem fderiv_fixedPoint_eq_firstDerivativeMap
    (T : E × F → F) (g : E → F)
    (hfix : g = fun y => T (y, g y))
    (hg : Differentiable ℝ g)
    (hT : ∀ y, DifferentiableAt ℝ T (y, g y)) :
    fderiv ℝ g =
      fun y =>
        fixedPointFirstDerivativeMap T g
          (y, fderiv ℝ g y) := by
  funext y
  have hgraph :
      HasFDerivAt (fun z => (z, g z))
        (fixedPointGraphDerivative (fderiv ℝ g y)) y := by
    simpa [fixedPointGraphDerivative] using
      (hasFDerivAt_id (𝕜 := ℝ) y).prodMk
        (hg.differentiableAt.hasFDerivAt)
  have hcomp :
      fderiv ℝ (fun z => T (z, g z)) y =
        (fderiv ℝ T (y, g y)).comp
          (fixedPointGraphDerivative (fderiv ℝ g y)) :=
    ((hT y).hasFDerivAt.comp y hgraph).fderiv
  exact
    (congrArg (fun f : E → F => fderiv ℝ f y) hfix).trans
      (by
        simpa [fixedPointFirstDerivativeMap] using hcomp)

/-- The vertical derivative of the derived fixed-point map is controlled
by the same vertical derivative of the original map.  This removes a
seemingly new contraction hypothesis from the third-jet recurrence. -/
theorem norm_fderiv_fixedPointFirstDerivativeMap_vertical_le
    (T : E × F → F) (g : E → F)
    (x : E) (A : E →L[ℝ] F) {q : ℝ}
    (hq0 : 0 ≤ q)
    (hderived :
      DifferentiableAt ℝ
        (fixedPointFirstDerivativeMap T g) (x, A))
    (hvertical :
      ‖(fderiv ℝ T (x, g x)).comp
        (ContinuousLinearMap.inr ℝ E F)‖ ≤ q) :
    ‖(fderiv ℝ (fixedPointFirstDerivativeMap T g) (x, A)).comp
        (ContinuousLinearMap.inr ℝ E (E →L[ℝ] F))‖ ≤ q := by
  let V :=
    (fderiv ℝ T (x, g x)).comp
      (ContinuousLinearMap.inr ℝ E F)
  let slice : (E →L[ℝ] F) → (E →L[ℝ] F) :=
    fun B => fixedPointFirstDerivativeMap T g (x, B)
  have hsliceLip : LipschitzWith ⟨q, hq0⟩ slice := by
    apply LipschitzWith.of_dist_le_mul
    intro B C
    rw [dist_eq_norm, dist_eq_norm]
    have heq :
        slice B - slice C = V.comp (B - C) := by
      apply ContinuousLinearMap.ext
      intro v
      simp [slice, V, fixedPointFirstDerivativeMap,
        fixedPointGraphDerivative]
      rw [show (v, B v) = (v, 0) + (0, B v) by ext <;> simp,
        show (v, C v) = (v, 0) + (0, C v) by ext <;> simp,
        map_add, map_add]
      abel
    rw [heq]
    exact
      (V.opNorm_comp_le (B - C)).trans
        (mul_le_mul_of_nonneg_right hvertical (norm_nonneg _))
  have hsliceDeriv :
      fderiv ℝ slice A =
        (fderiv ℝ (fixedPointFirstDerivativeMap T g) (x, A)).comp
          (ContinuousLinearMap.inr ℝ E (E →L[ℝ] F)) := by
    have hinr :
        HasFDerivAt (fun B : E →L[ℝ] F => (x, B))
          (ContinuousLinearMap.inr ℝ E (E →L[ℝ] F)) A := by
      simpa using
        (hasFDerivAt_const (x := A) (c := x)).prodMk
          (hasFDerivAt_id (𝕜 := ℝ) A)
    simpa [slice] using
      (hderived.hasFDerivAt.comp A hinr).fderiv
  rw [← hsliceDeriv]
  simpa only [NNReal.coe_mk] using
    (norm_fderiv_le_of_lipschitz ℝ hsliceLip (x₀ := A))

/-- A uniform second-jet bound makes the first derivative Lipschitz on a
convex source domain.  This is the bridge from the already generated
second jet to the third-jet fixed-point recurrence. -/
theorem lipschitzOnWith_fderiv_of_iteratedFDeriv_two_le
    (g : E → F) (s : Set E) {L₂ : ℝ}
    (hL₂0 : 0 ≤ L₂)
    (hg : ContDiff ℝ 2 g)
    (hsecond : ∀ y ∈ s,
      ‖iteratedFDeriv ℝ 2 g y‖ ≤ L₂)
    (hs : Convex ℝ s) :
    LipschitzOnWith ⟨L₂, hL₂0⟩ (fderiv ℝ g) s := by
  have hDg : ContDiff ℝ 1 (fderiv ℝ g) :=
    hg.fderiv_right (by norm_num)
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  rw [dist_eq_norm, dist_eq_norm]
  apply hs.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ)
      (f := fderiv ℝ g)
      (fun w _ => hDg.differentiable (by decide) w)
      (fun w hw => ?_) hz hy
  have hnorm :
      ‖fderiv ℝ (fderiv ℝ g) w‖ =
        ‖iteratedFDeriv ℝ 2 g w‖ := by
    simpa only [norm_iteratedFDeriv_one] using
      (norm_iteratedFDeriv_fderiv
        (𝕜 := ℝ) (f := g) (x := w) (n := 1))
  rw [hnorm]
  exact hsecond w hw

/-- **Third-jet absorption theorem.**  Apply the quantitative second-jet
fixed-point theorem to the literal derived map for `Dg`.  The hypotheses
`hjoint` and `hvertical` concern derivatives of that derived map, not a
third derivative of `g`; they are the precise quantities to be generated
from the physical second and third source jets of `T`. -/
theorem norm_iteratedFDeriv_three_fixedPoint_le
    (T : E × F → F) (g : E → F)
    (s : Set E) (hs : IsOpen s) (x : E) (hx : x ∈ s)
    {L₂ B₂ q₂ : ℝ}
    (hL₂0 : 0 ≤ L₂) (hB₂0 : 0 ≤ B₂) (hq₂1 : q₂ < 1)
    (hfix : g = fun y => T (y, g y))
    (hg : ContDiff ℝ 3 g)
    (hT : ∀ y, DifferentiableAt ℝ T (y, g y))
    (hderived : ∀ y ∈ s,
      DifferentiableAt ℝ
        (fixedPointFirstDerivativeMap T g)
        (y, fderiv ℝ g y))
    (hsecond : ∀ y ∈ s,
      ‖iteratedFDeriv ℝ 2 g y‖ ≤ L₂)
    (hconv : Convex ℝ s)
    (hjoint : ∀ y ∈ s, ∀ z ∈ s,
      ‖fderiv ℝ (fixedPointFirstDerivativeMap T g)
          (y, fderiv ℝ g y) -
        fderiv ℝ (fixedPointFirstDerivativeMap T g)
          (z, fderiv ℝ g z)‖ ≤
        B₂ * dist (y, fderiv ℝ g y) (z, fderiv ℝ g z))
    (hvertical : ∀ y ∈ s,
      ‖(fderiv ℝ T (y, g y)).comp
        (ContinuousLinearMap.inr ℝ E F)‖ ≤ q₂) :
    ‖iteratedFDeriv ℝ 3 g x‖ ≤
      B₂ * (max 1 L₂) ^ 2 / (1 - q₂) := by
  have hgDiff : Differentiable ℝ g :=
    hg.differentiable (by decide)
  have hDgfix :
      fderiv ℝ g =
        fun y =>
          fixedPointFirstDerivativeMap T g
            (y, fderiv ℝ g y) :=
    fderiv_fixedPoint_eq_firstDerivativeMap T g hfix hgDiff hT
  have hDg : ContDiff ℝ 2 (fderiv ℝ g) := by
    exact hg.fderiv_right (by norm_num)
  have hDglip :
      LipschitzOnWith ⟨L₂, hL₂0⟩ (fderiv ℝ g) s :=
    lipschitzOnWith_fderiv_of_iteratedFDeriv_two_le
      g s hL₂0 (hg.of_le (by norm_num)) hsecond hconv
  have hq₂0 : 0 ≤ q₂ := by
    have hy := hvertical x hx
    exact (norm_nonneg _).trans hy
  have hderivedVertical : ∀ y ∈ s,
      ‖(fderiv ℝ (fixedPointFirstDerivativeMap T g)
          (y, fderiv ℝ g y)).comp
        (ContinuousLinearMap.inr ℝ E (E →L[ℝ] F))‖ ≤ q₂ := by
    intro y hy
    exact norm_fderiv_fixedPointFirstDerivativeMap_vertical_le
      T g y (fderiv ℝ g y) hq₂0 (hderived y hy)
      (hvertical y hy)
  have hmain :=
    norm_iteratedFDeriv_two_fixedPoint_le
      (fixedPointFirstDerivativeMap T g) (fderiv ℝ g)
      s hs x hx hL₂0 hB₂0 hq₂1 hDgfix hDg
      hderived hDglip hjoint hderivedVertical
  calc
    ‖iteratedFDeriv ℝ 3 g x‖ =
        ‖iteratedFDeriv ℝ 2 (fderiv ℝ g) x‖ := by
      simpa using
        (norm_iteratedFDeriv_fderiv
          (𝕜 := ℝ) (f := g) (x := x) (n := 2)).symm
    _ ≤ B₂ * (max 1 L₂) ^ 2 / (1 - q₂) := hmain

/-- A consumer form in which the derivative-variation premise is generated
from a uniform second derivative of the *literal derived map*.  Since that
map contains only `DT`, `g`, and `Dg`, its second derivative is generated by
jets of `T` through order three and jets of `g` through order two; it does
not contain `D³g`. -/
theorem norm_iteratedFDeriv_three_fixedPoint_le_of_derivedSecond
    (T : E × F → F) (g : E → F) (x : E)
    {L₂ B₂ q₂ : ℝ}
    (hL₂0 : 0 ≤ L₂) (hB₂0 : 0 ≤ B₂) (hq₂1 : q₂ < 1)
    (hfix : g = fun y => T (y, g y))
    (hg : ContDiff ℝ 3 g)
    (hT : ∀ y, DifferentiableAt ℝ T (y, g y))
    (hderived :
      ContDiff ℝ 2 (fixedPointFirstDerivativeMap T g))
    (hsecond : ∀ y,
      ‖iteratedFDeriv ℝ 2 g y‖ ≤ L₂)
    (hderivedSecond : ∀ p,
      ‖iteratedFDeriv ℝ 2
        (fixedPointFirstDerivativeMap T g) p‖ ≤ B₂)
    (hvertical : ∀ y,
      ‖(fderiv ℝ T (y, g y)).comp
        (ContinuousLinearMap.inr ℝ E F)‖ ≤ q₂) :
    ‖iteratedFDeriv ℝ 3 g x‖ ≤
      B₂ * (max 1 L₂) ^ 2 / (1 - q₂) := by
  have hderivedLip :
      LipschitzOnWith ⟨B₂, hB₂0⟩
        (fderiv ℝ (fixedPointFirstDerivativeMap T g))
        (Set.univ : Set (E × (E →L[ℝ] F))) :=
    lipschitzOnWith_fderiv_of_iteratedFDeriv_two_le
      (fixedPointFirstDerivativeMap T g) Set.univ hB₂0
      hderived (fun p _ => hderivedSecond p) convex_univ
  apply norm_iteratedFDeriv_three_fixedPoint_le
      T g Set.univ isOpen_univ x (Set.mem_univ x)
      hL₂0 hB₂0 hq₂1 hfix hg hT
  · intro y _
    exact hderived.differentiable (by decide)
      (y, fderiv ℝ g y)
  · intro y _
    exact hsecond y
  · exact convex_univ
  · intro y _ z _
    simpa only [NNReal.coe_mk, dist_eq_norm] using
      hderivedLip.dist_le_mul
        (y, fderiv ℝ g y) (Set.mem_univ _)
        (z, fderiv ℝ g z) (Set.mem_univ _)
  · intro y _
    exact hvertical y

/-- The bounded tube around the derivative graph on which the literal
derived-map second jet has to be controlled. -/
def fixedPointDerivativeTube
    (s : Set E) (L₁ : ℝ) :
    Set (E × (E →L[ℝ] F)) :=
  s ×ˢ Metric.closedBall 0 L₁

/-- The source-useful third-jet theorem.  Unlike the global convenience
corollary above, it asks for the second-jet bound of the derived map only
on the convex tube `x ∈ s`, `‖A‖ ≤ L₁`.  The actual graph belongs to this
tube by the supplied first-jet estimate.  Hence no impossible uniform
control for arbitrary linear maps `A` is introduced. -/
theorem norm_iteratedFDeriv_three_fixedPoint_le_of_derivedSecond_on_tube
    (T : E × F → F) (g : E → F)
    (s : Set E) (hsOpen : IsOpen s) (hsConvex : Convex ℝ s)
    (x : E) (hx : x ∈ s)
    {L₁ L₂ B₂ q₂ : ℝ}
    (hL₂0 : 0 ≤ L₂)
    (hB₂0 : 0 ≤ B₂) (hq₂1 : q₂ < 1)
    (hfix : g = fun y => T (y, g y))
    (hg : ContDiff ℝ 3 g)
    (hT : ∀ y, DifferentiableAt ℝ T (y, g y))
    (hderived :
      ContDiff ℝ 2 (fixedPointFirstDerivativeMap T g))
    (hfirst : ∀ y ∈ s, ‖fderiv ℝ g y‖ ≤ L₁)
    (hsecond : ∀ y ∈ s,
      ‖iteratedFDeriv ℝ 2 g y‖ ≤ L₂)
    (hderivedSecond :
      ∀ p ∈ fixedPointDerivativeTube (E := E) (F := F) s L₁,
        ‖iteratedFDeriv ℝ 2
          (fixedPointFirstDerivativeMap T g) p‖ ≤ B₂)
    (hvertical : ∀ y ∈ s,
      ‖(fderiv ℝ T (y, g y)).comp
        (ContinuousLinearMap.inr ℝ E F)‖ ≤ q₂) :
    ‖iteratedFDeriv ℝ 3 g x‖ ≤
      B₂ * (max 1 L₂) ^ 2 / (1 - q₂) := by
  let tube :=
    fixedPointDerivativeTube (E := E) (F := F) s L₁
  have htubeConvex : Convex ℝ tube := by
    exact hsConvex.prod (convex_closedBall 0 L₁)
  have hgraphMem : ∀ y ∈ s,
      (y, fderiv ℝ g y) ∈ tube := by
    intro y hy
    refine ⟨hy, ?_⟩
    simpa [tube, fixedPointDerivativeTube, Metric.mem_closedBall,
      dist_eq_norm] using hfirst y hy
  have hderivedLip :
      LipschitzOnWith ⟨B₂, hB₂0⟩
        (fderiv ℝ (fixedPointFirstDerivativeMap T g)) tube :=
    lipschitzOnWith_fderiv_of_iteratedFDeriv_two_le
      (fixedPointFirstDerivativeMap T g) tube hB₂0
      hderived (by
        intro p hp
        exact hderivedSecond p hp) htubeConvex
  apply norm_iteratedFDeriv_three_fixedPoint_le
      T g s hsOpen x hx hL₂0 hB₂0 hq₂1 hfix hg hT
  · intro y _
    exact hderived.differentiable (by decide)
      (y, fderiv ℝ g y)
  · exact hsecond
  · exact hsConvex
  · intro y hy z hz
    simpa only [NNReal.coe_mk, dist_eq_norm] using
      hderivedLip.dist_le_mul
        (y, fderiv ℝ g y) (hgraphMem y hy)
        (z, fderiv ℝ g z) (hgraphMem z hz)
  · exact hvertical

end

end YangMills.RG

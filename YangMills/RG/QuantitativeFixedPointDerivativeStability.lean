/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Quantitative stability of the derivative of a fixed point

For a differentiable fixed-point equation

`g x = T (x, g x)`,

the derivative satisfies

`Dg = DT ∘ (id, Dg)`.

This file isolates the quantitative absorption step behind the second jet
of the selected CMP102 correction.  A strict bound on the vertical
derivative of `T` absorbs the occurrence of `Dg x - Dg y`; a Lipschitz
bound for the full derivative of `T` then makes `Dg` Lipschitz.

The result is rectangular: `g : E → F`.  No second derivative of `g` is
assumed.
-/

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of the graph map `x ↦ (x, g x)`. -/
noncomputable def fixedPointGraphDerivative
    (A : E →L[ℝ] F) : E →L[ℝ] E × F :=
  (1 : E →L[ℝ] E).prod A

@[simp] theorem fixedPointGraphDerivative_apply
    (A : E →L[ℝ] F) (x : E) :
    fixedPointGraphDerivative A x = (x, A x) := rfl

/-- The graph derivative has the expected max-product norm bound. -/
theorem norm_fixedPointGraphDerivative_le
    (A : E →L[ℝ] F) :
    ‖fixedPointGraphDerivative A‖ ≤ max 1 ‖A‖ := by
  rw [fixedPointGraphDerivative, ContinuousLinearMap.opNorm_prod]
  exact max_le_max ContinuousLinearMap.norm_id_le le_rfl

/-- Algebraic absorption lemma for the derivative equations at two fixed
points.  The quantity `jointDifference` bounds the change of the complete
joint derivative, while `q` bounds its vertical part. -/
theorem norm_sub_le_of_fixedPointDerivativeEquations
    (A B : E →L[ℝ] F)
    (TX TY : E × F →L[ℝ] F)
    {L jointDifference q : ℝ}
    (hL : ‖A‖ ≤ L)
    (hjoint : ‖TX - TY‖ ≤ jointDifference)
    (hvertical :
      ‖TY.comp (ContinuousLinearMap.inr ℝ E F)‖ ≤ q)
    (hq1 : q < 1)
    (hA : A = TX.comp (fixedPointGraphDerivative A))
    (hB : B = TY.comp (fixedPointGraphDerivative B)) :
    ‖A - B‖ ≤
      jointDifference * max 1 L / (1 - q) := by
  have hL0 : 0 ≤ L := (norm_nonneg A).trans hL
  have hjoint0 : 0 ≤ jointDifference :=
    (norm_nonneg (TX - TY)).trans hjoint
  have hgraph :
      ‖fixedPointGraphDerivative A‖ ≤ max 1 L :=
    (norm_fixedPointGraphDerivative_le A).trans
      (max_le_max le_rfl hL)
  have hdecomp :
      A - B =
        (TX - TY).comp (fixedPointGraphDerivative A) +
          (TY.comp (ContinuousLinearMap.inr ℝ E F)).comp (A - B) := by
    calc
      A - B =
          TX.comp (fixedPointGraphDerivative A) -
            TY.comp (fixedPointGraphDerivative B) :=
        congrArg₂ (· - ·) hA hB
      _ = (TX - TY).comp (fixedPointGraphDerivative A) +
            (TY.comp (ContinuousLinearMap.inr ℝ E F)).comp (A - B) := by
        apply ContinuousLinearMap.ext
        intro x
        simp only [ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
          fixedPointGraphDerivative_apply, ContinuousLinearMap.inr_apply]
        have hpair :
            ((0, A x - B x) : E × F) =
              (x, A x) - (x, B x) := by
          ext <;> simp
        rw [hpair, map_sub]
        abel
  have hraw :
      ‖A - B‖ ≤
        jointDifference * max 1 L + q * ‖A - B‖ := by
    calc
      ‖A - B‖ =
          ‖(TX - TY).comp (fixedPointGraphDerivative A) +
            (TY.comp (ContinuousLinearMap.inr ℝ E F)).comp (A - B)‖ :=
        congrArg norm hdecomp
      _ ≤ ‖(TX - TY).comp (fixedPointGraphDerivative A)‖ +
              ‖(TY.comp (ContinuousLinearMap.inr ℝ E F)).comp (A - B)‖ :=
        norm_add_le _ _
      _ ≤ ‖TX - TY‖ * ‖fixedPointGraphDerivative A‖ +
            ‖TY.comp (ContinuousLinearMap.inr ℝ E F)‖ * ‖A - B‖ := by
        gcongr
        · exact ContinuousLinearMap.opNorm_comp_le _ _
        · exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ jointDifference * max 1 L + q * ‖A - B‖ := by
        gcongr
  have honeq : 0 < 1 - q := sub_pos.mpr hq1
  apply (le_div_iff₀ honeq).mpr
  nlinarith [norm_nonneg (A - B),
    mul_nonneg (show 0 ≤ max 1 L by positivity)
      hjoint0]

/-- A joint derivative-Lipschitz estimate and a strict vertical contraction
make the derivative of a smooth fixed point Lipschitz.  Consequently the
second derivative of the fixed point is bounded, without assuming any
second derivative estimate for the fixed point itself. -/
theorem norm_iteratedFDeriv_two_fixedPoint_le
    (T : E × F → F) (g : E → F)
    (s : Set E) (hs : IsOpen s) (x : E) (hx : x ∈ s)
    {L B q : ℝ}
    (hL0 : 0 ≤ L) (hB0 : 0 ≤ B) (hq1 : q < 1)
    (hfix : g = fun y => T (y, g y))
    (hg : ContDiff ℝ 2 g) (hT : ContDiff ℝ 2 T)
    (hglip : LipschitzOnWith ⟨L, hL0⟩ g s)
    (hjoint : ∀ y ∈ s, ∀ z ∈ s,
      ‖fderiv ℝ T (y, g y) - fderiv ℝ T (z, g z)‖ ≤
        B * dist (y, g y) (z, g z))
    (hvertical : ∀ y ∈ s,
      ‖(fderiv ℝ T (y, g y)).comp
          (ContinuousLinearMap.inr ℝ E F)‖ ≤ q) :
    ‖iteratedFDeriv ℝ 2 g x‖ ≤
      B * (max 1 L) ^ 2 / (1 - q) := by
  have hden : 0 ≤ 1 - q := (sub_pos.mpr hq1).le
  let C : NNReal :=
    ⟨B * (max 1 L) ^ 2 / (1 - q), by
      exact div_nonneg
        (mul_nonneg hB0 (sq_nonneg (max 1 L))) hden⟩
  have hdiff : ContDiff ℝ 1 (fderiv ℝ g) :=
    hg.fderiv_right (by norm_num)
  have hderivEq : ∀ y,
      fderiv ℝ g y =
        (fderiv ℝ T (y, g y)).comp
          (fixedPointGraphDerivative (fderiv ℝ g y)) := by
    intro y
    have hgAt : DifferentiableAt ℝ g y :=
      (hg.differentiable (by decide)).differentiableAt
    have hTAt : DifferentiableAt ℝ T (y, g y) :=
      (hT.differentiable (by decide)).differentiableAt
    have hgraph :
        HasFDerivAt (fun z => (z, g z))
          (fixedPointGraphDerivative (fderiv ℝ g y)) y := by
      simpa [fixedPointGraphDerivative] using
        (hasFDerivAt_id (𝕜 := ℝ) y).prodMk hgAt.hasFDerivAt
    have hcomp :
        fderiv ℝ (fun z => T (z, g z)) y =
          (fderiv ℝ T (y, g y)).comp
            (fixedPointGraphDerivative (fderiv ℝ g y)) :=
      (hTAt.hasFDerivAt.comp y hgraph).fderiv
    exact
      (congrArg (fun f : E → F => fderiv ℝ f y) hfix).trans hcomp
  have hgraphDist : ∀ y ∈ s, ∀ z ∈ s,
      dist (y, g y) (z, g z) ≤ max 1 L * dist y z := by
    intro y hy z hz
    rw [Prod.dist_eq]
    apply max_le
    · calc
        dist y z = 1 * dist y z := (one_mul _).symm
        _ ≤ max 1 L * dist y z :=
          mul_le_mul_of_nonneg_right
            (le_max_left (1 : ℝ) L) dist_nonneg
    · exact
        (hglip.dist_le_mul y hy z hz).trans
          (mul_le_mul_of_nonneg_right
            (le_max_right (1 : ℝ) L) (dist_nonneg))
  have hlipDeriv : LipschitzOnWith C (fderiv ℝ g) s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    have hDy :
        ‖fderiv ℝ g y‖ ≤ L := by
      simpa using
        (norm_fderiv_le_of_lipschitzOn ℝ (hs.mem_nhds hy) hglip)
    have hjoint' :
        ‖fderiv ℝ T (y, g y) - fderiv ℝ T (z, g z)‖ ≤
          (B * max 1 L) * dist y z := by
      calc
        ‖fderiv ℝ T (y, g y) - fderiv ℝ T (z, g z)‖
            ≤ B * dist (y, g y) (z, g z) :=
          hjoint y hy z hz
        _ ≤ B * (max 1 L * dist y z) := by
          exact mul_le_mul_of_nonneg_left
            (hgraphDist y hy z hz) hB0
        _ = (B * max 1 L) * dist y z := by ring
    have habsorb :=
      norm_sub_le_of_fixedPointDerivativeEquations
        (fderiv ℝ g y) (fderiv ℝ g z)
        (fderiv ℝ T (y, g y)) (fderiv ℝ T (z, g z))
        hDy hjoint' (hvertical z hz) hq1
        (hderivEq y) (hderivEq z)
    rw [dist_eq_norm]
    have hqne : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
    have hrearrange :
        ((B * max 1 L) * dist y z) * max 1 L / (1 - q) =
          (B * (max 1 L) ^ 2 / (1 - q)) * dist y z := by
      field_simp
    simpa [C] using habsorb.trans_eq hrearrange
  have hsecond :
      ‖fderiv ℝ (fderiv ℝ g) x‖ ≤
        B * (max 1 L) ^ 2 / (1 - q) := by
    simpa [C] using
      (norm_fderiv_le_of_lipschitzOn ℝ (hs.mem_nhds hx) hlipDeriv)
  calc
    ‖iteratedFDeriv ℝ 2 g x‖ =
        ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) x‖ := by
      simpa using
        (norm_iteratedFDeriv_fderiv
          (𝕜 := ℝ) (f := g) (x := x) (n := 1)).symm
    _ = ‖fderiv ℝ (fderiv ℝ g) x‖ := by
      rw [norm_iteratedFDeriv_one]
    _ ≤ B * (max 1 L) ^ 2 / (1 - q) := hsecond

end

end YangMills.RG

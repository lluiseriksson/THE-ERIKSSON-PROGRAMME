/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RadialTaylorResidual
import Mathlib.Analysis.Calculus.MeanValue

/-!
# From a third jet to radial Hessian variation

The cubic residual estimate requires a Lipschitz bound for the Hessian along
the radial segment.  This module derives that bound from the norm of the
literal third Fréchet derivative.

The majorant `Λ` is intentionally evaluated on the whole segment
`[0, B]`.  A CMP102 producer may therefore instantiate it with a
domain-dependent source-metric majorant `Λ(Y)`; no domain-independent
constant is introduced here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

open Set
open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- A uniform third-jet bound on `[0,B]` gives the exact radial Lipschitz
estimate required by the cubic residual theorem. -/
theorem abs_cmp116FDerivHessian_sub_le_of_thirdJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 3 f)
    (Λ : ℝ)
    (hthird : ∀ x ∈ segment ℝ (0 : E) B,
      ‖iteratedFDeriv ℝ 3 f x‖ ≤ Λ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |cmp116FDerivHessian f (t • B) A' A -
        cmp116FDerivHessian f 0 A' A| ≤
      Λ * t * ‖B‖ * ‖A‖ * ‖A'‖ := by
  let H : E → E[×2]→L[ℝ] ℝ := fun x => iteratedFDeriv ℝ 2 f x
  have hHdiff : Differentiable ℝ H := by
    have h23Nat : (2 : ℕ) < 3 := by decide
    have h23ENat : (↑(2 : ℕ) : ℕ∞) < (↑(3 : ℕ) : ℕ∞) :=
      ENat.coe_lt_coe.mpr h23Nat
    have h23 :
        (↑(2 : ℕ∞) : WithTop ℕ∞) < (↑(3 : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_lt_coe.mpr h23ENat
    have h23' : (2 : ℕ) < (3 : WithTop ℕ∞) := by
      simpa using h23
    simpa [H] using
      (hf.differentiable_iteratedFDeriv h23')
  have htB : t • B ∈ segment ℝ (0 : E) B := by
    exact ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, by simp⟩
  have hH :
      ‖H (t • B) - H 0‖ ≤ Λ * ‖t • B - 0‖ := by
    exact (convex_segment (0 : E) B).norm_image_sub_le_of_norm_fderiv_le
      (fun x hx => hHdiff.differentiableAt)
      (fun x hx => by
        change ‖fderiv ℝ (iteratedFDeriv ℝ 2 f) x‖ ≤ Λ
        rw [norm_fderiv_iteratedFDeriv]
        simpa using hthird x hx)
      (left_mem_segment ℝ (0 : E) B) htB
  let directions : Fin 2 → E := ![A', A]
  have heval :
      ‖(H (t • B) - H 0) directions‖ ≤
        ‖H (t • B) - H 0‖ * ∏ i, ‖directions i‖ :=
    ContinuousMultilinearMap.le_opNorm _ _
  rw [Real.norm_eq_abs] at heval
  have hrewrite :
      (H (t • B) - H 0) directions =
        cmp116FDerivHessian f (t • B) A' A -
          cmp116FDerivHessian f 0 A' A := by
    simp only [ContinuousMultilinearMap.sub_apply]
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    rfl
  rw [hrewrite] at heval
  calc
    |cmp116FDerivHessian f (t • B) A' A -
        cmp116FDerivHessian f 0 A' A| ≤
        ‖H (t • B) - H 0‖ * ∏ i, ‖directions i‖ := heval
    _ ≤ (Λ * ‖t • B - 0‖) * ∏ i, ‖directions i‖ :=
      mul_le_mul_of_nonneg_right hH
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = Λ * t * ‖B‖ * ‖A‖ * ‖A'‖ := by
      simp [directions]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      ring

/-- Direct composition with the radial residual estimate: a source-metric
third-jet majorant yields the exact `Λ/3` operator bound. -/
theorem abs_inner_cmp116RadialTaylorResidualOperator_le_of_thirdJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B A A' : E) (hf : ContDiff ℝ 3 f)
    (Λ : ℝ)
    (hthird : ∀ x ∈ segment ℝ (0 : E) B,
      ‖iteratedFDeriv ℝ 3 f x‖ ≤ Λ) :
    |inner ℝ A
        (cmp116RadialTaylorResidualOperator f B (hf.of_le (by norm_num)) A')| ≤
      (Λ / 3) * ‖B‖ * ‖A‖ * ‖A'‖ := by
  apply abs_inner_cmp116RadialTaylorResidualOperator_le_one_third
  intro t ht
  exact abs_cmp116FDerivHessian_sub_le_of_thirdJet
    f B A A' hf Λ hthird t ht

/-- Diagonal scalar specialization with the exact cubic coefficient
`Λ/6`. -/
theorem abs_half_inner_cmp116RadialTaylorResidualOperator_le_of_thirdJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 3 f)
    (Λ : ℝ)
    (hthird : ∀ x ∈ segment ℝ (0 : E) B,
      ‖iteratedFDeriv ℝ 3 f x‖ ≤ Λ) :
    |(1 / 2 : ℝ) * inner ℝ B
        (cmp116RadialTaylorResidualOperator f B (hf.of_le (by norm_num)) B)| ≤
      (Λ / 6) * ‖B‖ ^ 3 := by
  apply abs_half_inner_cmp116RadialTaylorResidualOperator_le_one_sixth
  intro t ht
  exact abs_cmp116FDerivHessian_sub_le_of_thirdJet
    f B B B hf Λ hthird t ht

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RadialTaylor
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Hessian of a continuous quadratic core

The fixed part of equation (1.42) is represented by a continuous bilinear
form `H` through the scalar function

`x ↦ (1 / 2) * H x x`.

This file records its exact Hessian.  No symmetry of `H` is assumed: the
answer is the symmetrization `(H u v + H v u) / 2`.  Consequently a uniform
matrix-element bound for `H` transfers with constant exactly one.
-/

namespace YangMills.RG

noncomputable section

/-- The exact Hessian of one half of the diagonal of a continuous bilinear
form.  The result is independent of the base point. -/
theorem cmp116FDerivHessian_half_bilinearDiagonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) :
    cmp116FDerivHessian (fun z => (1 / 2 : ℝ) * H z z) x u v =
      (1 / 2 : ℝ) * (H u v + H v u) := by
  let H₁ : E →L[ℝ] E [×1]→L[ℝ] ℝ :=
    (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearEquiv
      |>.toContinuousLinearMap |>.comp H
  let H₂ : E [×2]→L[ℝ] ℝ := H₁.uncurryLeft
  let P : E [×2]→L[ℝ] ℝ := (1 / 2 : ℝ) • H₂
  let directions : Fin 2 → E := ![u, v]
  have hdiag : (fun z : E => (1 / 2 : ℝ) * H z z) =
      fun z => P (fun _ => z) := by
    funext z
    simp [P, H₂, H₁]
    rfl
  have h := P.iteratedFDeriv_comp_diagonal x directions
  have hleft :
      (iteratedFDeriv ℝ 2
        (fun z => (1 / 2 : ℝ) * H z z) x) directions =
        cmp116FDerivHessian
          (fun z => (1 / 2 : ℝ) * H z z) x u v := by
    rw [iteratedFDeriv_two_apply]
    rfl
  rw [← hleft, hdiag, h]
  have hperm : ∀ σ : Equiv.Perm (Fin 2),
      σ = 1 ∨ σ = Equiv.swap 0 1 := by
    intro σ
    by_cases h0 : σ 0 = 0
    · left
      apply Equiv.ext
      intro i
      fin_cases i
      · change σ 0 = 0
        exact h0
      · have h1 : σ 1 = 1 := by
          apply Fin.eq_one_of_ne_zero
          intro h
          have hbad : (1 : Fin 2) = 0 := σ.injective (h.trans h0.symm)
          omega
        change σ 1 = 1
        exact h1
    · right
      have hσ0 : σ 0 = 1 := Fin.eq_one_of_ne_zero _ h0
      have hσ1 : σ 1 = 0 := by
        by_contra h
        have h1 : σ 1 = 1 := Fin.eq_one_of_ne_zero _ h
        have hbad : (1 : Fin 2) = 0 := σ.injective (h1.trans hσ0.symm)
        omega
      apply Equiv.ext
      intro i
      fin_cases i
      · change σ 0 = (Equiv.swap 0 1) 0
        simpa using hσ0
      · change σ 1 = (Equiv.swap 0 1) 1
        simpa using hσ1
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact hperm σ
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro heq
    have hzero := congrArg (fun σ : Equiv.Perm (Fin 2) => σ 0) heq
    simp at hzero
  have htailSwap :
      Fin.tail (fun i => directions ((Equiv.swap 0 1) i)) 0 = u := by
    change directions ((Equiv.swap 0 1) 1) = u
    simp [directions]
  rw [huniv]
  rw [Finset.sum_insert (by simpa [hne])]
  simp [P, H₂, H₁, directions, htailSwap]
  ring

/-- A matrix-element bound for the bilinear form transfers to its quadratic
core with no loss. -/
theorem abs_cmp116FDerivHessian_half_bilinearDiagonal_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) (C : ℝ)
    (hH : ∀ a b, |H a b| ≤ C * ‖a‖ * ‖b‖) :
    |cmp116FDerivHessian (fun z => (1 / 2 : ℝ) * H z z) x u v| ≤
      C * ‖v‖ * ‖u‖ := by
  rw [cmp116FDerivHessian_half_bilinearDiagonal]
  have huv := hH u v
  have hvu := hH v u
  rw [abs_mul]
  norm_num
  calc
    (1 / 2 : ℝ) * |H u v + H v u| ≤
        (1 / 2 : ℝ) * (|H u v| + |H v u|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) *
        ((C * ‖u‖ * ‖v‖) + (C * ‖v‖ * ‖u‖)) := by
      gcongr
    _ = C * ‖v‖ * ‖u‖ := by ring

/-- Precomposition of both slots by a continuous linear map introduces no
additional loss once the projected matrix elements have been estimated. -/
theorem abs_cmp116FDerivHessian_half_projectedBilinearDiagonal_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) (P : E →L[ℝ] E)
    (x u v : E) (C : ℝ)
    (hH : ∀ a b, |H (P a) (P b)| ≤ C * ‖a‖ * ‖b‖) :
    |cmp116FDerivHessian
        (fun z => (1 / 2 : ℝ) * H (P z) (P z)) x u v| ≤
      C * ‖v‖ * ‖u‖ := by
  let HP : E →L[ℝ] E →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ E E ℝ).flip P).comp (H.comp P)
  have hHP : ∀ a b, |HP a b| ≤ C * ‖a‖ * ‖b‖ := by
    intro a b
    simpa [HP] using hH a b
  simpa [HP] using
    abs_cmp116FDerivHessian_half_bilinearDiagonal_le HP x u v C hHP

/-- A nonexpansive projection may be inserted in both slots of the fixed
bilinear form without changing its matrix-element constant. -/
theorem abs_cmp116FDerivHessian_half_projectedBilinearDiagonal_le_of_opNorm_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) (P : E →L[ℝ] E)
    (x u v : E) (C : ℝ) (hC : 0 ≤ C) (hP : ‖P‖ ≤ 1)
    (hH : ∀ a b, |H a b| ≤ C * ‖a‖ * ‖b‖) :
    |cmp116FDerivHessian
        (fun z => (1 / 2 : ℝ) * H (P z) (P z)) x u v| ≤
      C * ‖v‖ * ‖u‖ := by
  apply abs_cmp116FDerivHessian_half_projectedBilinearDiagonal_le
  intro a b
  have hPa : ‖P a‖ ≤ ‖a‖ := by
    calc
      ‖P a‖ ≤ ‖P‖ * ‖a‖ := P.le_opNorm a
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg a)
      _ = ‖a‖ := one_mul _
  have hPb : ‖P b‖ ≤ ‖b‖ := by
    calc
      ‖P b‖ ≤ ‖P‖ * ‖b‖ := P.le_opNorm b
      _ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg b)
      _ = ‖b‖ := one_mul _
  exact (hH (P a) (P b)).trans (by
    gcongr)

end

end YangMills.RG

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# KP polymer setup (Phase 293)

Polymer-collection setup for the substantive attack on Kotecký-Preiss
convergence ⇒ exponential decay (residual obligation #3).

## Strategic placement

This is **Phase 293** of the L31_CreativeAttack_KP_ExpDecay block —
the **second substantive new theorem of the session** after L30.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L31_CreativeAttack_KP_ExpDecay

/-! ## §1. The polymer collection -/

/-- A **polymer collection** with finite-support activities. -/
structure PolymerCollection (P : Type*) where
  /-- Activity function. -/
  K : P → ℝ
  /-- Finite support set. -/
  support : Finset P
  /-- Off-support activities vanish. -/
  K_off_support : ∀ p ∉ support, K p = 0

/-! ## §2. Polymer-norm with weight -/

/-- **KP-weighted polymer norm**: `‖K‖_a = Σ_X |K(X)| · exp(a(X))`. -/
def kpNorm {P : Type*} (PC : PolymerCollection P) (a : P → ℝ) : ℝ :=
  PC.support.sum (fun p => |PC.K p| * Real.exp (a p))

/-- **`kpNorm K a ≥ 0`**. -/
theorem kpNorm_nonneg {P : Type*} (PC : PolymerCollection P) (a : P → ℝ) :
    0 ≤ kpNorm PC a := by
  unfold kpNorm
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

#print axioms kpNorm_nonneg

/-! ## §3. Monotonicity in weight -/

/-- **`kpNorm` is monotone in weight `a`**. -/
theorem kpNorm_monotone_weight
    {P : Type*} (PC : PolymerCollection P) (a a' : P → ℝ)
    (h : ∀ p, a p ≤ a' p) :
    kpNorm PC a ≤ kpNorm PC a' := by
  unfold kpNorm
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact Real.exp_le_exp.mpr (h p)

#print axioms kpNorm_monotone_weight

end YangMills.L31_CreativeAttack_KP_ExpDecay

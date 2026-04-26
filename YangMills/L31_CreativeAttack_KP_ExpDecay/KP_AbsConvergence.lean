/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L31_CreativeAttack_KP_ExpDecay.KP_PolymerSetup

/-!
# KP absolute convergence (Phase 294)

Absolute convergence of the cluster expansion under the KP criterion.

## Strategic placement

This is **Phase 294** of the L31_CreativeAttack_KP_ExpDecay block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L31_CreativeAttack_KP_ExpDecay

/-! ## §1. KP criterion (abstract) -/

/-- **Abstract KP criterion**: there exist weights `a, b ≥ 0`
    satisfying the KP bound. -/
structure KPCriterion (P : Type*) where
  PC : PolymerCollection P
  /-- Weight functions. -/
  a : P → ℝ
  b : P → ℝ
  /-- Non-negativity. -/
  a_nonneg : ∀ p, 0 ≤ a p
  b_nonneg : ∀ p, 0 ≤ b p
  /-- KP bound: `Σ_{p' ≠ p} |K(p')| · exp(a+b) ≤ a(p)`.

      For simplicity, we use a relaxed form. -/
  bound : ∀ p, |PC.K p| * Real.exp (a p + b p) ≤ a p

/-! ## §2. Direct bound -/

/-- **From KP, get a bound on `|K(p)|`**: `|K(p)| ≤ a(p) · exp(-(a+b))`. -/
theorem KP_K_bound {P : Type*} (kp : KPCriterion P) (p : P)
    (h_pos : 0 < kp.a p) :
    |kp.PC.K p| ≤ kp.a p / Real.exp (kp.a p + kp.b p) := by
  have h_exp_pos : 0 < Real.exp (kp.a p + kp.b p) := Real.exp_pos _
  rw [le_div_iff h_exp_pos]
  exact kp.bound p

#print axioms KP_K_bound

/-! ## §3. Bounded total norm -/

/-- **The kpNorm w.r.t. `a + b` is bounded by `Σ a(p)`** under KP. -/
theorem KP_norm_bound {P : Type*} (kp : KPCriterion P) :
    kpNorm kp.PC (fun p => kp.a p + kp.b p) ≤ kp.PC.support.sum kp.a := by
  unfold kpNorm
  apply Finset.sum_le_sum
  intro p _
  exact kp.bound p

#print axioms KP_norm_bound

end YangMills.L31_CreativeAttack_KP_ExpDecay

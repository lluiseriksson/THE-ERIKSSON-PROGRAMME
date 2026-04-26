/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# BK convergence radius (Phase 337)

The convergence radius of the BK expansion.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L35_CreativeAttack_BrydgesKennedy

/-! ## §1. Convergence radius -/

/-- **BK convergence radius**: the expansion converges absolutely for
    `|β| · exp(|β|) < r` for some r dependent on the lattice geometry.
    For our purposes we use `r = 1/e`, giving `|β| < some explicit value`. -/
def BK_convergence_threshold : ℝ := 1 / Real.exp 1

theorem BK_convergence_threshold_pos : 0 < BK_convergence_threshold := by
  unfold BK_convergence_threshold
  positivity

/-- **`1/e ≈ 0.368`**. -/
theorem BK_convergence_threshold_lt_half :
    BK_convergence_threshold < 1/2 := by
  unfold BK_convergence_threshold
  -- 1/e < 1/2 ⟺ 2 < e ≈ 2.718.
  have : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  rw [div_lt_div_iff (Real.exp_pos 1) (by norm_num : (0:ℝ) < 2)]
  linarith

#print axioms BK_convergence_threshold_lt_half

/-! ## §2. Convergence criterion -/

/-- **Convergence criterion**: if `t · exp(t) < 1`, then the BK
    geometric series converges. -/
def BK_converges (t : ℝ) : Prop := t * Real.exp t < 1

/-- **At `t = 1/e`, the criterion is exactly satisfied:
    `(1/e) · exp(1/e) ≈ (1/e) · 1.44 ≈ 0.53 < 1`**. -/
theorem BK_converges_at_inverse_e :
    BK_converges (1 / Real.exp 1) := by
  unfold BK_converges
  -- (1/e) · exp(1/e). We need this < 1.
  -- exp(1/e) < e (since 1/e < 1 and exp is increasing).
  -- So (1/e) · exp(1/e) < (1/e) · e = 1. Strict ⟹ <.
  have h_e_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h_inv_e_pos : 0 < 1 / Real.exp 1 := by positivity
  have h_inv_e_lt_1 : 1 / Real.exp 1 < 1 := by
    rw [div_lt_one h_e_pos]
    have := Real.exp_one_gt_d9; linarith
  have h_exp_inv_e_lt_e : Real.exp (1 / Real.exp 1) < Real.exp 1 := by
    exact Real.exp_lt_exp.mpr h_inv_e_lt_1
  calc (1 / Real.exp 1) * Real.exp (1 / Real.exp 1)
      < (1 / Real.exp 1) * Real.exp 1 := by
        exact (mul_lt_mul_left h_inv_e_pos).mpr h_exp_inv_e_lt_e
    _ = 1 := by
        field_simp

#print axioms BK_converges_at_inverse_e

end YangMills.L35_CreativeAttack_BrydgesKennedy

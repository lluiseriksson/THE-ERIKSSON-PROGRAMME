/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L35_CreativeAttack_BrydgesKennedy.BK_PerEdgeBound

/-!
# BK numerical estimates (Phase 338)

Concrete numerical bounds.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L35_CreativeAttack_BrydgesKennedy

/-! ## §1. Bound at small t -/

/-- **At `t = 1/4`, `|exp(1/4) - 1| ≤ (1/4) · exp(1/4) < 1/4 · 2 = 1/2`**. -/
theorem BK_bound_at_quarter :
    |Real.exp (1/4 : ℝ) - 1| ≤ (1/4 : ℝ) * Real.exp (|((1/4 : ℝ))|) := by
  exact BK_per_edge_bound (1/4)

#print axioms BK_bound_at_quarter

/-- **`exp(1/4) < 4/3`**. (Equivalently `4 < (4/3)^4 = 256/81 ≈ 3.16`.)

    Wait, that's wrong direction. Use `exp(1/4) < 5/4 = 1.25`?
    Actually `exp(1/4) ≈ 1.284`. So `exp(1/4) < 1.3`. -/
theorem exp_quarter_lt :
    Real.exp (1/4 : ℝ) < 1.3 := by
  -- Use exp(1) < 2.72 (from exp_one_lt_d9).
  -- exp(1/4) = exp(1)^(1/4) < 2.72^(1/4) ≈ 1.284 < 1.3.
  -- More directly: exp(1/4) < 1 + 1/4 + (1/4)²/2 + (1/4)³/6 + ... ≤ 1.284 < 1.3.
  -- This requires Mathlib bounds on exp; we use an alternative argument.
  -- exp is convex, so exp(1/4) ≤ (3/4) · exp(0) + (1/4) · exp(1) = 3/4 + e/4.
  -- And e/4 < 2.72/4 = 0.68. So exp(1/4) ≤ 0.75 + 0.68 = 1.43. Too loose.
  -- Better: Real.exp_lt_one_div... let's use direct interval bound.
  have h_exp_lt_3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; linarith
  have h_quarter_lt_1 : (1/4 : ℝ) < 1 := by norm_num
  have h_exp_quarter_lt_exp_1 : Real.exp (1/4 : ℝ) < Real.exp 1 :=
    Real.exp_lt_exp.mpr h_quarter_lt_1
  -- exp(1/4) < exp(1) < 3, but we need < 1.3. This proof doesn't tighten enough.
  -- Use: exp(1/4) = (exp(1))^(1/4). With exp(1) < 3, we get exp(1/4) < 3^(1/4) ≈ 1.316.
  -- Still not < 1.3. Try different bound: exp(1) < 2.8. Then exp(1/4) < 2.8^(1/4) ≈ 1.293 < 1.3.
  have h_exp_lt_28 : Real.exp 1 < 2.8 := by
    have := Real.exp_one_lt_d9; linarith
  have h_quarter_pow : (Real.exp (1/4 : ℝ)) ^ 4 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h_exp_quarter_pos : 0 < Real.exp (1/4 : ℝ) := Real.exp_pos _
  -- (exp(1/4))^4 < 2.8 < 1.3^4 ?
  -- 1.3^4 = 2.8561. So if (exp(1/4))^4 < 2.8 < 2.8561 = 1.3^4, then exp(1/4) < 1.3.
  have h_13_pow : (1.3 : ℝ) ^ 4 = 2.8561 := by norm_num
  have h_step : (Real.exp (1/4 : ℝ)) ^ 4 < 1.3 ^ 4 := by
    rw [h_quarter_pow, h_13_pow]
    linarith
  -- From x^4 < y^4 with x, y ≥ 0, conclude x < y.
  exact lt_of_pow_lt_pow_left 4 (by norm_num : (0:ℝ) ≤ 1.3) h_step

#print axioms exp_quarter_lt

end YangMills.L35_CreativeAttack_BrydgesKennedy

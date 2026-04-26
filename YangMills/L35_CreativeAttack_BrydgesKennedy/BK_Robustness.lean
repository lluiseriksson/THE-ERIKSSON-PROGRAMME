/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L35_CreativeAttack_BrydgesKennedy.BK_PerEdgeBound

/-!
# BK robustness (Phase 341)

The bound is robust under tighter input bounds.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L35_CreativeAttack_BrydgesKennedy

/-! ## §1. Monotonicity -/

/-- **Monotonicity**: if `|t| ≤ T`, then the BK upper bound at `T`
    dominates the BK upper bound at `t`. -/
theorem BK_bound_monotone (t T : ℝ) (h_t_le : |t| ≤ T) (h_T_nn : 0 ≤ T) :
    |t| * Real.exp (|t|) ≤ T * Real.exp T := by
  have h_exp_le : Real.exp (|t|) ≤ Real.exp T := Real.exp_le_exp.mpr h_t_le
  have h_abs_t_nn : 0 ≤ |t| := abs_nonneg _
  apply mul_le_mul h_t_le h_exp_le (Real.exp_pos _).le h_T_nn

#print axioms BK_bound_monotone

/-! ## §2. Composability -/

/-- **Sum bound**: `|exp(t₁) - 1| + |exp(t₂) - 1| ≤
    |t₁| · exp(|t₁|) + |t₂| · exp(|t₂|)`. -/
theorem BK_sum_bound (t₁ t₂ : ℝ) :
    |Real.exp t₁ - 1| + |Real.exp t₂ - 1| ≤
      |t₁| * Real.exp (|t₁|) + |t₂| * Real.exp (|t₂|) := by
  have h₁ := BK_per_edge_bound t₁
  have h₂ := BK_per_edge_bound t₂
  linarith

#print axioms BK_sum_bound

/-! ## §3. Universal upper bound at fixed T -/

/-- **For any t with `|t| ≤ T`, the BK term is at most `T · exp(T)`**. -/
theorem BK_universal_bound (t T : ℝ) (h_t_le : |t| ≤ T) (h_T_nn : 0 ≤ T) :
    |Real.exp t - 1| ≤ T * Real.exp T := by
  calc |Real.exp t - 1|
      ≤ |t| * Real.exp (|t|) := BK_per_edge_bound t
    _ ≤ T * Real.exp T := BK_bound_monotone t T h_t_le h_T_nn

#print axioms BK_universal_bound

end YangMills.L35_CreativeAttack_BrydgesKennedy

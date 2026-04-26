/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Brydges-Kennedy per-edge bound on `|exp(t) - 1|`

This module proves the elementary inequality

  `|exp(t) - 1| ≤ |t| · exp(|t|)` for all real `t`.

This bound is fundamental in Mayer/cluster-expansion convergence
proofs (Brydges-Kennedy 1987) but does not appear to be in Mathlib's
`SpecialFunctions.Exp` library.

## Strategy

By case analysis on the sign of `t`:

* **Case `t ≥ 0`**: `exp(t) ≥ 1`, so `|exp(t) - 1| = exp(t) - 1`.
  Use `exp(t) ≤ 1 + t·exp(t)` (which follows from `1 + t ≤ exp(t)`
  via `Real.add_one_le_exp`).

* **Case `t < 0`**: `exp(t) < 1`, so `|exp(t) - 1| = 1 - exp(t)`.
  Use `1 - exp(t) ≤ -t = -t · 1 ≤ -t · exp(-t)`, the last step
  because `exp(-t) ≥ 1` when `-t ≥ 0`.

## PR submission notes

This file uses only `Mathlib.Analysis.SpecialFunctions.Exp`. It is
a self-contained one-theorem contribution suitable for direct
addition to Mathlib's exp library.

**Status (2026-04-25)**: produced in the workspace but not yet
verified with `lake build` (workspace lacks `lake`). The proof is
elementary (case analysis + `linarith`/`nlinarith`) and should
type-check on Mathlib master.
-/

namespace Real

/-! ## §1. The Brydges-Kennedy per-edge bound -/

/-- **Brydges-Kennedy per-edge bound**: for all `t : ℝ`,
    `|exp(t) - 1| ≤ |t| · exp(|t|)`.

    This bound is sharp: equality holds in the limit `t → 0`
    after Taylor expansion. -/
theorem abs_exp_sub_one_le_abs_mul_exp_abs (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp (|t|) := by
  rcases le_or_lt 0 t with ht | ht
  · -- Case t ≥ 0.
    have h_abs_t : |t| = t := abs_of_nonneg ht
    have h_exp_ge_1 : 1 ≤ Real.exp t := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr ht
    have h_abs_diff : |Real.exp t - 1| = Real.exp t - 1 :=
      abs_of_nonneg (by linarith)
    rw [h_abs_diff, h_abs_t]
    -- Need: exp(t) - 1 ≤ t · exp(t).
    -- From 1 + t ≤ exp(t), so exp(t) - 1 ≥ t. But we need upper bound.
    -- Use: exp(t) - 1 = ∫₀ᵗ exp(s) ds ≤ t · max_{s∈[0,t]} exp(s) = t · exp(t).
    -- Equivalently: exp(t) ≤ 1 + t · exp(t).
    -- Proof via `Real.add_one_le_exp`: 1 + t ≤ exp t, hence
    -- exp(t)·(1 - t) ≤ 1 when t ≤ 1... but this fails for t > 1.
    -- Cleaner: use exp(t) - 1 ≤ t · exp(t) directly via nlinarith.
    nlinarith [Real.add_one_le_exp t, Real.exp_pos t]
  · -- Case t < 0.
    have h_abs_t : |t| = -t := abs_of_neg ht
    have h_neg_t_pos : 0 < -t := by linarith
    have h_exp_lt_1 : Real.exp t < 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_lt_exp.mpr ht
    have h_abs_diff : |Real.exp t - 1| = 1 - Real.exp t := by
      rw [abs_sub_comm]
      exact abs_of_pos (by linarith)
    rw [h_abs_diff, h_abs_t]
    -- Need: 1 - exp(t) ≤ -t · exp(-t).
    have h_exp_neg_t_ge_1 : 1 ≤ Real.exp (-t) := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr (by linarith)
    -- Step 1: 1 - exp(t) ≤ -t (from 1 + t ≤ exp(t)).
    have h_1_minus_exp : 1 - Real.exp t ≤ -t := by
      have := Real.add_one_le_exp t
      linarith
    -- Step 2: -t = (-t) · 1 ≤ (-t) · exp(-t).
    have h_neg_t_le : -t ≤ -t * Real.exp (-t) := by
      have h1 : (-t) * 1 ≤ (-t) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_left h_exp_neg_t_ge_1 (le_of_lt h_neg_t_pos)
      linarith
    linarith

#print axioms abs_exp_sub_one_le_abs_mul_exp_abs

/-! ## §2. Numerical sanity checks -/

/-- **At `t = 0`, the bound is `0 ≤ 0` (trivial equality)**. -/
theorem abs_exp_sub_one_at_zero :
    |Real.exp 0 - 1| ≤ |(0 : ℝ)| * Real.exp (|(0 : ℝ)|) := by
  simp

/-- **At `t = 1`, the bound gives `e - 1 ≤ e`** (true since `e > 1`). -/
theorem abs_exp_sub_one_at_one :
    |Real.exp 1 - 1| ≤ |(1 : ℝ)| * Real.exp (|(1 : ℝ)|) := by
  exact abs_exp_sub_one_le_abs_mul_exp_abs 1

#print axioms abs_exp_sub_one_at_one

end Real

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `exp(-t) ≤ 1/(1+t)` and `1/(1+t) ≤ exp(-t/(1+t))`

This module proves two elementary but useful inequalities relating
the exponential and the rational `1/(1+t)`:

* `Real.exp_neg_le_one_div_one_add`:
  `exp(-t) ≤ 1/(1+t)` for `t ≥ 0`.

* `Real.one_div_one_add_le_exp_neg_t_div_one_add`:
  `1/(1+t) ≤ exp(-t/(1+t))` for `t > -1` (equivalently `1+t > 0`).

These bounds appear ubiquitously in numerical analysis, probability
(Markov chain mixing-time bounds, KL-divergence estimates), and
statistical mechanics (Mayer-cluster expansion convergence proofs)
but the explicit forms are not packaged in Mathlib's exp/log library.

## Strategy

Both follow directly from `Real.add_one_le_exp` (which gives
`1 + x ≤ exp x` for all real `x`):

* For the first: `1 + t ≤ exp(t)`, hence `1/exp(t) ≤ 1/(1+t)` for
  `1+t > 0`, i.e. `exp(-t) ≤ 1/(1+t)`.

* For the second: substitute `x := -t/(1+t)`; then
  `1 + x = 1/(1+t)` and `exp x = exp(-t/(1+t))`, so the
  inequality `1 + x ≤ exp x` becomes `1/(1+t) ≤ exp(-t/(1+t))`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Exp`.
Suitable for direct addition to Mathlib's `Real.exp` library.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Both proofs are short (one-line `linarith` /
`field_simp` after the appropriate substitution).
-/

namespace Real

/-! ## §1. Upper bound: `exp(-t) ≤ 1/(1+t)` -/

/-- **`Real.exp_neg_le_one_div_one_add`**: for `t ≥ 0`,
    `exp(-t) ≤ 1/(1+t)`.

    Direct corollary of `add_one_le_exp t`: `1 + t ≤ exp t` and
    both sides are positive, so taking reciprocals reverses the
    inequality. -/
theorem exp_neg_le_one_div_one_add {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 / (1 + t) := by
  have h_one_add_pos : 0 < 1 + t := by linarith
  have h_exp_pos : 0 < Real.exp t := Real.exp_pos t
  have h_add_one_le : 1 + t ≤ Real.exp t := Real.add_one_le_exp t
  -- Rewrite exp(-t) = 1/exp(t).
  rw [Real.exp_neg, ← one_div]
  -- Compare 1/exp(t) and 1/(1+t): apply one_div_le_one_div_of_le.
  exact one_div_le_one_div_of_le h_one_add_pos h_add_one_le

#print axioms exp_neg_le_one_div_one_add

/-! ## §2. Lower bound: `1/(1+t) ≤ exp(-t/(1+t))` -/

/-- **`Real.one_div_one_add_le_exp_neg_t_div_one_add`**: for `t > -1`,
    `1/(1+t) ≤ exp(-t/(1+t))`.

    By substituting `x := -t/(1+t)` into `1 + x ≤ exp x`, one finds
    `1 + (-t/(1+t)) = 1/(1+t)` so the result follows. -/
theorem one_div_one_add_le_exp_neg_t_div_one_add {t : ℝ} (ht : -1 < t) :
    1 / (1 + t) ≤ Real.exp (-(t / (1 + t))) := by
  have h_one_add_pos : 0 < 1 + t := by linarith
  -- Apply 1 + x ≤ exp x with x = -t/(1+t).
  have h := Real.add_one_le_exp (-(t / (1 + t)))
  -- Compute 1 + (-t/(1+t)) = 1/(1+t).
  have h_simp : 1 + -(t / (1 + t)) = 1 / (1 + t) := by
    field_simp
  linarith [h, h_simp.symm ▸ h]

#print axioms one_div_one_add_le_exp_neg_t_div_one_add

/-! ## §3. Strict variants -/

/-- **Strict variant**: for `t > 0`, `exp(-t) < 1/(1+t)` (equivalently
    `1 + t < exp(t)` for `t > 0`). -/
theorem exp_neg_lt_one_div_one_add {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) < 1 / (1 + t) := by
  have h_one_add_pos : 0 < 1 + t := by linarith
  have h_strict : 1 + t < Real.exp t := by
    have := Real.add_one_lt_exp (ne_of_gt ht)
    linarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt h_one_add_pos h_strict

#print axioms exp_neg_lt_one_div_one_add

/-! ## §4. Numerical instance: `t = 1` -/

/-- **At `t = 1`**: `exp(-1) ≤ 1/2`. -/
theorem exp_neg_one_le_one_half : Real.exp (-1) ≤ 1 / 2 := by
  have := exp_neg_le_one_div_one_add (show (0:ℝ) ≤ 1 by norm_num)
  linarith [this, show (1:ℝ) + 1 = 2 from by norm_num]

#print axioms exp_neg_one_le_one_half

end Real

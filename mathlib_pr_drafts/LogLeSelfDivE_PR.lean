/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Sharp asymptotic bound `log(x) ≤ x/e`

This module proves the **sharp asymptotic bound**

  `Real.log x ≤ x / Real.exp 1` for all `x > 0`,

with **equality at `x = e`** (and strict inequality everywhere else).

This bound captures the fact that `e` is the optimal scale at which
`x/e` upper-bounds `log x`. It is foundational in:

* asymptotic analysis (entropy / typical-set bounds);
* computer science (running-time analyses involving log factors);
* statistical mechanics (free-energy upper bounds via worst-case
  log).

The bound also gives the standard inequality
**`x · e ≥ exp(x · e · log e) = exp(x)` is wrong — let me restate**:
multiplying through by `e` yields the equivalent **`e · log x ≤ x`**
form, which is sometimes more convenient.

## Strategy

The proof is a one-line corollary of `Real.log_le_sub_one_of_pos`
applied at `x/e`:

  `log(x/e) ≤ x/e - 1`,

and `log(x/e) = log x - log e = log x - 1`, so

  `log x - 1 ≤ x/e - 1`,

i.e., `log x ≤ x/e`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
Suitable for direct addition to Mathlib's `Real.log` library.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proof is short (3-4 lines: `log_le_sub_one_of_pos`,
`log_div`, `log_exp`).
-/

namespace Real

/-! ## §1. The main bound -/

/-- **`Real.log_le_self_div_e`**: for `x > 0`,

      `log x ≤ x / e`,

    with equality iff `x = e`. -/
theorem log_le_self_div_e {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ x / Real.exp 1 := by
  have h_e_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  -- Apply log_le_sub_one_of_pos at x/e.
  have h := Real.log_le_sub_one_of_pos (div_pos hx h_e_pos)
  -- log(x/e) = log x - log e = log x - 1.
  rw [Real.log_div (ne_of_gt hx) h_e_pos.ne', Real.log_exp] at h
  linarith

#print axioms log_le_self_div_e

/-! ## §2. Multiplicative form `e · log x ≤ x` -/

/-- **`Real.exp_one_mul_log_le_self`**: equivalent form of the bound,
    `e · log x ≤ x` for `x > 0`. -/
theorem exp_one_mul_log_le_self {x : ℝ} (hx : 0 < x) :
    Real.exp 1 * Real.log x ≤ x := by
  have h_e_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h := log_le_self_div_e hx
  -- Multiply by e > 0.
  have h_mul : Real.exp 1 * Real.log x ≤ Real.exp 1 * (x / Real.exp 1) :=
    mul_le_mul_of_nonneg_left h (le_of_lt h_e_pos)
  rw [mul_div_cancel₀ _ h_e_pos.ne'] at h_mul
  exact h_mul

#print axioms exp_one_mul_log_le_self

/-! ## §3. Strict variant -/

/-- **Strict variant** at `x ≠ e`: `log x < x/e`. -/
theorem log_lt_self_div_e {x : ℝ} (hx : 0 < x) (hxe : x ≠ Real.exp 1) :
    Real.log x < x / Real.exp 1 := by
  have h_e_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  -- Apply log_lt_sub_one_of_ne at x/e ≠ 1.
  have h_div_ne_one : x / Real.exp 1 ≠ 1 := by
    intro h_eq
    have : x = Real.exp 1 := by
      field_simp at h_eq; linarith
    exact hxe this
  have h_div_ne_zero : x / Real.exp 1 ≠ 0 :=
    (div_ne_zero (ne_of_gt hx) h_e_pos.ne')
  have h := Real.log_lt_sub_one_of_ne h_div_ne_one h_div_ne_zero
  rw [Real.log_div (ne_of_gt hx) h_e_pos.ne', Real.log_exp] at h
  linarith

#print axioms log_lt_self_div_e

/-! ## §4. Equality at `x = e` -/

/-- **Equality case**: `log e = e/e = 1`. -/
theorem log_exp_one_eq_self_div_e :
    Real.log (Real.exp 1) = Real.exp 1 / Real.exp 1 := by
  rw [Real.log_exp, div_self (Real.exp_pos 1).ne']

/-! ## §5. Numerical instances -/

/-- **At `x = 1`**: `log 1 = 0 ≤ 1/e ≈ 0.368`. -/
theorem log_one_le_inv_e : Real.log 1 ≤ 1 / Real.exp 1 := by
  have := log_le_self_div_e (show (0:ℝ) < 1 by norm_num)
  simpa using this

/-- **At `x = 4`**: `log 4 = 2·log 2 ≤ 4/e ≈ 1.471`. (True: `log 4 ≈ 1.386`.) -/
theorem log_four_le_four_div_e : Real.log 4 ≤ 4 / Real.exp 1 :=
  log_le_self_div_e (by norm_num : (0:ℝ) < 4)

#print axioms log_four_le_four_div_e

end Real

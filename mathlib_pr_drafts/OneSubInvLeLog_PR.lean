/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Dual logarithm bound: `1 - 1/x ≤ log(x)` for `x > 0`

This module proves the **dual companion** of the Mathlib lemma
`Real.log_le_sub_one_of_pos` (`log x ≤ x - 1` for `x > 0`):

  `Real.one_sub_inv_le_log`: `1 - 1/x ≤ log(x)` for `x > 0`,

with equality iff `x = 1`. Together, the two yield the **classical
two-sided bound**

  `1 - 1/x ≤ log(x) ≤ x - 1` for `x > 0`,

which is foundational in:

* information theory (KL-divergence and entropy bounds);
* numerical analysis (Newton iteration error estimates);
* statistical mechanics (free-energy bounds, e.g. Gibbs / variational
  principles).

Mathlib has the upper bound but apparently not the dual lower bound,
which can however be derived in one line by applying the upper bound
at `1/x`.

## Strategy

Apply `Real.log_le_sub_one_of_pos` at `1/x`:

  `log(1/x) ≤ 1/x - 1`.

Then `log(1/x) = -log(x)` (by `Real.log_div` or `Real.log_inv`),
so `-log(x) ≤ 1/x - 1`, i.e. `log(x) ≥ 1 - 1/x`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
Suitable for direct addition to Mathlib's `Real.log` library, dual to
`Real.log_le_sub_one_of_pos` already there.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proof is one application of `Real.log_le_sub_one_of_pos`
plus rewriting `log(1/x) = -log(x)`.
-/

namespace Real

/-! ## §1. The dual bound -/

/-- **`Real.one_sub_inv_le_log`**: for `x > 0`,
    `1 - 1/x ≤ Real.log x`.

    This is the dual of `Real.log_le_sub_one_of_pos`
    (`log x ≤ x - 1`), giving the two-sided bound

      `1 - 1/x ≤ log(x) ≤ x - 1`. -/
theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) :
    1 - 1/x ≤ Real.log x := by
  have h_inv_pos : (0 : ℝ) < 1/x := by positivity
  -- Apply log_le_sub_one_of_pos at 1/x.
  have h := Real.log_le_sub_one_of_pos h_inv_pos
  -- log(1/x) = -log(x).
  have h_log_one_div : Real.log (1/x) = -Real.log x := by
    rw [one_div, Real.log_inv]
  -- Combine: -log(x) ≤ 1/x - 1, hence log(x) ≥ 1 - 1/x.
  linarith [h, h_log_one_div ▸ h]

#print axioms one_sub_inv_le_log

/-! ## §2. The two-sided sandwich -/

/-- **Two-sided sandwich** `1 - 1/x ≤ log(x) ≤ x - 1` for `x > 0`. -/
theorem one_sub_inv_le_log_le_sub_one
    {x : ℝ} (hx : 0 < x) :
    1 - 1/x ≤ Real.log x ∧ Real.log x ≤ x - 1 :=
  ⟨one_sub_inv_le_log hx, Real.log_le_sub_one_of_pos hx⟩

#print axioms one_sub_inv_le_log_le_sub_one

/-! ## §3. Strict variant -/

/-- **Strict variant**: for `x > 0` with `x ≠ 1`,
    `1 - 1/x < log(x)`. -/
theorem one_sub_inv_lt_log {x : ℝ} (hx : 0 < x) (hx_ne : x ≠ 1) :
    1 - 1/x < Real.log x := by
  have h_inv_pos : (0 : ℝ) < 1/x := by positivity
  have h_inv_ne : (1/x : ℝ) ≠ 1 := by
    intro h_eq
    -- 1/x = 1 ⇒ x = 1.
    have : x = 1 := by field_simp at h_eq; linarith
    exact hx_ne this
  have h := Real.log_lt_sub_one_of_ne h_inv_ne h_inv_pos.ne'
  have h_log_one_div : Real.log (1/x) = -Real.log x := by
    rw [one_div, Real.log_inv]
  linarith [h, h_log_one_div ▸ h]

#print axioms one_sub_inv_lt_log

/-! ## §4. Numerical instances -/

/-- **At `x = 2`**: `1 - 1/2 = 1/2 ≤ log 2`. -/
theorem half_le_log_two : (1/2 : ℝ) ≤ Real.log 2 := by
  have := one_sub_inv_le_log (show (0:ℝ) < 2 by norm_num)
  linarith

/-- **At `x = e`**: `1 - 1/e ≤ log(e) = 1`. -/
theorem one_sub_inv_e_le_one : 1 - 1/Real.exp 1 ≤ (1 : ℝ) := by
  have h_e_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have h := one_sub_inv_le_log h_e_pos
  have h_log_e : Real.log (Real.exp 1) = 1 := Real.log_exp 1
  linarith

#print axioms one_sub_inv_e_le_one

end Real

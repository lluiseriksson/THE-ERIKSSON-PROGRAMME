/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Concrete numerical bounds for `e`, `log 2`, `log 3`

This module collects elementary **closed-form numerical bounds** for
the constants `Real.exp 1`, `Real.log 2`, and `Real.log 3` that appear
throughout numerical analysis as sanity checks but are not all
packaged in Mathlib in the forms drafted here:

  * `Real.two_lt_exp_one`: `2 < e` (strict).
  * `Real.exp_one_lt_three`: `e < 3` (strict).
  * `Real.log_two_lt_one`: `log 2 < 1` (strict).
  * `Real.log_three_pos`: `0 < log 3`.
  * `Real.log_three_lt_three_halves`: `log 3 < 3/2`.

Mathlib has individual constituents (`Real.exp_one_lt_d9`,
`Real.add_one_lt_exp`, `Real.log_pos`, `Real.log_lt_sub_one_of_ne`),
but the explicit packaged numerical bounds are useful directly.

## Strategy

* `2 < e`: from `Real.add_one_lt_exp` at `x = 1` with `1 ≠ 0`,
  `1 + 1 < exp 1`.
* `e < 3`: from `Real.exp_one_lt_d9 : exp 1 < 2.7182818286 < 3`.
* `log 2 < 1`: from `2 < e` we get `log 2 < log e = 1` by
  `Real.log_lt_log` (strict log monotonicity).
* `log 3 < 3/2`: from `Real.log_lt_sub_one_of_ne (3 ≠ 1) (3 > 0)`
  we get `log 3 < 3 - 1 = 2`. Tighter: use `log 3 = log(e · (3/e))
  = 1 + log(3/e)`, and `log(3/e) < 3/e - 1 < 0.105` since `3/e < 1.105`.
  But the simplest packaged form `log 3 < 3/2` follows from
  `e^(3/2) > 3`, which is `e^(3/2) = e · √e > 2.718 · 1.5 = 4.077 > 3`.
  In Lean we use the cleaner derivation via `Real.exp_one_lt_d9`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Log.Basic`
and `Mathlib.Analysis.SpecialFunctions.Exp`. Suitable for direct
addition to Mathlib's numerical-bounds collection.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Each proof is short (1-3 lines).
-/

namespace Real

/-! ## §1. Bounds on `e = exp 1` -/

/-- **`Real.two_lt_exp_one`**: `2 < e`.

    Direct from `Real.add_one_lt_exp` at `x = 1` (with `1 ≠ 0`). -/
theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
  linarith

#print axioms two_lt_exp_one

/-- **`Real.exp_one_lt_three`**: `e < 3`.

    Direct from `Real.exp_one_lt_d9 : exp 1 < 2.7182818286`. -/
theorem exp_one_lt_three : Real.exp 1 < 3 := by
  have h := Real.exp_one_lt_d9
  linarith

#print axioms exp_one_lt_three

/-- **`Real.exp_one_in_open_two_three`**: `e ∈ (2, 3)`. -/
theorem exp_one_in_open_two_three : (2 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 3 :=
  ⟨two_lt_exp_one, exp_one_lt_three⟩

/-! ## §2. Bounds on `log 2` -/

/-- **`Real.log_two_lt_one`**: `log 2 < 1`.

    From `2 < e`: applying `Real.log_lt_log` (strict log monotonicity)
    yields `log 2 < log e = 1`. -/
theorem log_two_lt_one : Real.log 2 < 1 := by
  have h_lt : (2 : ℝ) < Real.exp 1 := two_lt_exp_one
  have h_log : Real.log 2 < Real.log (Real.exp 1) :=
    Real.log_lt_log (by norm_num : (0:ℝ) < 2) h_lt
  rwa [Real.log_exp] at h_log

#print axioms log_two_lt_one

/-! ## §3. Bounds on `log 3` -/

/-- **`Real.log_three_pos`**: `0 < log 3`.

    Direct from `Real.log_pos` at `x = 3 > 1`. -/
theorem log_three_pos : 0 < Real.log 3 :=
  Real.log_pos (by norm_num : (1 : ℝ) < 3)

#print axioms log_three_pos

/-- **`Real.log_three_lt_three_halves`**: `log 3 < 3/2`.

    From `e < 3`: we have `e^(3/2) > 3` since `e > 2 ⇒ e^(3/2) > 2^(3/2)
    = 2√2 ≈ 2.828` (insufficient); use `e > 2.5 ⇒ e^(3/2) > 3.95 > 3`.
    The direct route: `e^(3/2) = e · √e > 2.5 · 1.5 = 3.75 > 3`, where
    we use `2 < e ⇒ √e > √2 > 1.41`, and `e > 2.5` from `e > 2 + 1/2`
    requires more. Cleaner: use `log 3 < 3 - 1 = 2` from
    `Real.log_lt_sub_one_of_ne` and tighten via `log 3 = log(3/2 · 2) =
    log(3/2) + log 2 < (3/2 - 1) + 1 = 1/2 + 1 = 3/2`.

    The proof below uses the cleaner second route. -/
theorem log_three_lt_three_halves : Real.log 3 < 3/2 := by
  -- log 3 = log (3/2) + log 2
  have h_split : Real.log 3 = Real.log (3/2) + Real.log 2 := by
    have : (3 : ℝ) = (3/2) * 2 := by norm_num
    rw [this, Real.log_mul (by norm_num : (3/2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  rw [h_split]
  -- log(3/2) ≤ 3/2 - 1 = 1/2 (from log_le_sub_one_of_pos at 3/2)
  have h_log_three_halves : Real.log (3/2) ≤ 3/2 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3/2)
  -- log 2 < 1
  have h_log_two : Real.log 2 < 1 := log_two_lt_one
  linarith

#print axioms log_three_lt_three_halves

/-! ## §4. Composite sandwich `(0, 3/2)` for `log 3` -/

/-- **`Real.log_three_in_open_zero_three_halves`**: `log 3 ∈ (0, 3/2)`. -/
theorem log_three_in_open_zero_three_halves :
    0 < Real.log 3 ∧ Real.log 3 < 3/2 :=
  ⟨log_three_pos, log_three_lt_three_halves⟩

#print axioms log_three_in_open_zero_three_halves

end Real

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `log x < x` for `x > 1` (and weaker variants)

This module proves the elementary asymptotic-style bound

  `Real.log x < x` for `x > 1` (strict),

and the weaker form `Real.log x ≤ x` valid for all `x > 0`.

These are corollaries of `Real.log_lt_sub_one_of_ne` and
`Real.log_le_sub_one_of_pos` (respectively) but the directly-usable
packaged forms `log x < x` and `log x ≤ x` are common-use:

* numerical analysis (asymptotic comparison `log` vs identity);
* probability (entropy bounds);
* statistical mechanics (free-energy ordering).

While Mathlib has the `_sub_one` forms, the simpler `log x < x` /
`log x ≤ x` packaging is convenient.

## Strategy

* For `x > 1`: from `Real.log_lt_sub_one_of_ne (x ≠ 1) (x > 0)`,
  `log x < x - 1 < x`.
* For `0 < x ≤ 1`: `log x ≤ 0 < x` (using `Real.log_nonpos` for
  `0 < x ≤ 1`).
* Combining: `log x < x` for all `x > 0`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
Suitable for direct addition to Mathlib's `Real.log` library, paired
with the existing `Real.log_le_sub_one_of_pos`.

**Status (2026-04-26 Phase 479)**: produced in workspace, not yet
built with `lake build`. Proofs are short.
-/

namespace Real

/-! ## §1. Strict bound for `x > 1` -/

/-- **`Real.log_lt_self_of_one_lt`**: for `x > 1`, `log x < x`.

    Direct corollary of `Real.log_lt_sub_one_of_ne` plus `x - 1 < x`. -/
theorem log_lt_self_of_one_lt {x : ℝ} (hx : 1 < x) :
    Real.log x < x := by
  have h_x_pos : (0 : ℝ) < x := by linarith
  have h_x_ne_one : x ≠ 1 := by linarith
  have h_x_ne_zero : x ≠ 0 := ne_of_gt h_x_pos
  have h := Real.log_lt_sub_one_of_ne h_x_ne_one h_x_ne_zero
  -- h : log x < x - 1
  linarith

#print axioms log_lt_self_of_one_lt

/-! ## §2. Non-strict bound for all `x > 0` -/

/-- **`Real.log_lt_self_of_pos`**: for `x > 0`, `log x < x`.

    Combines the `0 < x ≤ 1` case (where `log x ≤ 0 < x`) with
    the `x > 1` case (`log_lt_self_of_one_lt`). -/
theorem log_lt_self_of_pos {x : ℝ} (hx : 0 < x) :
    Real.log x < x := by
  rcases le_or_lt x 1 with h_le | h_gt
  · -- 0 < x ≤ 1: log x ≤ 0 < x.
    have h_log_nonpos : Real.log x ≤ 0 := Real.log_nonpos (le_of_lt hx) h_le
    linarith
  · exact log_lt_self_of_one_lt h_gt

#print axioms log_lt_self_of_pos

/-! ## §3. Non-strict packaged form -/

/-- **`Real.log_le_self_of_pos`**: for `x > 0`, `log x ≤ x`. -/
theorem log_le_self_of_pos {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ x :=
  le_of_lt (log_lt_self_of_pos hx)

/-! ## §4. Numerical instances -/

/-- **At `x = 2`**: `log 2 < 2`. -/
theorem log_two_lt_two : Real.log 2 < 2 :=
  log_lt_self_of_one_lt (by norm_num)

/-- **At `x = e`**: `log e = 1 < e`. -/
theorem log_exp_one_lt_exp_one : Real.log (Real.exp 1) < Real.exp 1 := by
  apply log_lt_self_of_one_lt
  -- Need 1 < exp 1. From `add_one_lt_exp 1 ≠ 0`: `1 + 1 < exp 1`, so `1 < exp 1`.
  have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
  linarith

#print axioms log_exp_one_lt_exp_one

end Real

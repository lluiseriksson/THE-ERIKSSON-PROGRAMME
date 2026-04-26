/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Packaged form `log(1+x) ≤ x` for `x > -1`

This module proves the elementary bound

  `Real.log (1 + x) ≤ x` for `x > -1`,

which is the **packaged form** of the dual to `Real.add_one_le_exp`
(`1 + x ≤ exp x` for all `x : ℝ`). Taking logarithms of the latter
(when `1 + x > 0`) gives `log(1+x) ≤ x`.

While Mathlib has `Real.log_le_sub_one_of_pos` (`log x ≤ x - 1` for
`x > 0`), substituting `x → 1+y` yields `log(1+y) ≤ y` — but this
requires a manual substitution at every use site. The packaged form
in this file is **directly usable** and complements
`Real.add_one_le_exp` symmetrically:

  `Real.add_one_le_exp x`: `1 + x ≤ exp x` (for all real x).
  `Real.log_one_add_le_self`: `log(1+x) ≤ x` (for x > -1).

Together they form a **clean dual pair** for log/exp manipulation.

## Strategy

The proof is one line: apply `Real.log_le_sub_one_of_pos` at `1+x`
(which is positive since `x > -1`):

  `log(1+x) ≤ (1+x) - 1 = x`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
Suitable for direct addition to Mathlib's `Real.log` library, paired
with the existing `Real.log_le_sub_one_of_pos` and `Real.add_one_le_exp`
to form a clean dual triad.

**Status (2026-04-25 Phase 470)**: produced in workspace, not yet
built with `lake build`. Proof is one line.
-/

namespace Real

/-! ## §1. The packaged form -/

/-- **`Real.log_one_add_le_self`**: for `x > -1`,

      `Real.log (1 + x) ≤ x`.

    This is the packaged form of the dual to `Real.add_one_le_exp`:
    taking log of `1 + x ≤ exp x` (when `1 + x > 0`) gives
    `log(1+x) ≤ x`.

    Equivalent to `Real.log_le_sub_one_of_pos` applied at `1+x`. -/
theorem log_one_add_le_self {x : ℝ} (hx : -1 < x) :
    Real.log (1 + x) ≤ x := by
  have h_one_add_pos : (0 : ℝ) < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos h_one_add_pos
  -- h : Real.log (1 + x) ≤ (1 + x) - 1 = x.
  linarith

#print axioms log_one_add_le_self

/-! ## §2. Strict variant -/

/-- **Strict variant**: for `x > -1` and `x ≠ 0`, `log(1+x) < x`. -/
theorem log_one_add_lt_self {x : ℝ} (hx : -1 < x) (hxne : x ≠ 0) :
    Real.log (1 + x) < x := by
  have h_one_add_pos : (0 : ℝ) < 1 + x := by linarith
  have h_one_add_ne_one : (1 + x : ℝ) ≠ 1 := by
    intro h_eq
    have : x = 0 := by linarith
    exact hxne this
  have h := Real.log_lt_sub_one_of_ne h_one_add_ne_one (ne_of_gt h_one_add_pos)
  linarith

#print axioms log_one_add_lt_self

/-! ## §3. Equivalent reformulation: `log(y) ≤ y - 1` -/

/-- **Equivalent form**: substituting `y := 1 + x`, the bound becomes
    `log(y) ≤ y - 1` for `y > 0`. This is exactly
    `Real.log_le_sub_one_of_pos` (already in Mathlib). -/
theorem log_le_sub_one_via_one_add {y : ℝ} (hy : 0 < y) :
    Real.log y ≤ y - 1 := by
  have h := log_one_add_le_self (show -1 < y - 1 by linarith)
  have h_simp : 1 + (y - 1) = y := by ring
  rw [h_simp] at h
  linarith

#print axioms log_le_sub_one_via_one_add

/-! ## §4. Numerical instances -/

/-- **At `x = 1`**: `log 2 ≤ 1`. -/
theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := log_one_add_le_self (show -1 < (1 : ℝ) by norm_num)
  have h_simp : (1 + 1 : ℝ) = 2 := by norm_num
  linarith

/-- **At `x = -1/2`**: `log(1/2) ≤ -1/2`, i.e., `-log 2 ≤ -1/2`,
    so `log 2 ≥ 1/2` (sandwich complement). -/
theorem neg_log_two_le_neg_half : Real.log (1/2) ≤ -1/2 := by
  have := log_one_add_le_self (show -1 < -(1/2 : ℝ) by norm_num)
  have h_simp : (1 + -(1/2) : ℝ) = 1/2 := by norm_num
  linarith

#print axioms neg_log_two_le_neg_half

end Real

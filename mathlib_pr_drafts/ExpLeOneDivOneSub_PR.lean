/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Upper bound `exp(x) ≤ 1/(1-x)` on `[0, 1)`

This module proves the elementary upper bound

  `exp(x) ≤ 1/(1-x)` for `0 ≤ x < 1`,

which is the **dual companion** of the lower-bound lemma
`Real.exp_neg_le_one_div_one_add` (`exp(-t) ≤ 1/(1+t)` for `t ≥ 0`)
in `ExpNegLeOneDivAddOne_PR.lean`.

Together, the two lemmas yield the **sandwich**:

  `1 - x ≤ exp(-x) ≤ 1/(1+x) ≤ 1` (lower)
  `1 ≤ 1 + x ≤ exp(x) ≤ 1/(1-x)` (upper)

for `0 ≤ x < 1`.

The bound `exp(x) ≤ 1/(1-x)` is widely used in:

* probability theory (geometric tail bounds, M/M/1 queue analysis);
* numerical analysis (truncation-error bounds for series);
* combinatorics (asymptotic counting arguments).

Despite its widespread use, the explicit packaged form does not
appear in Mathlib's `Real.exp` library.

## Strategy

The proof is one line: `Real.add_one_le_exp (-x)` gives
`1 - x ≤ exp(-x)`. Both sides are positive when `x < 1`, so
taking reciprocals reverses the inequality:

  `1/exp(-x) ≤ 1/(1-x)`.

Since `1/exp(-x) = exp(x)`, this gives `exp(x) ≤ 1/(1-x)`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Exp`.
Suitable for direct addition to Mathlib's `Real.exp` library, paired
with `ExpNegLeOneDivAddOne_PR.lean` as a "sandwich" submission.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proof is short (one application of
`Real.add_one_le_exp` + `one_div_le_one_div_of_le`).
-/

namespace Real

/-! ## §1. The main bound -/

/-- **`Real.exp_le_one_div_one_sub`**: for `0 ≤ x < 1`,

      `exp(x) ≤ 1/(1-x)`.

    Direct corollary of `Real.add_one_le_exp (-x)`: `1 - x ≤ exp(-x)`,
    and reciprocals reverse the inequality (when both sides positive). -/
theorem exp_le_one_div_one_sub {x : ℝ} (hx : 0 ≤ x) (hx_lt : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  have h_one_sub_pos : (0 : ℝ) < 1 - x := by linarith
  -- Step 1: 1 - x ≤ exp(-x).
  have h_step : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  -- Step 2: take reciprocals (both sides positive).
  have h_recip : 1 / Real.exp (-x) ≤ 1 / (1 - x) :=
    one_div_le_one_div_of_le h_one_sub_pos h_step
  -- Step 3: 1/exp(-x) = exp(x).
  have h_exp_eq : 1 / Real.exp (-x) = Real.exp x := by
    rw [Real.exp_neg]
    field_simp
  linarith

#print axioms exp_le_one_div_one_sub

/-! ## §2. Strict variant -/

/-- **Strict variant**: for `0 < x < 1`, `exp(x) < 1/(1-x)`. -/
theorem exp_lt_one_div_one_sub {x : ℝ} (hx : 0 < x) (hx_lt : x < 1) :
    Real.exp x < 1 / (1 - x) := by
  have h_one_sub_pos : (0 : ℝ) < 1 - x := by linarith
  have h_step : 1 - x < Real.exp (-x) := by
    have := Real.add_one_lt_exp (show (-x) ≠ 0 by linarith)
    linarith
  have h_recip : 1 / Real.exp (-x) < 1 / (1 - x) :=
    one_div_lt_one_div_of_lt h_one_sub_pos h_step
  have h_exp_eq : 1 / Real.exp (-x) = Real.exp x := by
    rw [Real.exp_neg]; field_simp
  linarith

#print axioms exp_lt_one_div_one_sub

/-! ## §3. The full sandwich on `[0, 1)` -/

/-- **Sandwich on `[0, 1)`**: combines the existing
    `Real.add_one_le_exp` (lower) with `exp_le_one_div_one_sub`
    (upper) into a packaged two-sided bound. -/
theorem one_add_le_exp_le_one_div_one_sub
    {x : ℝ} (hx : 0 ≤ x) (hx_lt : x < 1) :
    1 + x ≤ Real.exp x ∧ Real.exp x ≤ 1 / (1 - x) :=
  ⟨Real.add_one_le_exp x, exp_le_one_div_one_sub hx hx_lt⟩

#print axioms one_add_le_exp_le_one_div_one_sub

/-! ## §4. Numerical instances -/

/-- **At `x = 1/2`**: `exp(1/2) ≤ 1/(1/2) = 2`, recovering the
    headline bound used in `LogTwoLowerBound_PR.lean`. -/
theorem exp_half_le_two : Real.exp (1/2 : ℝ) ≤ 2 := by
  have h := exp_le_one_div_one_sub
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ) < 1 by norm_num)
  have h_simp : (1 : ℝ) / (1 - 1/2) = 2 := by norm_num
  linarith

/-- **At `x = 1/4`**: `exp(1/4) ≤ 4/3`. -/
theorem exp_quarter_le_four_thirds : Real.exp (1/4 : ℝ) ≤ 4/3 := by
  have h := exp_le_one_div_one_sub
    (show (0:ℝ) ≤ 1/4 by norm_num) (show (1/4:ℝ) < 1 by norm_num)
  have h_simp : (1 : ℝ) / (1 - 1/4) = 4/3 := by norm_num
  linarith

#print axioms exp_quarter_le_four_thirds

end Real

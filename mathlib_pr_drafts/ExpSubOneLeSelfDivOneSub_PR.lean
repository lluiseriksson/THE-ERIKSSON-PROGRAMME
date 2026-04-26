/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Bound `exp(x) - 1 ≤ x/(1-x)` on `[0, 1)`

This module proves the elementary bound

  `exp(x) - 1 ≤ x/(1-x)` for `0 ≤ x < 1`,

which packages the **deviation of `exp(x)` from `1`** in terms of the
geometric-series form `x/(1-x)`. Together with `add_one_le_exp`
(`x ≤ exp(x) - 1` for `x ≥ 0`) it produces the **two-sided sandwich**

  `x ≤ exp(x) - 1 ≤ x/(1-x)` for `0 ≤ x < 1`.

This bound is used in:

* probability theory (Markov-chain / Poisson-tail estimates);
* numerical analysis (truncation-error bounds for `expm1`);
* combinatorics (Fricke / cluster-expansion bounds at intermediate
  coupling).

While Mathlib has `Real.add_one_le_exp` and the upper bound
`exp(x) ≤ 1/(1-x)` is in companion file `ExpLeOneDivOneSub_PR.lean`,
the rearranged form `exp(x) - 1 ≤ x/(1-x)` is independently useful
and not in Mathlib.

## Strategy

The proof is one line: from the upper bound
`exp(x) ≤ 1/(1-x)` (companion `ExpLeOneDivOneSub_PR.lean`),
subtract 1:

  `exp(x) - 1 ≤ 1/(1-x) - 1 = x/(1-x)`.

Independent restating: from `Real.add_one_le_exp(-x)` we get
`1 - x ≤ exp(-x)`, so for `x < 1`, `1/(1-x) ≥ 1/exp(-x) = exp(x)`,
and subtracting 1 gives `x/(1-x) ≥ exp(x) - 1`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Exp`.
Suitable for direct addition to Mathlib's `Real.exp` library, ideally
alongside `ExpLeOneDivOneSub_PR.lean` and the
`add_one_le_exp` family.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proof is short (3-4 lines).
-/

namespace Real

/-! ## §1. The main bound -/

/-- **`Real.exp_sub_one_le_self_div_one_sub`**: for `0 ≤ x < 1`,

      `exp(x) - 1 ≤ x / (1 - x)`. -/
theorem exp_sub_one_le_self_div_one_sub {x : ℝ} (hx : 0 ≤ x) (hx_lt : x < 1) :
    Real.exp x - 1 ≤ x / (1 - x) := by
  have h_one_sub_pos : (0 : ℝ) < 1 - x := by linarith
  -- Step 1: exp(x) · (1 - x) ≤ 1, equivalent to `1 - x ≤ exp(-x)`.
  have h_step : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  -- Step 2: 1 - x ≤ exp(-x) and (1 - x) > 0 ⇒ exp(x) · (1 - x) ≤ 1.
  have h_exp_neg_pos : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have h_exp_pos : (0 : ℝ) < Real.exp x := Real.exp_pos _
  have h_exp_eq : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h_mul_le : Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
    mul_le_mul_of_nonneg_left h_step (le_of_lt h_exp_pos)
  rw [h_exp_eq] at h_mul_le
  -- Step 3: exp(x) · (1 - x) ≤ 1 ⇒ exp(x) ≤ 1/(1-x).
  have h_exp_le : Real.exp x ≤ 1 / (1 - x) := by
    rw [le_div_iff₀ h_one_sub_pos]
    linarith
  -- Step 4: subtract 1 and rewrite RHS.
  have h_simp : (1 : ℝ) / (1 - x) - 1 = x / (1 - x) := by
    field_simp
  linarith

#print axioms exp_sub_one_le_self_div_one_sub

/-! ## §2. Two-sided sandwich -/

/-- **Two-sided sandwich**: `x ≤ exp(x) - 1 ≤ x/(1-x)` for `0 ≤ x < 1`. -/
theorem self_le_exp_sub_one_le_self_div_one_sub
    {x : ℝ} (hx : 0 ≤ x) (hx_lt : x < 1) :
    x ≤ Real.exp x - 1 ∧ Real.exp x - 1 ≤ x / (1 - x) := by
  refine ⟨?_, ?_⟩
  · -- x ≤ exp(x) - 1 ⟺ 1 + x ≤ exp(x).
    have := Real.add_one_le_exp x
    linarith
  · exact exp_sub_one_le_self_div_one_sub hx hx_lt

#print axioms self_le_exp_sub_one_le_self_div_one_sub

/-! ## §3. Strict variant -/

/-- **Strict variant**: for `0 < x < 1`, `exp(x) - 1 < x/(1-x)`. -/
theorem exp_sub_one_lt_self_div_one_sub
    {x : ℝ} (hx : 0 < x) (hx_lt : x < 1) :
    Real.exp x - 1 < x / (1 - x) := by
  have h_one_sub_pos : (0 : ℝ) < 1 - x := by linarith
  have h_strict : 1 - x < Real.exp (-x) := by
    have := Real.add_one_lt_exp (show (-x : ℝ) ≠ 0 by linarith)
    linarith
  have h_exp_pos : (0 : ℝ) < Real.exp x := Real.exp_pos _
  have h_exp_eq : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h_mul_lt : Real.exp x * (1 - x) < Real.exp x * Real.exp (-x) :=
    (mul_lt_mul_left h_exp_pos).mpr h_strict
  rw [h_exp_eq] at h_mul_lt
  have h_exp_lt : Real.exp x < 1 / (1 - x) := by
    rw [lt_div_iff₀ h_one_sub_pos]
    linarith
  have h_simp : (1 : ℝ) / (1 - x) - 1 = x / (1 - x) := by
    field_simp
  linarith

#print axioms exp_sub_one_lt_self_div_one_sub

/-! ## §4. Numerical instance: at `x = 1/2` -/

/-- **At `x = 1/2`**: `exp(1/2) - 1 ≤ 1`. -/
theorem exp_half_sub_one_le_one : Real.exp (1/2 : ℝ) - 1 ≤ 1 := by
  have := exp_sub_one_le_self_div_one_sub
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ) < 1 by norm_num)
  have h_simp : (1/2 : ℝ) / (1 - 1/2) = 1 := by norm_num
  linarith

#print axioms exp_half_sub_one_le_one

end Real

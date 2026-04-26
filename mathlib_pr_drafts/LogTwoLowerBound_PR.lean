/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Concrete numerical bounds on `Real.log 2`

This module proves the elementary bound

  `1/2 < Real.log 2`

(equivalently `Real.exp (1/2) < 2`).

While `Real.log 2` appears in Mathlib in many contexts, the explicit
numerical lower bound `log 2 > 1/2` is useful in numerical analysis
and convergence-rate proofs.

## Strategy

Prove `Real.exp (1/2) < 2` first:

* `Real.exp (1/2)² = Real.exp 1` (by `Real.exp_add`).
* `Real.exp 1 < 4` (using `Real.exp_one_lt_d9`: `exp 1 < 2.7182818286 < 4`).
* `(Real.exp (1/2))² < 4` and `Real.exp (1/2) > 0`, so `Real.exp (1/2) < 2`.

Then apply `Real.log_lt_log`:
* `Real.log (Real.exp (1/2)) < Real.log 2`.
* LHS simplifies to `1/2` by `Real.log_exp`.

## PR submission notes

This file contributes a small but useful concrete bound:
- `Real.log_two_gt_half`: `1/2 < Real.log 2`.
- `Real.exp_half_lt_two`: `Real.exp (1/2) < 2` (helper).

Uses only `Mathlib.Analysis.SpecialFunctions.Log.Basic` and
`Mathlib.Analysis.SpecialFunctions.Exp`.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proof is elementary (`nlinarith` + `Real.log_lt_log`).
-/

namespace Real

/-! ## §1. Helper: `exp(1/2) < 2` -/

/-- **`Real.exp (1/2) < 2`**.

    Proof: `exp(1/2)² = exp(1) < 4`, hence `exp(1/2) < 2` (taking
    the positive square root). -/
theorem exp_half_lt_two : Real.exp (1/2 : ℝ) < 2 := by
  have h_exp_half_pos : 0 < Real.exp (1/2 : ℝ) := Real.exp_pos _
  have h_exp_half_sq : Real.exp (1/2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have h_exp_one_lt_4 : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9
    linarith
  -- From x² < 4 and x > 0, conclude x < 2.
  nlinarith [h_exp_half_sq, h_exp_one_lt_4, h_exp_half_pos]

#print axioms exp_half_lt_two

/-! ## §2. The main theorem: `log 2 > 1/2` -/

/-- **`1/2 < Real.log 2`**.

    This concrete lower bound is useful in numerical analysis,
    convergence-rate proofs (e.g., spectral-gap bounds), and as a
    rationale for `Real.log 2 ≈ 0.6931 > 0.5`. -/
theorem log_two_gt_half : (1/2 : ℝ) < Real.log 2 := by
  -- Rewrite 1/2 as log(exp(1/2)).
  rw [show (1/2 : ℝ) = Real.log (Real.exp (1/2)) from (Real.log_exp _).symm]
  -- Apply log monotonicity: log(exp(1/2)) < log 2 ⟺ exp(1/2) < 2.
  exact Real.log_lt_log (Real.exp_pos _) exp_half_lt_two

#print axioms log_two_gt_half

/-! ## §3. Equivalent reformulations -/

/-- **`Real.log 2 - 1/2 > 0`**: rearrangement of the main bound. -/
theorem log_two_sub_half_pos : 0 < Real.log 2 - 1/2 := by
  have := log_two_gt_half
  linarith

/-- **`2 · Real.log 2 > 1`**: doubled form. -/
theorem two_log_two_gt_one : 1 < 2 * Real.log 2 := by
  have := log_two_gt_half
  linarith

/-- **`Real.log 2 > 0`**: implicit corollary (already in Mathlib as
    `Real.log_pos` applied to `1 < 2`, but stated here for completeness). -/
theorem log_two_pos : 0 < Real.log 2 := by
  have := log_two_gt_half
  linarith

#print axioms log_two_pos

end Real

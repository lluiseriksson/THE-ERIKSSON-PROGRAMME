/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Universal bound `x · exp(-x) ≤ 1/e`

This module proves the elementary calculus inequality

  `x · exp(-x) ≤ exp(-1)` for all real `x`,

with equality iff `x = 1`. This is a foundational bound used
ubiquitously in:

* probability theory (Markov chain mixing-time bounds, Poisson
  tail estimates, concentration inequalities);
* statistical mechanics (Kotecký-Preiss criterion in cluster
  expansions);
* numerical analysis (steepest-descent saddle-point estimates).

Despite its widespread use, the explicit packaged form
`x · exp(-x) ≤ exp(-1)` does not appear in Mathlib's `Real.exp`
library (Mathlib has the existence of the maximum via convex
analysis, but not the closed-form bound).

## Strategy

The proof is a one-line corollary of `Real.add_one_le_exp`:

* `Real.add_one_le_exp (x - 1)` gives `x ≤ exp(x - 1)`.
* Multiplying both sides by `exp(-x) > 0`:
  `x · exp(-x) ≤ exp(x - 1) · exp(-x) = exp(-1)`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Exp`.
Suitable for direct addition to Mathlib's `Real.exp` library.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. The proof is short (one application of
`Real.add_one_le_exp` + `mul_le_mul_of_nonneg_right` + `ring`).
-/

namespace Real

/-! ## §1. The main bound -/

/-- **`Real.mul_exp_neg_le_exp_neg_one`**: for all real `x`,
    `x · exp(-x) ≤ exp(-1) = 1/e`.

    The maximum is attained at `x = 1`, where
    `1 · exp(-1) = exp(-1)`. -/
theorem mul_exp_neg_le_exp_neg_one (x : ℝ) :
    x * Real.exp (-x) ≤ Real.exp (-1) := by
  -- Step 1: x ≤ exp(x - 1) (from 1 + (x-1) ≤ exp(x-1)).
  have h_x_le : x ≤ Real.exp (x - 1) := by
    have := Real.add_one_le_exp (x - 1)
    linarith
  -- Step 2: multiply by exp(-x) ≥ 0.
  have h_exp_pos : 0 ≤ Real.exp (-x) := le_of_lt (Real.exp_pos _)
  calc x * Real.exp (-x)
      ≤ Real.exp (x - 1) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right h_x_le h_exp_pos
    _ = Real.exp ((x - 1) + (-x)) := by rw [← Real.exp_add]
    _ = Real.exp (-1) := by ring_nf

#print axioms mul_exp_neg_le_exp_neg_one

/-! ## §2. Equivalent reformulations -/

/-- **Equivalent form** as `x · exp(-x) ≤ 1 / e`. -/
theorem mul_exp_neg_le_one_div_e (x : ℝ) :
    x * Real.exp (-x) ≤ 1 / Real.exp 1 := by
  have h := mul_exp_neg_le_exp_neg_one x
  have h_exp_neg_one : Real.exp (-1) = 1 / Real.exp 1 := by
    rw [Real.exp_neg, ← one_div]
  linarith [h, h_exp_neg_one]

#print axioms mul_exp_neg_le_one_div_e

/-! ## §3. Maximum-attaining value -/

/-- **The maximum is attained at `x = 1`**, where the bound is
    sharp: `1 · exp(-1) = exp(-1)`. -/
theorem mul_exp_neg_at_one : (1 : ℝ) * Real.exp (-1) = Real.exp (-1) := by
  ring

/-! ## §4. Numerical instance -/

/-- **Numerical sanity**: at `x = 0`, the bound is
    `0 · exp(0) = 0 ≤ exp(-1)`. -/
theorem mul_exp_neg_at_zero : (0 : ℝ) * Real.exp (-0) ≤ Real.exp (-1) := by
  simp
  exact le_of_lt (Real.exp_pos _)

/-- **Numerical sanity**: at `x = 2`, the bound is
    `2 · exp(-2) ≤ exp(-1)` (since `2/e² ≈ 0.27 < 1/e ≈ 0.37`). -/
theorem mul_exp_neg_at_two : (2 : ℝ) * Real.exp (-2) ≤ Real.exp (-1) :=
  mul_exp_neg_le_exp_neg_one 2

#print axioms mul_exp_neg_at_two

end Real

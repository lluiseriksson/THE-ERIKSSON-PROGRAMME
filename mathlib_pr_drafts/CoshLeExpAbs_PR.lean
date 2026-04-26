/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# `cosh(x) ≤ exp(|x|)` and companion hyperbolic bounds

This module proves the elementary bound

  `Real.cosh x ≤ Real.exp |x|` for all real `x`,

with equality only at `x = 0`. This is a foundational bound used
throughout:

* probability theory (sub-Gaussian tail estimates, Hoeffding-type
  bounds, moment generating function calculations);
* real analysis (asymptotic estimates of hyperbolic integrals);
* statistical mechanics (partition function bounds for systems with
  symmetric interactions).

While Mathlib has the constituents (`Real.cosh`, `Real.exp`, sign
analysis), the explicit packaged statement `cosh(x) ≤ exp(|x|)` is
not in the library.

## Strategy

`cosh(x) = (exp(x) + exp(-x))/2`, and the larger of `exp(x)` and
`exp(-x)` is `exp(|x|)`. The mean of two non-negative numbers is at
most their max. Combined: `cosh(x) ≤ max(exp(x), exp(-x)) = exp(|x|)`.

Concretely, by case analysis on the sign of `x`:

* If `x ≥ 0`: `|x| = x`, `exp(-x) ≤ exp(x)`, so
  `cosh(x) = (exp(x) + exp(-x))/2 ≤ exp(x) = exp(|x|)`.
* If `x < 0`: `|x| = -x`, `exp(x) ≤ exp(-x)`, so
  `cosh(x) ≤ exp(-x) = exp(|x|)`.

## PR submission notes

Self-contained file using `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`
(for `Real.cosh` definition and `Real.cosh_eq`).

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proof is a 4-line case analysis with `linarith` /
`Real.exp_le_exp.mpr`.
-/

namespace Real

/-! ## §1. The main bound -/

/-- **`Real.cosh_le_exp_abs`**: for all real `x`,
    `cosh x ≤ exp |x|`.

    Equality holds iff `x = 0`. -/
theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  rcases le_or_lt 0 x with hx | hx
  · -- Case x ≥ 0: |x| = x, exp(-x) ≤ exp(x).
    rw [abs_of_nonneg hx]
    have h_le : Real.exp (-x) ≤ Real.exp x :=
      Real.exp_le_exp.mpr (by linarith)
    linarith [Real.exp_pos x]
  · -- Case x < 0: |x| = -x, exp(x) ≤ exp(-x).
    rw [abs_of_neg hx]
    have h_le : Real.exp x ≤ Real.exp (-x) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith [Real.exp_pos (-x)]

#print axioms cosh_le_exp_abs

/-! ## §2. Companion bounds -/

/-- **`Real.cosh_le_exp_of_nonneg`**: for `x ≥ 0`, `cosh(x) ≤ exp(x)`. -/
theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x ≤ Real.exp x := by
  have h := cosh_le_exp_abs x
  rw [abs_of_nonneg hx] at h
  exact h

#print axioms cosh_le_exp_of_nonneg

/-- **`Real.exp_neg_abs_le_cosh`**: for all real `x`,
    `exp(-|x|) ≤ cosh(x)`. The dual lower bound. -/
theorem exp_neg_abs_le_cosh (x : ℝ) : Real.exp (-|x|) ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  rcases le_or_lt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have h_le : Real.exp (-x) ≤ Real.exp x :=
      Real.exp_le_exp.mpr (by linarith)
    linarith [Real.exp_pos x]
  · rw [abs_of_neg hx]
    have h_le : Real.exp x ≤ Real.exp (-x) :=
      Real.exp_le_exp.mpr (by linarith)
    have h_neg_neg : -(-x) = x := by ring
    rw [h_neg_neg]
    linarith [Real.exp_pos x]

#print axioms exp_neg_abs_le_cosh

/-! ## §3. Sandwich packaging -/

/-- **`Real.cosh_sandwich`**: `exp(-|x|) ≤ cosh(x) ≤ exp(|x|)` for all
    real `x`. Both inequalities are sharp (equality only at `x = 0`). -/
theorem cosh_sandwich (x : ℝ) :
    Real.exp (-|x|) ≤ Real.cosh x ∧ Real.cosh x ≤ Real.exp |x| :=
  ⟨exp_neg_abs_le_cosh x, cosh_le_exp_abs x⟩

#print axioms cosh_sandwich

/-! ## §4. Numerical sanity check -/

/-- **At `x = 0`**: `cosh(0) = 1 ≤ exp(0) = 1` (equality case). -/
theorem cosh_zero_le_exp_zero : Real.cosh 0 ≤ Real.exp |(0 : ℝ)| := by
  simp [Real.cosh_zero, Real.exp_zero]

/-- **At `x = 1`**: `cosh(1) ≤ exp(1) = e`. -/
theorem cosh_one_le_exp_one : Real.cosh 1 ≤ Real.exp 1 := by
  have h := cosh_le_exp_abs 1
  rwa [show |(1 : ℝ)| = 1 from abs_one] at h

#print axioms cosh_one_le_exp_one

end Real

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Generalized tangent line bound for `exp`

This module proves the **tangent line bound** for `Real.exp` at an
arbitrary base point `a`:

  `exp(a) + exp(a) · (x - a) ≤ exp(x)` for all `a, x : ℝ`.

This generalizes `Real.add_one_le_exp` (which is the case `a = 0`)
to any base point and is the explicit packaged statement of the
fundamental fact that `exp` is convex (its graph lies above every
tangent line).

While Mathlib has convexity (`convexOn_exp`) and the `a = 0` case,
the explicit packaged form `exp a + exp a · (x - a) ≤ exp x` is
useful directly in:

* numerical analysis (Newton-method residual bounds at any base);
* probability (sub-exponential and Bernstein-type tail bounds at
  arbitrary base points);
* statistical mechanics (free-energy expansions around any
  reference state).

## Strategy

One-line reduction to `Real.add_one_le_exp` via the identity
`exp x = exp a · exp(x - a)`:

  `exp x = exp a · exp(x - a) ≥ exp a · (1 + (x - a))`
        `= exp a + exp a · (x - a)`.

The first inequality is `add_one_le_exp (x - a)` multiplied by
`exp a > 0`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Exp`.
Suitable for direct addition to Mathlib's `Real.exp` library.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proof composes one application of `add_one_le_exp`
with `mul_le_mul_of_nonneg_left` and `exp_add`.
-/

namespace Real

/-! ## §1. The generalized tangent line bound -/

/-- **`Real.exp_ge_tangent_at`**: for all `a, x : ℝ`,

      `exp(a) + exp(a) · (x - a) ≤ exp(x)`.

    This is the **tangent line bound** for `exp` at the point `a`,
    generalizing `Real.add_one_le_exp` (which is the case `a = 0`). -/
theorem exp_ge_tangent_at (a x : ℝ) :
    Real.exp a + Real.exp a * (x - a) ≤ Real.exp x := by
  -- Step 1: 1 + (x - a) ≤ exp(x - a).
  have h_step : 1 + (x - a) ≤ Real.exp (x - a) := Real.add_one_le_exp _
  -- Step 2: multiply by exp(a) > 0.
  have h_exp_a_pos : (0 : ℝ) ≤ Real.exp a := le_of_lt (Real.exp_pos a)
  have h_mul : Real.exp a * (1 + (x - a)) ≤ Real.exp a * Real.exp (x - a) :=
    mul_le_mul_of_nonneg_left h_step h_exp_a_pos
  -- Step 3: exp(a) · exp(x - a) = exp(a + (x - a)) = exp(x).
  have h_exp_combine : Real.exp a * Real.exp (x - a) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1; ring
  -- Step 4: exp(a) · (1 + (x - a)) = exp(a) + exp(a) · (x - a).
  have h_lhs : Real.exp a * (1 + (x - a)) = Real.exp a + Real.exp a * (x - a) := by
    ring
  linarith [h_mul, h_exp_combine, h_lhs]

#print axioms exp_ge_tangent_at

/-! ## §2. Strict variant -/

/-- **Strict variant** at `x ≠ a`:
    `exp(a) + exp(a) · (x - a) < exp(x)`. -/
theorem exp_gt_tangent_at_of_ne (a x : ℝ) (hxa : x ≠ a) :
    Real.exp a + Real.exp a * (x - a) < Real.exp x := by
  have h_diff_ne : x - a ≠ 0 := sub_ne_zero.mpr hxa
  have h_step : 1 + (x - a) < Real.exp (x - a) := by
    have := Real.add_one_lt_exp h_diff_ne
    linarith
  have h_exp_a_pos : (0 : ℝ) < Real.exp a := Real.exp_pos a
  have h_mul : Real.exp a * (1 + (x - a)) < Real.exp a * Real.exp (x - a) :=
    mul_lt_mul_of_pos_left h_step h_exp_a_pos
  have h_exp_combine : Real.exp a * Real.exp (x - a) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1; ring
  have h_lhs : Real.exp a * (1 + (x - a)) = Real.exp a + Real.exp a * (x - a) := by
    ring
  linarith [h_mul, h_exp_combine, h_lhs]

#print axioms exp_gt_tangent_at_of_ne

/-! ## §3. Equivalent reformulation: secant ≥ tangent -/

/-- **Secant-tangent reformulation**:
    `(exp(x) - exp(a)) ≥ exp(a) · (x - a)` for all `a, x : ℝ`. -/
theorem exp_sub_exp_ge_exp_mul_sub (a x : ℝ) :
    Real.exp a * (x - a) ≤ Real.exp x - Real.exp a := by
  have h := exp_ge_tangent_at a x
  linarith

#print axioms exp_sub_exp_ge_exp_mul_sub

/-! ## §4. Specializations: `a = 0` recovers `add_one_le_exp` -/

/-- **`a = 0` specialization**: recovers `Real.add_one_le_exp`. -/
theorem exp_ge_tangent_at_zero (x : ℝ) :
    1 + x ≤ Real.exp x := by
  have h := exp_ge_tangent_at 0 x
  simp at h
  linarith [h, show Real.exp 0 = 1 from Real.exp_zero]

/-- **`a = 1` specialization**: `e + e·(x-1) ≤ exp(x)` for all `x`. -/
theorem exp_ge_tangent_at_one (x : ℝ) :
    Real.exp 1 + Real.exp 1 * (x - 1) ≤ Real.exp x :=
  exp_ge_tangent_at 1 x

#print axioms exp_ge_tangent_at_one

end Real

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Two-sided MVT bounds for `exp` on an interval

This module proves the **explicit two-sided mean-value bounds** for
`Real.exp` on an interval `[a, b]`:

  `(b - a) · exp(a) ≤ exp(b) - exp(a) ≤ (b - a) · exp(b)`,

valid for all `a ≤ b`. Both inequalities are sharp at `a = b`.

This is the elementary analogue of the standard MVT statement
`exp(b) - exp(a) = (b - a) · exp(c)` for some `c ∈ [a, b]` — we
upper- and lower-bound by replacing `c` with the endpoints.

The bound is foundational in:

* numerical analysis (error estimates for `exp` Taylor truncations);
* probability (Chernoff-style tail bound expansions);
* statistical mechanics (free-energy increments).

While Mathlib has convexity / `StrictConvexOn.gradient_lt` machinery
that implies these, the explicit packaged form is not in the library.

## Strategy

Both bounds follow directly from the **tangent-line bound**
`Real.exp_ge_tangent_at` (companion file `ExpTangentLineBound_PR.lean`,
or directly from `Real.add_one_le_exp` with a translation):

* **Lower bound**: tangent line at `a` gives
  `exp(b) ≥ exp(a) + exp(a)·(b - a)`, so
  `exp(b) - exp(a) ≥ exp(a)·(b - a)`.

* **Upper bound**: tangent line at `b` gives
  `exp(a) ≥ exp(b) + exp(b)·(a - b) = exp(b) - exp(b)·(b - a)`,
  so `exp(b) - exp(a) ≤ exp(b)·(b - a)`.

In each case the tangent-line bound is `Real.add_one_le_exp` applied
to the difference, multiplied by the appropriate `exp` of the base point.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Exp`.
Suitable for direct addition to Mathlib's `Real.exp` library, paired
with `ExpTangentLineBound_PR.lean` as a "convexity" submission set.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Both proofs are 4-line tactic blocks composing
`Real.add_one_le_exp` with `mul_le_mul_of_nonneg_left` and `Real.exp_add`.
-/

namespace Real

/-! ## §1. Lower MVT bound -/

/-- **`Real.exp_sub_exp_ge_mul_exp_left`**: for `a ≤ b`,

      `(b - a) · exp(a) ≤ exp(b) - exp(a)`.

    The lower MVT bound: replacing the unknown `c ∈ [a, b]` with the
    left endpoint `a` underestimates. Sharp at `a = b`. -/
theorem exp_sub_exp_ge_mul_exp_left {a b : ℝ} (hab : a ≤ b) :
    (b - a) * Real.exp a ≤ Real.exp b - Real.exp a := by
  -- Step 1: 1 + (b - a) ≤ exp(b - a).
  have h_step : 1 + (b - a) ≤ Real.exp (b - a) := Real.add_one_le_exp _
  -- Step 2: multiply by exp a > 0.
  have h_exp_a_pos : (0 : ℝ) ≤ Real.exp a := le_of_lt (Real.exp_pos a)
  have h_mul : Real.exp a * (1 + (b - a)) ≤ Real.exp a * Real.exp (b - a) :=
    mul_le_mul_of_nonneg_left h_step h_exp_a_pos
  -- Step 3: exp a · exp(b-a) = exp b.
  have h_exp_combine : Real.exp a * Real.exp (b - a) = Real.exp b := by
    rw [← Real.exp_add]; congr 1; ring
  -- Step 4: exp a · (1 + (b-a)) = exp a + (b-a)·exp a.
  have h_lhs : Real.exp a * (1 + (b - a)) = Real.exp a + (b - a) * Real.exp a := by
    ring
  linarith [h_mul, h_exp_combine, h_lhs]

#print axioms exp_sub_exp_ge_mul_exp_left

/-! ## §2. Upper MVT bound -/

/-- **`Real.exp_sub_exp_le_mul_exp_right`**: for `a ≤ b`,

      `exp(b) - exp(a) ≤ (b - a) · exp(b)`.

    The upper MVT bound: replacing the unknown `c ∈ [a, b]` with the
    right endpoint `b` overestimates. Sharp at `a = b`. -/
theorem exp_sub_exp_le_mul_exp_right {a b : ℝ} (hab : a ≤ b) :
    Real.exp b - Real.exp a ≤ (b - a) * Real.exp b := by
  -- Apply add_one_le_exp at -(b-a) = a-b ≤ 0:
  -- 1 + (a - b) ≤ exp(a - b).
  have h_step : 1 + (a - b) ≤ Real.exp (a - b) := Real.add_one_le_exp _
  have h_exp_b_pos : (0 : ℝ) ≤ Real.exp b := le_of_lt (Real.exp_pos b)
  have h_mul : Real.exp b * (1 + (a - b)) ≤ Real.exp b * Real.exp (a - b) :=
    mul_le_mul_of_nonneg_left h_step h_exp_b_pos
  -- exp b · exp(a-b) = exp a.
  have h_exp_combine : Real.exp b * Real.exp (a - b) = Real.exp a := by
    rw [← Real.exp_add]; congr 1; ring
  -- exp b · (1 + (a-b)) = exp b + (a-b)·exp b = exp b - (b-a)·exp b.
  have h_lhs : Real.exp b * (1 + (a - b)) = Real.exp b - (b - a) * Real.exp b := by
    ring
  linarith [h_mul, h_exp_combine, h_lhs]

#print axioms exp_sub_exp_le_mul_exp_right

/-! ## §3. Two-sided sandwich -/

/-- **Two-sided MVT bounds** packaged together. -/
theorem exp_sub_exp_mvt_sandwich {a b : ℝ} (hab : a ≤ b) :
    (b - a) * Real.exp a ≤ Real.exp b - Real.exp a ∧
    Real.exp b - Real.exp a ≤ (b - a) * Real.exp b :=
  ⟨exp_sub_exp_ge_mul_exp_left hab, exp_sub_exp_le_mul_exp_right hab⟩

#print axioms exp_sub_exp_mvt_sandwich

/-! ## §4. Symmetric bound for general `a, b` -/

/-- **Symmetric absolute-value form**: for any `a, b : ℝ`,

      `|exp(b) - exp(a)| ≤ |b - a| · max(exp(a), exp(b))`.

    This is independent of whether `a ≤ b` or `b ≤ a`. -/
theorem abs_exp_sub_exp_le_abs_mul_max (a b : ℝ) :
    |Real.exp b - Real.exp a| ≤ |b - a| * max (Real.exp a) (Real.exp b) := by
  rcases le_or_lt a b with hab | hab
  · -- Case a ≤ b: exp a ≤ exp b, so max = exp b.
    have h_exp_le : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
    have h_max : max (Real.exp a) (Real.exp b) = Real.exp b := max_eq_right h_exp_le
    have h_abs_b_a : |b - a| = b - a := abs_of_nonneg (by linarith)
    have h_abs_diff : |Real.exp b - Real.exp a| = Real.exp b - Real.exp a :=
      abs_of_nonneg (by linarith)
    rw [h_max, h_abs_b_a, h_abs_diff]
    exact exp_sub_exp_le_mul_exp_right hab
  · -- Case b < a: symmetric.
    have h_ba : b ≤ a := le_of_lt hab
    have h_exp_le : Real.exp b ≤ Real.exp a := Real.exp_le_exp.mpr h_ba
    have h_max : max (Real.exp a) (Real.exp b) = Real.exp a := max_eq_left h_exp_le
    have h_abs_b_a : |b - a| = a - b := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    have h_abs_diff : |Real.exp b - Real.exp a| = Real.exp a - Real.exp b := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [h_max, h_abs_b_a, h_abs_diff]
    exact exp_sub_exp_le_mul_exp_right h_ba

#print axioms abs_exp_sub_exp_le_abs_mul_max

/-! ## §5. Numerical sanity check -/

/-- **At `a = 0, b = 1`**: `1·1 ≤ e - 1 ≤ 1·e`. The lower part says
    `e ≥ 2`; the upper says `e ≥ e - 1` (trivial; sharp upper). -/
theorem exp_one_ge_two_via_mvt :
    (1 - 0 : ℝ) * Real.exp 0 ≤ Real.exp 1 - Real.exp 0 := by
  exact exp_sub_exp_ge_mul_exp_left (show (0:ℝ) ≤ 1 by norm_num)

#print axioms exp_one_ge_two_via_mvt

end Real

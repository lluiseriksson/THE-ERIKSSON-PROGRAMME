/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Two-sided MVT bounds for `log` on an interval

This module proves the **explicit two-sided mean-value bounds** for
`Real.log` on an interval `[x, y]` with `0 < x ≤ y`:

  `(y - x) / y ≤ log(y) - log(x) ≤ (y - x) / x`,

with equality on both sides at `x = y`.

This is the elementary analogue of the standard MVT statement
`log(y) - log(x) = (y - x) / c` for some `c ∈ [x, y]` — we upper-
and lower-bound by replacing `c` with the endpoints (the derivative
`1/c` is monotone-decreasing, so `1/y ≤ 1/c ≤ 1/x`).

This is the **dual companion** of `ExpMVTBounds_PR.lean`, which gives
two-sided bounds for `exp`.

The bound is foundational in:

* numerical analysis (logarithmic interpolation error bounds);
* probability (KL-divergence bounds, log-sum inequalities);
* statistical mechanics (free-energy expansions, entropy bounds).

Mathlib has the constituent `Real.log_le_sub_one_of_pos` and the
dual `Real.one_sub_inv_le_log` (companion file `OneSubInvLeLog_PR.lean`),
but the explicit packaged MVT form is not in the library.

## Strategy

Both bounds reduce to existing one-sided bounds via the substitution
`log(y) - log(x) = log(y/x)`:

* **Upper**: `log(y/x) ≤ y/x - 1 = (y - x)/x` from
  `Real.log_le_sub_one_of_pos`.
* **Lower**: `log(y/x) ≥ 1 - x/y = (y - x)/y` from
  `Real.one_sub_inv_le_log` (companion file).

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
Suitable for direct addition to Mathlib's `Real.log` library, paired
with `ExpMVTBounds_PR.lean` and `OneSubInvLeLog_PR.lean`.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Both proofs are 3-4 line tactic blocks.
-/

namespace Real

/-! ## §1. Upper MVT bound -/

/-- **`Real.log_sub_log_le_div_left`**: for `0 < x` and `0 < y`,

      `log(y) - log(x) ≤ (y - x) / x`.

    The upper MVT bound: replacing `c ∈ [x, y]` with the smaller
    endpoint `x` in the formula `1/c · (y - x)` gives an overestimate. -/
theorem log_sub_log_le_div_left {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y - Real.log x ≤ (y - x) / x := by
  -- log y - log x = log(y/x).
  rw [← Real.log_div (ne_of_gt hy) (ne_of_gt hx)]
  -- log(y/x) ≤ y/x - 1.
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  -- y/x - 1 = (y - x)/x.
  have h_simp : y / x - 1 = (y - x) / x := by field_simp
  linarith

#print axioms log_sub_log_le_div_left

/-! ## §2. Lower MVT bound -/

/-- **`Real.log_sub_log_ge_div_right`**: for `0 < x` and `0 < y`,

      `(y - x) / y ≤ log(y) - log(x)`.

    The lower MVT bound: replacing `c ∈ [x, y]` with the larger
    endpoint `y` in the formula `1/c · (y - x)` gives an underestimate. -/
theorem log_sub_log_ge_div_right {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y - x) / y ≤ Real.log y - Real.log x := by
  -- log y - log x = log(y/x).
  rw [← Real.log_div (ne_of_gt hy) (ne_of_gt hx)]
  -- log(y/x) ≥ 1 - x/y (this is `one_sub_inv_le_log` at y/x).
  -- Equivalently: 1 - 1/(y/x) ≤ log(y/x), i.e., 1 - x/y ≤ log(y/x).
  have h_inv_pos : (0 : ℝ) < x/y := div_pos hx hy
  have h := Real.log_le_sub_one_of_pos h_inv_pos
  -- h : log(x/y) ≤ x/y - 1.
  -- log(y/x) = -log(x/y), so log(y/x) ≥ 1 - x/y = (y - x)/y.
  have h_log_neg : Real.log (x/y) = -Real.log (y/x) := by
    rw [show (x : ℝ)/y = (y/x)⁻¹ from by field_simp, Real.log_inv]
  -- Combine: -log(y/x) ≤ x/y - 1, i.e., log(y/x) ≥ 1 - x/y.
  have h_simp : 1 - x / y = (y - x) / y := by field_simp
  linarith [h_log_neg ▸ h]

#print axioms log_sub_log_ge_div_right

/-! ## §3. Two-sided sandwich -/

/-- **`Real.log_sub_log_mvt_sandwich`**: two-sided MVT bounds for log,
    packaged together. -/
theorem log_sub_log_mvt_sandwich {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y - x) / y ≤ Real.log y - Real.log x ∧
    Real.log y - Real.log x ≤ (y - x) / x :=
  ⟨log_sub_log_ge_div_right hx hy, log_sub_log_le_div_left hx hy⟩

#print axioms log_sub_log_mvt_sandwich

/-! ## §4. Numerical instance -/

/-- **At `x = 1, y = 2`**: `1/2 ≤ log 2 - log 1 = log 2 ≤ 1`. -/
theorem log_two_in_half_one : (1/2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  have h := log_sub_log_mvt_sandwich
    (show (0:ℝ) < 1 by norm_num) (show (0:ℝ) < 2 by norm_num)
  rw [Real.log_one] at h
  obtain ⟨h_lo, h_hi⟩ := h
  refine ⟨?_, ?_⟩
  · -- (2 - 1)/2 = 1/2 ≤ log 2 - 0 = log 2.
    have h_simp : (2 - 1 : ℝ) / 2 = 1/2 := by norm_num
    linarith
  · -- log 2 - 0 = log 2 ≤ (2 - 1)/1 = 1.
    have h_simp : (2 - 1 : ℝ) / 1 = 1 := by norm_num
    linarith

#print axioms log_two_in_half_one

end Real

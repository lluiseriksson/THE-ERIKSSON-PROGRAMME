/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Universal Bernoulli-type bound `(1 + x)^n ≤ exp(n · x)`

This module proves the universal bound

  `(1 + x)^n ≤ exp(n · x)` for all `x ≥ -1` and `n : ℕ`,

which **generalizes Bernoulli's inequality** (`1 + n·x ≤ (1+x)^n`
for `x ≥ 0` or `x ≥ -1`) by replacing the linear lower bound with an
exponential upper bound.

The bound is sharp at `x = 0` (both sides equal 1) and reflects the
fact that `(1 + x/n)^n → exp(x)` from below.

## Strategy

Combine three Mathlib facts:

1. `Real.add_one_le_exp x`: `1 + x ≤ exp x` for all real `x`.
2. `pow_le_pow_left h_one_add_nn h_step n`: monotonicity of
   `· ^ n` on nonneg reals (requires `0 ≤ 1 + x`, i.e. `x ≥ -1`).
3. `Real.exp_nat_mul`: `(exp y)^n = exp(n · y)`.

Composition: `(1+x)^n ≤ (exp x)^n = exp(n·x)`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Exp`.
Suitable for direct addition to Mathlib.

The lemma is dual to `Real.one_add_div_pow_le_exp` (companion file
`OneAddDivPowLeExp_PR.lean`): there `n` is the exponent for the limit,
here `n · x` plays the role of the exponential argument.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proof composes three small steps via `calc`.
-/

namespace Real

/-! ## §1. The main bound -/

/-- **`Real.one_add_pow_le_exp_mul`**: for `x : ℝ` with `x ≥ -1`
    and any `n : ℕ`,

      `(1 + x)^n ≤ exp(n · x)`.

    Generalizes Bernoulli's inequality with an exponential upper
    bound. Sharp at `x = 0`. -/
theorem one_add_pow_le_exp_mul (n : ℕ) {x : ℝ} (hx : -1 ≤ x) :
    (1 + x) ^ n ≤ Real.exp ((n : ℝ) * x) := by
  -- Step 1: 1 + x ≤ exp x.
  have h_step : 1 + x ≤ Real.exp x := Real.add_one_le_exp x
  -- Step 1b: 1 + x is nonneg.
  have h_one_add_nn : (0 : ℝ) ≤ 1 + x := by linarith
  -- Step 2: raise to nth power.
  have h_pow : (1 + x) ^ n ≤ (Real.exp x) ^ n :=
    pow_le_pow_left h_one_add_nn h_step n
  -- Step 3: rewrite (exp x)^n = exp(n · x).
  rw [← Real.exp_nat_mul] at h_pow
  exact h_pow

#print axioms one_add_pow_le_exp_mul

/-! ## §2. Symmetric companion: `(1 - x)^n ≤ exp(-n · x)` -/

/-- **`Real.one_sub_pow_le_exp_neg_mul`**: for `x : ℝ` with `x ≤ 1`
    and any `n : ℕ`, `(1 - x)^n ≤ exp(-n · x)`.

    Direct corollary of `one_add_pow_le_exp_mul` applied to `-x`. -/
theorem one_sub_pow_le_exp_neg_mul (n : ℕ) {x : ℝ} (hx : x ≤ 1) :
    (1 - x) ^ n ≤ Real.exp (-((n : ℝ) * x)) := by
  have h := one_add_pow_le_exp_mul n (show -1 ≤ -x by linarith)
  -- (1 + (-x))^n = (1 - x)^n.
  have h_rw : 1 + (-x) = 1 - x := by ring
  -- (n : ℝ) · (-x) = -(n · x).
  have h_rw2 : ((n : ℝ) * (-x)) = -((n : ℝ) * x) := by ring
  rw [h_rw] at h
  rw [h_rw2] at h
  exact h

#print axioms one_sub_pow_le_exp_neg_mul

/-! ## §3. Reformulation as `(1 + y/n)^n ≤ exp(y)` -/

/-- **Reformulation**: substituting `x := y/n` recovers
    `(1 + y/n)^n ≤ exp(y)` (companion result in
    `OneAddDivPowLeExp_PR.lean`).

    This shows the two formulations are equivalent. -/
theorem one_add_div_pow_le_exp_via_pow_mul
    (n : ℕ) {y : ℝ} (hy : -((n : ℝ)) ≤ y) :
    (1 + y / (n : ℝ)) ^ n ≤ Real.exp y := by
  by_cases hn : n = 0
  · subst hn; simp
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  -- Apply main lemma at x := y/n; need y/n ≥ -1.
  have h_x_ge : -1 ≤ y / (n : ℝ) := by
    rw [le_div_iff₀ h_n_pos]
    linarith
  have h := one_add_pow_le_exp_mul n h_x_ge
  -- (n : ℝ) · (y/n) = y.
  have h_simp : (n : ℝ) * (y / (n : ℝ)) = y := by
    field_simp
  rw [h_simp] at h
  exact h

#print axioms one_add_div_pow_le_exp_via_pow_mul

/-! ## §4. Numerical instances -/

/-- **At `x = 1, n = 0`**: `(1 + 1)^0 = 1 ≤ exp(0) = 1`. -/
theorem one_add_pow_zero : ((1 : ℝ) + 1)^0 ≤ Real.exp ((0 : ℕ) * 1) := by
  simpa using one_add_pow_le_exp_mul 0 (show -1 ≤ (1 : ℝ) by norm_num)

/-- **At `x = 1, n = 1`**: `2 ≤ e` (matches `e > 2`). -/
theorem two_le_exp_one_via_pow :
    ((1 : ℝ) + 1)^1 ≤ Real.exp ((1 : ℕ) * 1) := by
  simpa using one_add_pow_le_exp_mul 1 (show -1 ≤ (1 : ℝ) by norm_num)

#print axioms two_le_exp_one_via_pow

end Real

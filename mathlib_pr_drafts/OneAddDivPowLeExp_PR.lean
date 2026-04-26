/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `(1 + x/n)^n ≤ exp(x)` for `x ≥ 0`

This module proves the classical inequality

  `(1 + x/n)^n ≤ exp(x)` for all `n : ℕ` and `x : ℝ` with `x ≥ 0`,

which is the **elementwise (non-asymptotic) form** of the standard
limit `lim_{n→∞} (1 + x/n)^n = exp(x)`.

Mathlib has the limit (`Real.tendsto_one_plus_div_pow_exp`) but does
not appear to have the inequality form, which is independently
useful for:

* numerical analysis (error bounds for compound interest /
  exponential approximation);
* probability (Poisson approximation of binomial distribution);
* stochastic analysis (discrete-to-continuous comparison estimates).

## Strategy

The proof is a direct three-step application of `Real.add_one_le_exp`:

1. `1 + x/n ≤ exp(x/n)` (this is `Real.add_one_le_exp (x/n)`).
2. Both sides nonneg, raise to the `n`th power:
   `(1 + x/n)^n ≤ (exp(x/n))^n`.
3. Simplify the RHS via `Real.exp_nat_mul`:
   `(exp(x/n))^n = exp(n · (x/n)) = exp x`.

## PR submission notes

Self-contained file using only `Mathlib.Analysis.SpecialFunctions.Exp`.
Suitable for direct addition to Mathlib.

**Status (2026-04-25)**: produced in workspace, not yet built with
`lake build`. Proof is short (3 small steps composed via `calc`).
-/

namespace Real

/-! ## §1. The main bound -/

/-- **`Real.one_add_div_pow_le_exp`**: for `n : ℕ` and `x : ℝ` with
    `x ≥ 0`,

      `(1 + x/n)^n ≤ exp x`.

    This is the elementwise form of the limit
    `(1 + x/n)^n → exp x` as `n → ∞`. -/
theorem one_add_div_pow_le_exp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x / n) ^ n ≤ Real.exp x := by
  by_cases hn : n = 0
  · -- n = 0: LHS = 1 ≤ exp(x) since x ≥ 0.
    subst hn
    simp
    exact Real.one_le_exp hx
  -- n ≥ 1: main argument.
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  -- Step 1: 1 + x/n ≤ exp(x/n).
  have h_one_step : 1 + x / (n : ℝ) ≤ Real.exp (x / (n : ℝ)) :=
    Real.add_one_le_exp _
  -- Step 1b: 1 + x/n is nonneg (needed to raise to nth power).
  have h_one_add_nn : (0 : ℝ) ≤ 1 + x / (n : ℝ) := by
    have h_div_nn : (0 : ℝ) ≤ x / (n : ℝ) := div_nonneg hx (le_of_lt h_n_pos)
    linarith
  -- Step 2: raise both sides to the nth power.
  have h_pow : (1 + x / (n : ℝ)) ^ n ≤ (Real.exp (x / (n : ℝ))) ^ n :=
    pow_le_pow_left h_one_add_nn h_one_step n
  -- Step 3: rewrite (exp(x/n))^n = exp(n · (x/n)) = exp x.
  have h_exp_pow : (Real.exp (x / (n : ℝ))) ^ n = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  linarith

#print axioms one_add_div_pow_le_exp

/-! ## §2. Symmetric companion: `(1 - x/n)^n ≤ exp(-x)` -/

/-- **`Real.one_sub_div_pow_le_exp_neg`**: for `n : ℕ` with `n ≥ 1`
    and `x : ℝ` with `0 ≤ x ≤ n`,

      `(1 - x/n)^n ≤ exp(-x)`.

    This is the symmetric companion to `one_add_div_pow_le_exp`. -/
theorem one_sub_div_pow_le_exp_neg
    (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) (hx_le : x ≤ (n : ℝ)) :
    (1 - x / (n : ℝ)) ^ n ≤ Real.exp (-x) := by
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- 1 - x/n ≤ exp(-x/n) from Real.add_one_le_exp (-x/n).
  have h_one_step : 1 - x / (n : ℝ) ≤ Real.exp (-(x / (n : ℝ))) := by
    have := Real.add_one_le_exp (-(x / (n : ℝ)))
    linarith
  -- 1 - x/n is nonneg from x ≤ n.
  have h_one_sub_nn : (0 : ℝ) ≤ 1 - x / (n : ℝ) := by
    have h_div_le : x / (n : ℝ) ≤ 1 := by
      rw [div_le_one h_n_pos]
      exact hx_le
    linarith
  -- Raise to nth power and simplify.
  have h_pow : (1 - x / (n : ℝ)) ^ n ≤ (Real.exp (-(x / (n : ℝ)))) ^ n :=
    pow_le_pow_left h_one_sub_nn h_one_step n
  have h_exp_pow : (Real.exp (-(x / (n : ℝ)))) ^ n = Real.exp (-x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  linarith

#print axioms one_sub_div_pow_le_exp_neg

/-! ## §3. Numerical instance: compound-interest sanity check -/

/-- **At `n = 2, x = 1`**: `(1 + 1/2)^2 = 9/4 = 2.25 ≤ e ≈ 2.718`. -/
theorem compound_two_at_one : ((1 : ℝ) + 1/2) ^ 2 ≤ Real.exp 1 := by
  have := one_add_div_pow_le_exp 2 (show (0:ℝ) ≤ 1 by norm_num)
  simpa using this

#print axioms compound_two_at_one

/-- **At `n = 12, x = 1`**: monthly compounding bound. -/
theorem compound_twelve_at_one : ((1 : ℝ) + 1/12) ^ 12 ≤ Real.exp 1 := by
  have := one_add_div_pow_le_exp 12 (show (0:ℝ) ≤ 1 by norm_num)
  simpa using this

end Real

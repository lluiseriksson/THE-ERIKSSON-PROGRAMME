/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Complex.Exponential

/-!
# Absorbing local domain-cardinality costs into exponential decay

The literal CMP116 small-field cutoff is stated in a source sup norm,
whereas the radial Taylor residual is estimated in `L²`.  Restricting to one
localization domain costs the square root of its physical bond cardinality.
After cubing, this leaves a factor proportional to `|Y|^(3/2)`.

This module absorbs that polynomial factor into the already available
cardinality decay without optimizing constants.  The resulting constant is
uniform in the domain and the independent tree-metric exponential is left
untouched.

No identification between the source scale `Msource` in equations (1.36) or
(1.43) and the block scale `M` of a `CMP116LocalizationDomain` is asserted
here.  That remains a source-facing dictionary obligation.

Oracle target: no nonstandard axioms. No placeholders or local axioms.
-/

namespace YangMills.RG

noncomputable section

/-- A deliberately nonoptimal but elementary absorption of the cubic
square-root cardinality cost. -/
theorem sqrt_nat_pow_three_mul_exp_neg_le
    (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Real.sqrt (n : ℝ) ^ 3 * Real.exp (-(κ * (n : ℝ))) ≤
      2 / κ ^ 2 := by
  by_cases hn : n = 0
  · simp [hn]
    positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt hn0, Real.sqrt_nonneg (n : ℝ)]
  have hpow :
      Real.sqrt (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 := by
    calc
      Real.sqrt (n : ℝ) ^ 3 =
          Real.sqrt (n : ℝ) * (n : ℝ) := by
        rw [show Real.sqrt (n : ℝ) ^ 3 =
          Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) ^ 2 by ring,
          Real.sq_sqrt hn0]
      _ ≤ (n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt_le hn0
      _ = (n : ℝ) ^ 2 := by ring
  let x := κ * (n : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hexp : x ^ 2 / 2 ≤ Real.exp x := by
    simpa using Real.pow_div_factorial_le_exp x hx0 2
  have hxweighted : x ^ 2 / 2 * Real.exp (-x) ≤ 1 := by
    calc
      x ^ 2 / 2 * Real.exp (-x) ≤
          Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  have hpre :
      Real.sqrt (n : ℝ) ^ 3 * Real.exp (-x) ≤
        (n : ℝ) ^ 2 * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
  apply (le_div_iff₀ (sq_pos_of_pos hκ)).2
  calc
    Real.sqrt (n : ℝ) ^ 3 * Real.exp (-(κ * (n : ℝ))) *
          κ ^ 2 =
        (Real.sqrt (n : ℝ) ^ 3 * Real.exp (-x)) * κ ^ 2 := by
      rfl
    _ ≤ ((n : ℝ) ^ 2 * Real.exp (-x)) * κ ^ 2 :=
      mul_le_mul_of_nonneg_right hpre (sq_nonneg κ)
    _ = 2 * (x ^ 2 / 2 * Real.exp (-x)) := by
      dsimp [x]
      ring
    _ ≤ 2 := by nlinarith

/-- Exact extraction of the four-dimensional source-bond cardinality
constant before polynomial absorption. -/
theorem sqrt_four_mul_fourth_mul_nat
    (M n : ℕ) :
    Real.sqrt ((((M ^ 4 * n) * 4 : ℕ) : ℝ)) =
      2 * (M : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  rw [show (2 * (M : ℝ) ^ 2 * Real.sqrt (n : ℝ)) ^ 2 =
      4 * (M : ℝ) ^ 4 * Real.sqrt (n : ℝ) ^ 2 by ring,
    Real.sq_sqrt (by positivity)]
  push_cast
  ring

/-- The cubed `L∞ → L²` source-domain cost is absorbed uniformly by the
cardinality exponential.  The remaining prefactor is explicit and carries
the expected `M^6` cost. -/
theorem sqrt_explicitBlockCard_pow_three_mul_exp_neg_le
    (M n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Real.sqrt ((((M ^ 4 * n) * 4 : ℕ) : ℝ)) ^ 3 *
        Real.exp (-(κ * (n : ℝ))) ≤
      16 * (M : ℝ) ^ 6 / κ ^ 2 := by
  rw [sqrt_four_mul_fourth_mul_nat]
  have h := sqrt_nat_pow_three_mul_exp_neg_le n hκ
  calc
    (2 * (M : ℝ) ^ 2 * Real.sqrt (n : ℝ)) ^ 3 *
          Real.exp (-(κ * (n : ℝ))) =
        (8 * (M : ℝ) ^ 6) *
          (Real.sqrt (n : ℝ) ^ 3 *
            Real.exp (-(κ * (n : ℝ)))) := by ring
    _ ≤ (8 * (M : ℝ) ^ 6) * (2 / κ ^ 2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 16 * (M : ℝ) ^ 6 / κ ^ 2 := by ring

end

end YangMills.RG

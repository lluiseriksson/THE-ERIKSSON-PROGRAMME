/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98ExpCommutator
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast

/-!
# The coefficient identity behind CMP98's `g(ad Y)` formula

Left multiplication of the ordered derivative series by `exp (-Y)`
produces a triangular convolution.  This file proves the exact alternating
binomial identity governing each monomial `Y^a H Y^b`.  Keeping this finite
identity explicit avoids the invalid shortcut of cancelling `ad Y`.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Reversal of the standard partial alternating binomial sum. -/
theorem cmp98_alternating_choose_convolution (a b : ℕ) :
    (∑ i ∈ Finset.range (a + 1),
        ((-1 : ℤ) ^ (a - i)) * (a + b + 1).choose (a - i)) =
      (-1 : ℤ) ^ a * (a + b).choose a := by
  calc
    (∑ i ∈ Finset.range (a + 1),
        ((-1 : ℤ) ^ (a - i)) * (a + b + 1).choose (a - i)) =
        ∑ i ∈ Finset.range (a + 1),
          ((-1 : ℤ) ^ i) * (a + b + 1).choose i := by
      simpa using (Finset.sum_range_reflect
        (fun i => ((-1 : ℤ) ^ i) * (a + b + 1).choose i) (a + 1))
    _ = (-1 : ℤ) ^ a * (a + b).choose a :=
      Int.alternating_sum_range_choose_eq_choose

/-- Real-valued form of the reversed alternating binomial identity. -/
theorem cmp98_alternating_choose_convolution_real (a b : ℕ) :
    (∑ i ∈ Finset.range (a + 1),
        ((-1 : ℝ) ^ (a - i)) * (a + b + 1).choose (a - i)) =
      (-1 : ℝ) ^ a * (a + b).choose a := by
  exact_mod_cast cmp98_alternating_choose_convolution a b

/-- A single convolution coefficient written with a binomial coefficient. -/
theorem cmp98_exp_deriv_convolution_term (a b i : ℕ) (hi : i < a + 1) :
    ((-1 : ℝ) ^ (a - i)) /
        (((a - i).factorial : ℝ) * ((i + b + 1).factorial : ℝ)) =
      (((-1 : ℝ) ^ (a - i)) * (a + b + 1).choose (a - i)) /
        ((a + b + 1).factorial : ℝ) := by
  have hle : a - i ≤ a + b + 1 := by omega
  have hsub : a + b + 1 - (a - i) = i + b + 1 := by omega
  rw [Nat.cast_choose ℝ hle, hsub]
  have h₁ : ((a - i).factorial : ℝ) ≠ 0 := by positivity
  have h₂ : ((i + b + 1).factorial : ℝ) ≠ 0 := by positivity
  have h₃ : ((a + b + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The scalar coefficient of `Y^a H Y^b` after left trivializing the
ordered exponential derivative. -/
theorem cmp98_exp_deriv_convolution_coefficient (a b : ℕ) :
    (∑ i ∈ Finset.range (a + 1),
        ((-1 : ℝ) ^ (a - i)) /
          (((a - i).factorial : ℝ) * ((i + b + 1).factorial : ℝ))) =
      ((-1 : ℝ) ^ a) /
        (((a.factorial : ℝ) * (b.factorial : ℝ)) * (a + b + 1)) := by
  calc
    (∑ i ∈ Finset.range (a + 1),
        ((-1 : ℝ) ^ (a - i)) /
          (((a - i).factorial : ℝ) * ((i + b + 1).factorial : ℝ))) =
        ∑ i ∈ Finset.range (a + 1),
          (((-1 : ℝ) ^ (a - i)) * (a + b + 1).choose (a - i)) /
            ((a + b + 1).factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact cmp98_exp_deriv_convolution_term a b i (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range (a + 1),
          ((-1 : ℝ) ^ (a - i)) * (a + b + 1).choose (a - i)) /
            ((a + b + 1).factorial : ℝ) := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ = (((-1 : ℝ) ^ a) * (a + b).choose a) /
          ((a + b + 1).factorial : ℝ) := by
      rw [cmp98_alternating_choose_convolution_real]
    _ = ((-1 : ℝ) ^ a) /
          (((a.factorial : ℝ) * (b.factorial : ℝ)) * (a + b + 1)) := by
      rw [Nat.cast_add_choose ℝ, Nat.factorial_succ]
      have ha : (a.factorial : ℝ) ≠ 0 := by positivity
      have hb : (b.factorial : ℝ) ≠ 0 := by positivity
      have hab : ((a + b).factorial : ℝ) ≠ 0 := by positivity
      have hn : (a + b + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring

end YangMills.RG

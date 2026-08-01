/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib

/-!
# D-2a — the single-site Dobrushin coefficient of one bond, and it is sharp

Charter: `docs/DOBRUSHIN-CHARTER.md`.  Gate `scripts/judge_dobrushin_d2.py`,
committed before any computation of the quantity it judges.

## What this module is

Still no measure theory and still no Gibbs measure.  A two-state site in a real
field `h` has conditional `P(+1) = (1 + tanh h)/2`, written from the Boltzmann
weights and from nothing else.  Flipping one neighbour across a bond of strength
`J` moves that field from `h` to `h - 2J`.

The theorem is that the resulting total-variation distance is at most `tanh |J|`
for EVERY field, and equal to it at `h = J`.  That is the number which, summed
over the neighbours of a site, is the Dobrushin coefficient — and it is where the
window `2 tanh β + 2 tanh γ < 1` of this lane comes from.

**Sharpness matters here and is not decoration.**  A coefficient that were merely
an upper bound would leave the window unproved at its own boundary; `attained`
below says the supremum is reached, so the constant is the number and not a
number above it.

## The mechanism, in one line

`tanh a - tanh b = sinh (a - b) / (cosh a * cosh b)`, and the denominator is
minimised exactly when the two fields are symmetric about zero, because
`cosh a * cosh b = (cosh (a+b) + cosh (a-b))/2 ≥ (1 + cosh (a-b))/2`.

## What is NOT here

No probability space, no lattice, no product structure and no decay statement.
This is the single-bond constant alone.  Composing it over the neighbours of a
site, and feeding the result to `Matrix.sum_range_pow_apply_le` of D-1, is D-2b
and D-3, neither of which is in this file.
-/

namespace YangMills.OS

namespace Dobrushin

/-! ## §1  The conditional of a two-state site -/

/-- `P(+1)` for a two-state site in field `h`. -/
noncomputable def pPlus (h : ℝ) : ℝ := (1 + Real.tanh h) / 2

/-- The total-variation distance between two two-point distributions is the
difference of either mass. -/
noncomputable def tvField (h h' : ℝ) : ℝ := |pPlus h - pPlus h'|

theorem tvField_eq (h h' : ℝ) :
    tvField h h' = |Real.tanh h - Real.tanh h'| / 2 := by
  unfold tvField pPlus
  rw [show (1 + Real.tanh h) / 2 - (1 + Real.tanh h') / 2
      = (Real.tanh h - Real.tanh h') / 2 by ring, abs_div]
  norm_num

/-! ## §2  The difference of two hyperbolic tangents -/

/-- `tanh a - tanh b = sinh (a - b) / (cosh a * cosh b)`. -/
theorem tanh_sub_eq (a b : ℝ) :
    Real.tanh a - Real.tanh b = Real.sinh (a - b) / (Real.cosh a * Real.cosh b) := by
  have ha : Real.cosh a ≠ 0 := ne_of_gt (Real.cosh_pos a)
  have hb : Real.cosh b ≠ 0 := ne_of_gt (Real.cosh_pos b)
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub,
    div_sub_div _ _ ha hb, div_eq_div_iff (mul_ne_zero ha hb) (mul_ne_zero ha hb)]
  ring

/-- The product of two hyperbolic cosines, as a sum. -/
theorem cosh_mul_cosh (a b : ℝ) :
    Real.cosh a * Real.cosh b = (Real.cosh (a + b) + Real.cosh (a - b)) / 2 := by
  rw [Real.cosh_add, Real.cosh_sub]; ring

/-- **The denominator is minimised at symmetric fields.**  For any `a b`,
`cosh a * cosh b ≥ cosh ((a - b)/2) ^ 2`. -/
theorem cosh_mul_cosh_ge (a b : ℝ) :
    Real.cosh ((a - b) / 2) ^ 2 ≤ Real.cosh a * Real.cosh b := by
  rw [cosh_mul_cosh, Real.cosh_sq]
  have h1 : (1 : ℝ) ≤ Real.cosh (a + b) := Real.one_le_cosh _
  have h2 : Real.cosh (2 * ((a - b) / 2)) = Real.cosh (a - b) := by
    congr 1; ring
  rw [h2]
  linarith

/-! ## §3  The coefficient, and that it is attained -/

/-- **D-2a, the bound.**  Flipping one neighbour across a bond of strength `J`
moves a site's conditional by at most `tanh |J|`, whatever the field. -/
theorem tvField_le (h J : ℝ) : tvField h (h - 2 * J) ≤ Real.tanh |J| := by
  have hcpos : 0 < Real.cosh h * Real.cosh (h - 2 * J) :=
    mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  have hJpos : 0 < Real.cosh J := Real.cosh_pos J
  have hdiff : h - (h - 2 * J) = 2 * J := by ring
  -- the quotient form
  have hq : tvField h (h - 2 * J)
      = |Real.sinh (2 * J)| / (2 * (Real.cosh h * Real.cosh (h - 2 * J))) := by
    rw [tvField_eq, tanh_sub_eq, hdiff, abs_div,
      abs_of_pos hcpos]
    field_simp
  rw [hq]
  -- the denominator is at least 2 cosh J ^ 2
  have hden : Real.cosh J ^ 2 ≤ Real.cosh h * Real.cosh (h - 2 * J) := by
    have := cosh_mul_cosh_ge h (h - 2 * J)
    rwa [hdiff, show (2 * J) / 2 = J by ring] at this
  have hnum : |Real.sinh (2 * J)| = 2 * |Real.sinh J| * Real.cosh J := by
    rw [Real.sinh_two_mul, abs_mul, abs_mul, abs_two,
      abs_of_pos hJpos]
    ring
  rw [hnum]
  have htanh : Real.tanh |J| = |Real.sinh J| / Real.cosh J := by
    rcases abs_cases J with ⟨hJ, _⟩ | ⟨hJ, _⟩
    · rw [hJ, Real.tanh_eq_sinh_div_cosh, abs_of_nonneg]
      · rfl
      · exact Real.sinh_nonneg_iff.mpr (by linarith [abs_nonneg J, hJ.symm ▸ abs_nonneg J])
    · rw [hJ, Real.tanh_eq_sinh_div_cosh, Real.sinh_neg, Real.cosh_neg,
        abs_of_nonpos, neg_div]
      exact Real.sinh_nonpos_iff.mpr (by linarith)
  rw [htanh, div_le_div_iff (by positivity) hJpos]
  have hs : 0 ≤ |Real.sinh J| := abs_nonneg _
  nlinarith [hden, hJpos, hs, sq_nonneg (Real.cosh J)]

/-- **D-2a, sharpness.**  At `h = J` the two fields are `+J` and `−J`, and the
bound is an equality: the supremum is ATTAINED, so `tanh |J|` is the constant
and not merely an upper bound for it. -/
theorem tvField_attained (J : ℝ) : tvField J (J - 2 * J) = Real.tanh |J| := by
  have hJ : J - 2 * J = -J := by ring
  rw [hJ, tvField_eq, Real.tanh_neg, sub_neg_eq_add]
  rcases abs_cases J with ⟨hab, hJ0⟩ | ⟨hab, hJ0⟩
  · rw [hab, abs_of_nonneg (by
      have : 0 ≤ Real.tanh J := Real.tanh_nonneg_iff.mpr hJ0
      linarith)]
    ring
  · rw [hab, Real.tanh_neg, abs_of_nonpos (by
      have : Real.tanh J ≤ 0 := Real.tanh_nonpos_iff.mpr (le_of_lt hJ0)
      linarith)]
    ring

/-- The coefficient is nonnegative, which D-1 needs of every entry. -/
theorem tanh_abs_nonneg (J : ℝ) : 0 ≤ Real.tanh |J| :=
  Real.tanh_nonneg_iff.mpr (abs_nonneg J)

/-- And below one, so a site with `n` neighbours can meet Dobrushin's condition
only through the SUM, never through a single bond. -/
theorem tanh_abs_lt_one (J : ℝ) : Real.tanh |J| < 1 := Real.tanh_lt_one _

end Dobrushin

end YangMills.OS

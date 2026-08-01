/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib

/-!
# D-2a — the single-site Dobrushin coefficient of one bond, and it is attained

Charter: `docs/DOBRUSHIN-CHARTER.md`.  Gate `scripts/judge_dobrushin_d2.py`,
committed before the quantity it judges was computed even once.

## What this module is

Still no measure theory and still no Gibbs measure.  A two-state site in a real
field `h` has conditional `P(+1) = (1 + tanh h)/2`, written from the Boltzmann
weights and from nothing else.  Flipping one neighbour across a bond of strength
`J` moves that field from `h` to `h - 2J`.

`tvField_le` says the resulting total-variation move is at most `tanh J` for
EVERY field; `tvField_attained` says it equals `tanh J` at `h = J`.  That number,
summed over the neighbours of a site, is the Dobrushin coefficient, and it is
where the window `2 tanh β + 2 tanh γ < 1` comes from.

**Sharpness is not decoration.**  A coefficient that were merely an upper bound
would leave the window undetermined at its own boundary.  `tvField_attained` is
what makes `tanh J` the constant rather than a number above it.

## The sign convention, and why the statements carry `0 ≤ J`

A bond of strength `J` and one of strength `-J` move the conditional by the same
amount, so the coefficient of a general bond is `tanh |J|` and is obtained by
applying the theorems below to `|J|`.  Carrying `0 ≤ J` in the hypotheses rather
than `|J|` in the conclusions removes every case split on the sign of a
hyperbolic function; a first version of this file did the opposite and did not
compile.

## The mechanism, in one line

`tanh a - tanh b = sinh(a-b) / (cosh a · cosh b)`, and the denominator is
minimised exactly when the two fields are symmetric about zero, because
`cosh a · cosh b = (cosh(a+b) + cosh(a-b))/2 ≥ (1 + cosh(a-b))/2`.

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
      = (Real.tanh h - Real.tanh h') / 2 from by ring]
  rw [abs_div, abs_two]

/-! ## §2  Two hyperbolic identities -/

/-- `tanh a - tanh b = sinh (a - b) / (cosh a * cosh b)`. -/
theorem tanh_sub_eq (a b : ℝ) :
    Real.tanh a - Real.tanh b = Real.sinh (a - b) / (Real.cosh a * Real.cosh b) := by
  have ha : Real.cosh a ≠ 0 := ne_of_gt (Real.cosh_pos a)
  have hb : Real.cosh b ≠ 0 := ne_of_gt (Real.cosh_pos b)
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_sub_div _ _ ha hb, ← Real.sinh_sub]

/-- Product to sum.  Stated with FRESH variables: `Real.cosh_sub` matches any
subtraction, so rewriting it against a goal that already contains `cosh (h - 2J)`
tears apart the wrong term.  A first version did exactly that and did not
compile. -/
theorem cosh_mul_cosh (a b : ℝ) :
    Real.cosh a * Real.cosh b = (Real.cosh (a + b) + Real.cosh (a - b)) / 2 := by
  rw [Real.cosh_add, Real.cosh_sub]; ring

/-- **The denominator is minimised at symmetric fields.**  Its minimum over `h`
is `cosh J ^ 2`, reached when the two fields are `+J` and `-J`. -/
theorem cosh_mul_cosh_ge (h J : ℝ) :
    Real.cosh J ^ 2 ≤ Real.cosh h * Real.cosh (h - 2 * J) := by
  have hprod := cosh_mul_cosh h (h - 2 * J)
  have h1 : (1 : ℝ) ≤ Real.cosh (h + (h - 2 * J)) := Real.one_le_cosh _
  have h2 : Real.cosh (h - (h - 2 * J)) = Real.cosh (2 * J) := by
    congr 1; ring
  -- mathlib's `cosh_two_mul` is the `cosh² + sinh²` form; the Pythagorean
  -- identity turns it into the one needed here
  have h3 : Real.cosh (2 * J) = 2 * Real.cosh J ^ 2 - 1 := by
    rw [Real.cosh_two_mul]
    have hp : Real.cosh J ^ 2 - Real.sinh J ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq J
    linarith
  rw [hprod, h2, h3]
  linarith

/-! ## §3  Positivity of `sinh` on the nonnegative axis -/

theorem sinh_nonneg_of_nonneg {J : ℝ} (hJ : 0 ≤ J) : 0 ≤ Real.sinh J := by
  rw [Real.sinh_eq]
  have : Real.exp (-J) ≤ Real.exp J := Real.exp_le_exp.mpr (by linarith)
  linarith

theorem tanh_nonneg_of_nonneg {J : ℝ} (hJ : 0 ≤ J) : 0 ≤ Real.tanh J := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (sinh_nonneg_of_nonneg hJ) (Real.cosh_pos J).le

/-! ## §4  The coefficient, and that it is attained -/

/-- **D-2a, the bound.**  Flipping one neighbour across a bond of strength
`J ≥ 0` moves a site's conditional by at most `tanh J`, whatever the field. -/
theorem tvField_le {J : ℝ} (hJ : 0 ≤ J) (h : ℝ) :
    tvField h (h - 2 * J) ≤ Real.tanh J := by
  have hcJ : 0 < Real.cosh J := Real.cosh_pos J
  have hP : 0 < Real.cosh h * Real.cosh (h - 2 * J) :=
    mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  have hsJ : 0 ≤ Real.sinh J := sinh_nonneg_of_nonneg hJ
  have hge : Real.cosh J ^ 2 ≤ Real.cosh h * Real.cosh (h - 2 * J) :=
    cosh_mul_cosh_ge h J
  have hdiff : h - (h - 2 * J) = 2 * J := by ring
  -- the numerator, in a form whose sign is visible
  have hnum : Real.sinh (2 * J) = 2 * Real.sinh J * Real.cosh J :=
    Real.sinh_two_mul J
  -- the difference of tangents is nonnegative, so the modulus does nothing
  have hq : Real.tanh h - Real.tanh (h - 2 * J)
      = 2 * Real.sinh J * Real.cosh J / (Real.cosh h * Real.cosh (h - 2 * J)) := by
    rw [tanh_sub_eq, hdiff, hnum]
  have hqnn : 0 ≤ Real.tanh h - Real.tanh (h - 2 * J) := by
    rw [hq]
    exact div_nonneg (by positivity) hP.le
  rw [tvField_eq, abs_of_nonneg hqnn, hq]
  -- now a bare inequality between two quotients
  rw [← sub_nonneg]
  have expand : Real.tanh J
      - 2 * Real.sinh J * Real.cosh J / (Real.cosh h * Real.cosh (h - 2 * J)) / 2
      = Real.sinh J * (Real.cosh h * Real.cosh (h - 2 * J) - Real.cosh J ^ 2)
        / (Real.cosh J * (Real.cosh h * Real.cosh (h - 2 * J))) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring
  rw [expand]
  apply div_nonneg
  · exact mul_nonneg hsJ (by linarith)
  · positivity

/-- **D-2a, attainment.**  At `h = J` the two fields are `+J` and `-J`, and the
bound is an equality: the supremum is REACHED, so `tanh J` is the coefficient
and not merely an upper bound for it. -/
theorem tvField_attained {J : ℝ} (hJ : 0 ≤ J) :
    tvField J (J - 2 * J) = Real.tanh J := by
  have hneg : J - 2 * J = -J := by ring
  have htnn : 0 ≤ Real.tanh J := tanh_nonneg_of_nonneg hJ
  rw [hneg, tvField_eq, Real.tanh_neg, sub_neg_eq_add,
    show Real.tanh J + Real.tanh J = 2 * Real.tanh J from by ring,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.tanh J)]

/-- **The coefficient, as a supremum statement.**  `tanh J` is an upper bound for
the total-variation move over all fields, and it is one of the values, so it is
the least upper bound. -/
theorem tvField_isLUB {J : ℝ} (hJ : 0 ≤ J) :
    IsLUB (Set.range fun h : ℝ => tvField h (h - 2 * J)) (Real.tanh J) := by
  constructor
  · rintro x ⟨h, rfl⟩
    exact tvField_le hJ h
  · intro b hb
    exact le_trans (le_of_eq (tvField_attained hJ).symm) (hb ⟨J, rfl⟩)

/-- The coefficient is nonnegative, which D-1 needs of every entry. -/
theorem tanh_nonneg (J : ℝ) (hJ : 0 ≤ J) : 0 ≤ Real.tanh J :=
  tanh_nonneg_of_nonneg hJ

/-- And strictly below one, so a site with several neighbours can meet
Dobrushin's condition only through the SUM, never through a single bond. -/
theorem tanh_lt_one (J : ℝ) : Real.tanh J < 1 := Real.tanh_lt_one J

end Dobrushin

end YangMills.OS

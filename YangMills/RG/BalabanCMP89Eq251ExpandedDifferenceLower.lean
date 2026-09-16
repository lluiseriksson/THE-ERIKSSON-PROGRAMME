/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251ExpandedAliasGeometry

/-!
# Cold-sealed expanded difference lower bound below CMP89 (2.51)

Compiler-verified at exact source checkpoint
`4bf1f1bec890d1dbcf34a0d958ae10b9251e0146` by cold GitHub Actions run
`31233308717`.  Restoration and saving of `.lake/build` were skipped.  The
warning-free focal completed 3,284 jobs, the audit exited zero, and all six
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The sealed alias geometry shows that the fixed even representative set in
CMP89 (2.45) reaches scaled momentum `3*pi/2`, so the central Jordan estimate
on `[-pi,pi]` cannot be reused.  This module proves a separate explicit lower
bound on that expanded interval:

`(1/(3*pi))*|x| <= 2*|sin(x/2)|` for `|x| <= 3*pi/2`.

It transports the same visible constant to the unit and scaled lattice
difference symbols and to the removable sinc denominator, then specializes
both estimates to every printed alias.  No averaging-amplitude numerator,
Laplacian ratio, Holder factor, or complete integrand estimate is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- A coarse but explicit Jordan-type lower bound on the exact expanded
interval reached by the fixed source aliases. -/
theorem one_div_three_pi_mul_abs_le_two_mul_abs_sin_half
    {x : ℝ} (hx : |x| ≤ 3 * Real.pi / 2) :
    (1 / (3 * Real.pi)) * |x| ≤ 2 * |Real.sin (x / 2)| := by
  have hhalfAbs : |x / 2| = |x| / 2 := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hhalf : |x / 2| ≤ 3 * Real.pi / 4 := by
    rw [hhalfAbs]
    linarith
  have hhalfPi : |x / 2| ≤ Real.pi :=
    hhalf.trans (by nlinarith [Real.pi_pos] : 3 * Real.pi / 4 ≤ Real.pi)
  by_cases hcentral : |x / 2| ≤ Real.pi / 2
  · have hjordan := Real.mul_abs_le_abs_sin hcentral
    calc
      (1 / (3 * Real.pi)) * |x| ≤
          2 * ((2 / Real.pi) * |x / 2|) := by
        rw [hhalfAbs]
        field_simp [Real.pi_ne_zero]
        nlinarith [abs_nonneg x]
      _ ≤ 2 * |Real.sin (x / 2)| := by gcongr
  · have houter : Real.pi / 2 < |x / 2| := lt_of_not_ge hcentral
    let y : ℝ := |x / 2|
    have hyNonneg : 0 ≤ y := abs_nonneg _
    have hyUpper : y ≤ 3 * Real.pi / 4 := hhalf
    have hyPi : y ≤ Real.pi := hhalfPi
    have hzNonneg : 0 ≤ Real.pi - y := sub_nonneg.mpr hyPi
    have hzUpper : Real.pi - y ≤ Real.pi / 2 := by
      dsimp [y]
      linarith
    have hzLower : Real.pi / 4 ≤ Real.pi - y := by
      dsimp [y]
      linarith
    have hzAbs : |Real.pi - y| ≤ Real.pi / 2 := by
      rw [abs_of_nonneg hzNonneg]
      exact hzUpper
    have hjordan := Real.mul_abs_le_abs_sin hzAbs
    rw [abs_of_nonneg hzNonneg, Real.sin_pi_sub] at hjordan
    have hsinEq : |Real.sin y| = |Real.sin (x / 2)| := by
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hyNonneg hyPi)]
      exact (Real.abs_sin_eq_sin_abs_of_abs_le_pi hhalfPi).symm
    rw [hsinEq] at hjordan
    have hhalfSin : (1 : ℝ) / 2 ≤ |Real.sin (x / 2)| := by
      apply (show (1 : ℝ) / 2 ≤
          (2 / Real.pi) * (Real.pi - y) by
        field_simp [Real.pi_ne_zero]
        nlinarith [hzLower, Real.pi_pos]).trans
      exact hjordan
    have htarget : (1 / (3 * Real.pi)) * |x| ≤ (1 : ℝ) / 2 := by
      field_simp [Real.pi_ne_zero]
      nlinarith [hx, Real.pi_pos]
    exact htarget.trans (by nlinarith [hhalfSin])

/-- Expanded-zone lower bound for the unit lattice-difference symbol. -/
theorem one_div_three_pi_mul_abs_le_cmp89Eq249UnitDifferenceNorm
    {x : ℝ} (hx : |x| ≤ 3 * Real.pi / 2) :
    (1 / (3 * Real.pi)) * |x| ≤
      cmp89Eq249UnitDifferenceNorm x := by
  have htrig := one_div_three_pi_mul_abs_le_two_mul_abs_sin_half hx
  have hnorm :
      cmp89Eq249UnitDifferenceNorm x = 2 * |Real.sin (x / 2)| := by
    rw [cmp89Eq249UnitDifferenceNorm]
    have h := Complex.norm_exp_I_mul_ofReal_sub_one (-x)
    rw [show Complex.exp (Complex.I * (-x : ℂ)) =
        Complex.exp (Complex.I * ((-x : ℝ) : ℂ)) by norm_num, h]
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_pos (show (0 : ℝ) < 2 by norm_num), neg_div,
      Real.sin_neg, abs_neg]
  rwa [hnorm]

/-- The sinc denominator stays uniformly away from zero on the expanded
alias zone. -/
theorem one_div_three_pi_le_abs_sinc_half_of_abs_le_three_pi_div_two
    {x : ℝ} (hx : |x| ≤ 3 * Real.pi / 2) :
    1 / (3 * Real.pi) ≤ |Real.sinc (x / 2)| := by
  by_cases hx0 : x = 0
  · subst x
    simp only [zero_div, Real.sinc_zero, abs_one]
    exact (div_le_one (mul_pos (by norm_num) Real.pi_pos)).2
      (by nlinarith [Real.pi_gt_three] : 1 ≤ 3 * Real.pi)
  · have hxHalf0 : x / 2 ≠ 0 := div_ne_zero hx0 (by norm_num)
    have htrig := one_div_three_pi_mul_abs_le_two_mul_abs_sin_half hx
    rw [Real.sinc_of_ne_zero hxHalf0, abs_div]
    apply (le_div_iff₀ (abs_pos.mpr hxHalf0)).2
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith

/-- Expanded-zone lower bound for the scaled lattice-difference quotient. -/
theorem one_div_three_pi_mul_abs_le_cmp89Eq245ScaledDifferenceNorm
    {xi p : ℝ} (hxi : 0 < xi)
    (hxp : |xi * p| ≤ 3 * Real.pi / 2) :
    (1 / (3 * Real.pi)) * |p| ≤
      cmp89Eq245ScaledDifferenceNorm xi p := by
  have hunit :=
    one_div_three_pi_mul_abs_le_cmp89Eq249UnitDifferenceNorm hxp
  have hnum :
      ‖Complex.exp (Complex.I * (-(xi * p) : ℂ)) - 1‖ =
        cmp89Eq249UnitDifferenceNorm (xi * p) := by
    rw [cmp89Eq249UnitDifferenceNorm]
    norm_num
  rw [cmp89Eq245ScaledDifferenceNorm, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hxi, hnum]
  apply (le_div_iff₀ hxi).2
  rw [abs_mul, abs_of_pos hxi] at hunit
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hunit

/-- Source-specialized expanded lower bound for every printed coordinate
alias in CMP89 (2.45). -/
theorem one_div_three_pi_mul_abs_alias_le_scaledDifferenceNorm
    {N : ℕ} (hN : 0 < N) {m : ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasIntegers N)
    {p : ℝ} (hp : |p| ≤ Real.pi) :
    (1 / (3 * Real.pi)) * |p + 2 * Real.pi * (m : ℝ)| ≤
      cmp89Eq245ScaledDifferenceNorm (N : ℝ)⁻¹
        (p + 2 * Real.pi * (m : ℝ)) := by
  have hNReal : 0 < (N : ℝ) := by exact_mod_cast hN
  exact one_div_three_pi_mul_abs_le_cmp89Eq245ScaledDifferenceNorm
    (inv_pos.mpr hNReal)
    (abs_inverse_count_mul_add_cmp89Eq245AliasShift_le_three_pi_div_two
      hN hm hp)

/-- Source-specialized lower bound for the removable sinc denominator of
every printed coordinate alias. -/
theorem one_div_three_pi_le_abs_sinc_scaled_alias
    {N : ℕ} (hN : 0 < N) {m : ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasIntegers N)
    {p : ℝ} (hp : |p| ≤ Real.pi) :
    1 / (3 * Real.pi) ≤
      |Real.sinc (((N : ℝ)⁻¹ *
        (p + 2 * Real.pi * (m : ℝ))) / 2)| :=
  one_div_three_pi_le_abs_sinc_half_of_abs_le_three_pi_div_two
    (abs_inverse_count_mul_add_cmp89Eq245AliasShift_le_three_pi_div_two
      hN hm hp)

end

end YangMills.RG

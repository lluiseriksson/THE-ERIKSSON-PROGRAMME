/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245ComplexSincDictionary
import YangMills.RG.BalabanCMP89Eq251ExpandedDifferenceLower

/-!
# PRE-VALIDATION: alias-amplitude upper bound below CMP89 (2.51)

The source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

CMP89 (2.45), printed p. 584, writes the averaging symbol at every reciprocal
alias as a product of one-dimensional exponential quotients.  Periodicity
makes the numerator sine independent of the alias, while the expanded-zone
lower bound already sealed in `BalabanCMP89Eq251ExpandedDifferenceLower`
keeps the removable denominator away from zero.

This module combines those two literal inputs.  It proves an explicit
coordinate bound by `18*pi` times the source weight
`(1 + |2*pi*m|)^(-1)`, then multiplies the bounds to obtain the corresponding
real and complex amplitude estimates in dimension `d`.  No Laplacian ratio,
mass denominator, Holder factor, complete estimate (2.51), or analytic strip
is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Adding a reciprocal-lattice alias changes the half-angle sine only by a
sign, hence does not change its absolute value. -/
theorem abs_sin_half_add_alias (p : ℝ) (m : ℤ) :
    |Real.sin ((p + 2 * Real.pi * (m : ℝ)) / 2)| =
      |Real.sin (p / 2)| := by
  have harg :
      (p + 2 * Real.pi * (m : ℝ)) / 2 =
        p / 2 + (m : ℝ) * Real.pi := by ring
  rw [harg, Real.sin_add_int_mul_pi, abs_mul]
  norm_num

/-- A noncentral reciprocal alias stays at least `pi*|m|` away from zero on
the central momentum interval. -/
theorem pi_mul_abs_cast_le_abs_add_alias
    {p : ℝ} (hp : |p| ≤ Real.pi) {m : ℤ} (hm : m ≠ 0) :
    Real.pi * |(m : ℝ)| ≤ |p + 2 * Real.pi * (m : ℝ)| := by
  have hmOneInt : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
  have hmOne : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast hmOneInt
  have htriangle :
      |2 * Real.pi * (m : ℝ)| ≤
        |p + 2 * Real.pi * (m : ℝ)| + |p| := by
    calc
      |2 * Real.pi * (m : ℝ)| =
          |(p + 2 * Real.pi * (m : ℝ)) + (-p)| := by
        congr 1
        ring
      _ ≤ |p + 2 * Real.pi * (m : ℝ)| + |-p| := abs_add_le _ _
      _ = |p + 2 * Real.pi * (m : ℝ)| + |p| := by rw [abs_neg]
  have hshift :
      |2 * Real.pi * (m : ℝ)| =
        2 * Real.pi * |(m : ℝ)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
  rw [hshift] at htriangle
  nlinarith [Real.pi_pos]

/-- The removable numerator sinc has the reciprocal-alias decay used in
CMP89 (2.51).  The constant `6` is coarse but explicit and uniform in the
central momentum. -/
theorem abs_sinc_half_add_alias_le_six_mul_weight
    {p : ℝ} (hp : |p| ≤ Real.pi) (m : ℤ) :
    |Real.sinc ((p + 2 * Real.pi * (m : ℝ)) / 2)| ≤
      6 * cmp89Eq251OneDimensionalAliasWeight 1 m := by
  by_cases hm : m = 0
  · subst m
    simp only [Int.cast_zero, mul_zero, add_zero,
      cmp89Eq251OneDimensionalAliasWeight, abs_zero, add_zero,
      Real.one_rpow, one_div, inv_one, mul_one]
    exact (Real.abs_sinc_le_one (p / 2)).trans (by norm_num)
  · let q : ℝ := p + 2 * Real.pi * (m : ℝ)
    have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hmOneInt : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
    have hmOne : (1 : ℝ) ≤ |(m : ℝ)| := by
      exact_mod_cast hmOneInt
    have hqLower : Real.pi * |(m : ℝ)| ≤ |q| := by
      exact pi_mul_abs_cast_le_abs_add_alias hp hm
    have hqPos : 0 < |q| :=
      lt_of_lt_of_le (mul_pos Real.pi_pos (abs_pos.mpr hmReal)) hqLower
    have hq0 : q ≠ 0 := abs_pos.mp hqPos
    have hqHalf0 : q / 2 ≠ 0 := div_ne_zero hq0 (by norm_num)
    have hsinc : |Real.sinc (q / 2)| ≤ 2 / |q| := by
      rw [Real.sinc_of_ne_zero hqHalf0, abs_div]
      apply (div_le_iff₀ (abs_pos.mpr hqHalf0)).2
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      calc
        |Real.sin (q / 2)| ≤ 1 := Real.abs_sin_le_one _
        _ = (2 / |q|) * (|q| / 2) := by
          field_simp [ne_of_gt hqPos]
    have hshiftAbs :
        |2 * Real.pi * (m : ℝ)| =
          2 * Real.pi * |(m : ℝ)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]
    have hdecay :
        2 / |q| ≤ 6 / (1 + |2 * Real.pi * (m : ℝ)|) := by
      rw [hshiftAbs]
      apply (div_le_div_iff₀ hqPos
        (by positivity : 0 < 1 + 2 * Real.pi * |(m : ℝ)|)).2
      nlinarith [Real.pi_gt_three]
    rw [show p + 2 * Real.pi * (m : ℝ) = q by rfl,
      cmp89Eq251OneDimensionalAliasWeight, Real.rpow_one]
    exact hsinc.trans (by simpa [div_eq_mul_inv] using hdecay)

/-- Every printed one-coordinate averaging factor is bounded by the literal
reciprocal-lattice weight, with the denominator cost `3*pi` left visible. -/
theorem abs_cmp89Eq245SincAverageFactor_scaled_alias_le
    {N : ℕ} (hN : 0 < N) {m : ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasIntegers N)
    {p : ℝ} (hp : |p| ≤ Real.pi) :
    |cmp89Eq245SincAverageFactor (N : ℝ)⁻¹
        (p + 2 * Real.pi * (m : ℝ))| ≤
      (18 * Real.pi) * cmp89Eq251OneDimensionalAliasWeight 1 m := by
  have hnum := abs_sinc_half_add_alias_le_six_mul_weight hp m
  have hden := one_div_three_pi_le_abs_sinc_scaled_alias hN hm hp
  have hthreePi : 0 < 3 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hdenPos :
      0 < |Real.sinc (((N : ℝ)⁻¹ *
        (p + 2 * Real.pi * (m : ℝ))) / 2)| :=
    (div_pos (by norm_num) hthreePi).trans_le hden
  rw [cmp89Eq245SincAverageFactor, abs_div]
  apply (div_le_iff₀ hdenPos).2
  apply hnum.trans
  have hweightNonneg := cmp89Eq251OneDimensionalAliasWeight_nonneg 1 m
  calc
    6 * cmp89Eq251OneDimensionalAliasWeight 1 m =
        ((18 * Real.pi) * cmp89Eq251OneDimensionalAliasWeight 1 m) *
          (1 / (3 * Real.pi)) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ ((18 * Real.pi) * cmp89Eq251OneDimensionalAliasWeight 1 m) *
          |Real.sinc (((N : ℝ)⁻¹ *
            (p + 2 * Real.pi * (m : ℝ))) / 2)| := by
      gcongr

/-- Product-level real amplitude bound for every printed alias vector. -/
theorem abs_cmp89Eq245SincAverageAmplitude_scaled_alias_le
    {d N : ℕ} (hN : 0 < N) {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    |cmp89Eq245SincAverageAmplitude d (N : ℝ)⁻¹
        (fun mu => p mu + 2 * Real.pi * (m mu : ℝ))| ≤
      (18 * Real.pi) ^ d *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
  rw [cmp89Eq245SincAverageAmplitude, Finset.abs_prod,
    cmp89Eq251MultidimensionalAliasWeight]
  calc
    (∏ mu, |cmp89Eq245SincAverageFactor (N : ℝ)⁻¹
        (p mu + 2 * Real.pi * (m mu : ℝ))|) ≤
        ∏ mu, (18 * Real.pi) *
          cmp89Eq251OneDimensionalAliasWeight 1 (m mu) := by
      apply Finset.prod_le_prod
      · intro mu _
        positivity
      · intro mu _
        exact abs_cmp89Eq245SincAverageFactor_scaled_alias_le hN
          (by
            rw [cmp89Eq245CenteredAliasVectors,
              Fintype.mem_piFinset] at hm
            exact hm mu) (hp mu)
    _ = (18 * Real.pi) ^ d *
        ∏ mu, cmp89Eq251OneDimensionalAliasWeight 1 (m mu) := by
      rw [Finset.prod_mul_distrib, Fin.prod_const]

/-- Complex form of the same product estimate, through the exact norm
dictionary for the removable exponential quotient in CMP89 (2.45). -/
theorem norm_cmp89Eq245ComplexAverageAmplitude_scaled_alias_le
    {d N : ℕ} (hN : 0 < N) {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    ‖cmp89Eq245ComplexAverageAmplitude d (N : ℝ)⁻¹
        (fun mu => p mu + 2 * Real.pi * (m mu : ℝ))‖ ≤
      (18 * Real.pi) ^ d *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
  rw [norm_cmp89Eq245ComplexAverageAmplitude]
  exact abs_cmp89Eq245SincAverageAmplitude_scaled_alias_le hN hm hp

end

end YangMills.RG

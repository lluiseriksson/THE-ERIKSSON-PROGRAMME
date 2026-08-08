/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireLaplacianVariation
import YangMills.RG.BalabanCMP89Eq251AliasAmplitudeUpper

/-!
# Alias-weighted strip bound for the entire CMP89 average

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

The scale-uniform strip-growth estimate for the finite geometric average is
not enough for the noncentral alias sum: applying it independently to every
alias would reintroduce the cardinality of the reciprocal fibre.  This module
keeps the reciprocal-alias weight by using the finite geometric quotient
before estimating.

The real expanded-zone denominator is at least
`N⁻¹ * |p + 2*pi*m| / (3*pi)`.  A vertical displacement costs at most
`N⁻¹ * rho*exp(rho)`.  Under the explicit scale-free condition
`rho*exp(rho) <= 1/6`, every nonzero coordinate alias retains half of the real
denominator.  The literal `N⁻¹` in the normalized average then cancels, giving
one factor of `(1+|2*pi*m|)⁻¹`.  Zero coordinate aliases are handled directly
by the sealed entire strip-growth bound.

Here `rho` remains the normalized Brillouin-momentum strip width.  No
fine/block spatial conversion, stabilized-denominator radius, `B0`, contour
shift or regional-Green estimate is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit one-coordinate constant in the alias-weighted complex bound. -/
def cmp89Eq245EntireAverageAliasStripConstant (rho : ℝ) : ℝ :=
  18 * Real.pi * (Real.exp rho + 1)

/-- The geometric base varies vertically with the normalized factor `N⁻¹`
still visible. -/
theorem norm_cmp89Eq245EntireAverageBase_sub_realSlice_le
    {N : ℕ} (hN : 0 < N) {z : ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hz : |z.im| ≤ rho) :
    ‖cmp89Eq245EntireAverageBase N z -
        cmp89Eq245EntireAverageBase N (z.re : ℂ)‖ ≤
      (N : ℝ)⁻¹ * (rho * Real.exp rho) := by
  let xi : ℝ := (N : ℝ)⁻¹
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hxi : 0 < xi := inv_pos.mpr hNreal
  have hxi1 : xi ≤ 1 := by
    dsimp [xi]
    rw [inv_le_one₀ hNreal]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN))
  have hdiff :=
    norm_cmp89Eq245EntireScaledDifference_sub_realSlice_le
      hxi hxi1 hrho hz
  have heq :
      cmp89Eq245EntireAverageBase N z -
          cmp89Eq245EntireAverageBase N (z.re : ℂ) =
        (xi : ℂ) *
          (cmp89Eq245EntireScaledDifference xi z -
            cmp89Eq245EntireScaledDifference xi (z.re : ℂ)) := by
    unfold cmp89Eq245EntireAverageBase cmp89Eq245EntireScaledDifference
    dsimp [xi]
    field_simp [ne_of_gt hNreal]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxi]
  exact mul_le_mul_of_nonneg_left hdiff hxi.le

/-- The numerator of the finite geometric quotient is uniform in the real
momentum and hence in the reciprocal alias. -/
theorem norm_cmp89Eq245EntireAverageBase_pow_sub_one_le
    {N : ℕ} (hN : 0 < N) {z : ℂ} {rho : ℝ}
    (hz : |z.im| ≤ rho) :
    ‖cmp89Eq245EntireAverageBase N z ^ N - 1‖ ≤ Real.exp rho + 1 := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    ‖cmp89Eq245EntireAverageBase N z ^ N - 1‖ ≤
        ‖cmp89Eq245EntireAverageBase N z ^ N‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = Real.exp z.im + 1 := by
      rw [norm_cmp89Eq245EntireAverageBase_pow_eq hN]
      simp [hNreal]
    _ ≤ Real.exp rho + 1 := by
      gcongr
      exact (le_abs_self z.im).trans hz

/-- Exact geometric-quotient form of the entire average away from a zero of
the geometric denominator. -/
theorem cmp89Eq245EntireAverageFactor_eq_geometricQuotient
    {N : ℕ} {z : ℂ}
    (hbase : cmp89Eq245EntireAverageBase N z ≠ 1) :
    cmp89Eq245EntireAverageFactor N z =
      (N : ℂ)⁻¹ *
        ((cmp89Eq245EntireAverageBase N z ^ N - 1) /
          (cmp89Eq245EntireAverageBase N z - 1)) := by
  rw [cmp89Eq245EntireAverageFactor, geom_sum_eq hbase]

/-- The real geometric denominator retains the expanded-zone sinc floor. -/
theorem one_div_three_pi_mul_abs_le_norm_cmp89Eq245EntireAverageBase_sub_one
    {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hzone : |(N : ℝ)⁻¹ * q| ≤ 3 * Real.pi / 2) :
    (N : ℝ)⁻¹ * ((1 / (3 * Real.pi)) * |q|) ≤
      ‖cmp89Eq245EntireAverageBase N (q : ℂ) - 1‖ := by
  let xi : ℝ := (N : ℝ)⁻¹
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hxi : 0 < xi := inv_pos.mpr hNreal
  have hscaled :=
    one_div_three_pi_mul_abs_le_cmp89Eq245ScaledDifferenceNorm hxi hzone
  have heq :
      cmp89Eq245EntireAverageBase N (q : ℂ) - 1 =
        (xi : ℂ) * cmp89Eq245EntireScaledDifference xi (q : ℂ) := by
    unfold cmp89Eq245EntireAverageBase cmp89Eq245EntireScaledDifference
    dsimp [xi]
    field_simp [ne_of_gt hNreal]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxi,
    norm_cmp89Eq245EntireScaledDifference_ofReal_eq]
  exact mul_le_mul_of_nonneg_left hscaled hxi.le

/-- A noncentral coordinate retains half of its real geometric denominator
under the scale-free strip budget. -/
theorem one_div_six_pi_mul_abs_le_norm_cmp89Eq245EntireAverageBase_sub_one
    {N : ℕ} (hN : 0 < N) {q rho : ℝ}
    (hrho : 0 ≤ rho) (hq : Real.pi ≤ |q|)
    {z : ℂ} (hreal : z.re = q) (himag : |z.im| ≤ rho)
    (hzone : |(N : ℝ)⁻¹ * q| ≤ 3 * Real.pi / 2)
    (hsmall : rho * Real.exp rho ≤ 1 / 6) :
    (N : ℝ)⁻¹ * ((1 / (6 * Real.pi)) * |q|) ≤
      ‖cmp89Eq245EntireAverageBase N z - 1‖ := by
  let xi : ℝ := (N : ℝ)⁻¹
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hxi : 0 < xi := inv_pos.mpr hNreal
  have hrealDen :=
    one_div_three_pi_mul_abs_le_norm_cmp89Eq245EntireAverageBase_sub_one
      hN hzone
  have hvarRaw :=
    norm_cmp89Eq245EntireAverageBase_sub_realSlice_le hN hrho himag
  have hpiPart :
      (1 : ℝ) / 6 ≤ (1 / (6 * Real.pi)) * |q| := by
    calc
      (1 : ℝ) / 6 = (1 / (6 * Real.pi)) * Real.pi := by
        field_simp [Real.pi_ne_zero]
      _ ≤ (1 / (6 * Real.pi)) * |q| := by
        exact mul_le_mul_of_nonneg_left hq (by positivity)
  have hvar :
      ‖cmp89Eq245EntireAverageBase N z -
          cmp89Eq245EntireAverageBase N (q : ℂ)‖ ≤
        xi * ((1 / (6 * Real.pi)) * |q|) := by
    have hslice : (z.re : ℂ) = (q : ℂ) := by rw [hreal]
    rw [← hslice]
    exact hvarRaw.trans <|
      mul_le_mul_of_nonneg_left (hsmall.trans hpiPart) hxi.le
  have htri :
      ‖cmp89Eq245EntireAverageBase N (q : ℂ) - 1‖ ≤
        ‖cmp89Eq245EntireAverageBase N (q : ℂ) -
            cmp89Eq245EntireAverageBase N z‖ +
          ‖cmp89Eq245EntireAverageBase N z - 1‖ := by
    calc
      ‖cmp89Eq245EntireAverageBase N (q : ℂ) - 1‖ =
          ‖(cmp89Eq245EntireAverageBase N (q : ℂ) -
              cmp89Eq245EntireAverageBase N z) +
            (cmp89Eq245EntireAverageBase N z - 1)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev] at hvar
  change xi * ((1 / (6 * Real.pi)) * |q|) ≤ _
  change xi * ((1 / (3 * Real.pi)) * |q|) ≤ _ at hrealDen
  have hdouble :
      xi * ((1 / (3 * Real.pi)) * |q|) =
        2 * (xi * ((1 / (6 * Real.pi)) * |q|)) := by ring
  rw [hdouble] at hrealDen
  linarith

/-- One coordinate of the entire average preserves the reciprocal-alias
weight throughout the complex strip. -/
theorem norm_cmp89Eq245EntireAverageFactor_scaled_alias_le
    {N : ℕ} (hN : 0 < N) {m : ℤ}
    {p rho : ℝ} (hrho : 0 ≤ rho) (hp : |p| ≤ Real.pi)
    {z : ℂ}
    (hreal : z.re = p + 2 * Real.pi * (m : ℝ))
    (himag : |z.im| ≤ rho)
    (hzone : |(N : ℝ)⁻¹ * (p + 2 * Real.pi * (m : ℝ))| ≤
      3 * Real.pi / 2)
    (hsmall : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAverageFactor N z‖ ≤
      cmp89Eq245EntireAverageAliasStripConstant rho *
        cmp89Eq251OneDimensionalAliasWeight 1 m := by
  by_cases hm : m = 0
  · subst m
    have hstrip := norm_cmp89Eq245EntireAverageFactor_le_exp
      hN hrho himag
    rw [cmp89Eq245EntireAverageAliasStripConstant,
      cmp89Eq251OneDimensionalAliasWeight]
    norm_num
    nlinarith [Real.pi_gt_three, Real.exp_pos rho]
  · let q : ℝ := p + 2 * Real.pi * (m : ℝ)
    let xi : ℝ := (N : ℝ)⁻¹
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hxi : 0 < xi := inv_pos.mpr hNreal
    have hqLower : Real.pi * |(m : ℝ)| ≤ |q| :=
      pi_mul_abs_cast_le_abs_add_alias hp hm
    have hmOneInt : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
    have hmOne : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hmOneInt
    have hqPi : Real.pi ≤ |q| := by nlinarith [Real.pi_pos]
    have hqPos : 0 < |q| := Real.pi_pos.trans_le hqPi
    have hden :=
      one_div_six_pi_mul_abs_le_norm_cmp89Eq245EntireAverageBase_sub_one
        hN hrho hqPi hreal himag hzone hsmall
    have hdenPos :
        0 < ‖cmp89Eq245EntireAverageBase N z - 1‖ :=
      (mul_pos hxi (mul_pos (by positivity) hqPos)).trans_le hden
    have hbase : cmp89Eq245EntireAverageBase N z ≠ 1 := by
      intro h
      rw [h, sub_self, norm_zero] at hdenPos
      exact lt_irrefl 0 hdenPos
    have hnum :=
      norm_cmp89Eq245EntireAverageBase_pow_sub_one_le hN himag
    have hquot :
        ‖cmp89Eq245EntireAverageFactor N z‖ ≤
          6 * Real.pi * (Real.exp rho + 1) / |q| := by
      rw [cmp89Eq245EntireAverageFactor_eq_geometricQuotient hbase,
        norm_mul, norm_div, norm_inv, Complex.norm_natCast]
      apply (le_div_iff₀ hqPos).2
      apply (div_le_iff₀ hdenPos).2
      have hscale :
          (N : ℝ)⁻¹ * |q| *
              ‖cmp89Eq245EntireAverageBase N z ^ N - 1‖ ≤
            (Real.exp rho + 1) *
              ‖cmp89Eq245EntireAverageBase N z - 1‖ *
              (6 * Real.pi) := by
        calc
          (N : ℝ)⁻¹ * |q| *
              ‖cmp89Eq245EntireAverageBase N z ^ N - 1‖ ≤
            (N : ℝ)⁻¹ * |q| * (Real.exp rho + 1) := by
              gcongr
          _ ≤ (Real.exp rho + 1) *
              ‖cmp89Eq245EntireAverageBase N z - 1‖ *
              (6 * Real.pi) := by
            have hpi : 0 < 6 * Real.pi := mul_pos (by norm_num) Real.pi_pos
            have := mul_le_mul_of_nonneg_right hden hpi.le
            nlinarith [Real.exp_pos rho]
      simpa [div_eq_mul_inv, xi, mul_assoc, mul_left_comm, mul_comm] using hscale
    have hshiftAbs :
        |2 * Real.pi * (m : ℝ)| =
          2 * Real.pi * |(m : ℝ)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]
    have hweightDen :
        1 + |2 * Real.pi * (m : ℝ)| ≤ 3 * |q| := by
      rw [hshiftAbs]
      nlinarith [Real.pi_gt_three]
    apply hquot.trans
    rw [cmp89Eq245EntireAverageAliasStripConstant,
      cmp89Eq251OneDimensionalAliasWeight, Real.rpow_one]
    have hwPos : 0 < 1 + |2 * Real.pi * (m : ℝ)| := by positivity
    change
      6 * Real.pi * (Real.exp rho + 1) / |q| ≤
        (18 * Real.pi * (Real.exp rho + 1)) /
          (1 + |2 * Real.pi * (m : ℝ)|)
    apply (div_le_div_iff₀ hqPos hwPos).2
    nlinarith [Real.pi_pos, Real.exp_pos rho]

/-- Product-level alias-weighted strip bound, uniform in the averaging scale
and with no reciprocal-fibre cardinality. -/
theorem norm_cmp89Eq245EntireAverageAmplitude_scaled_alias_le
    {d N : ℕ} (hN : 0 < N) {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    {rho : ℝ} (hrho : 0 ≤ rho)
    {pvec : Fin d → ℝ} (hp : ∀ mu, |pvec mu| ≤ Real.pi)
    {z : Fin d → ℂ}
    (hreal : ∀ mu, (z mu).re =
      pvec mu + 2 * Real.pi * (m mu : ℝ))
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hsmall : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAverageAmplitude d N z‖ ≤
      cmp89Eq245EntireAverageAliasStripConstant rho ^ d *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
  rw [cmp89Eq245EntireAverageAmplitude, norm_prod,
    cmp89Eq251MultidimensionalAliasWeight]
  calc
    (∏ mu, ‖cmp89Eq245EntireAverageFactor N (z mu)‖) ≤
        ∏ mu, cmp89Eq245EntireAverageAliasStripConstant rho *
          cmp89Eq251OneDimensionalAliasWeight 1 (m mu) := by
      apply Finset.prod_le_prod
      · intro mu _
        exact norm_nonneg _
      · intro mu _
        apply norm_cmp89Eq245EntireAverageFactor_scaled_alias_le
          hN hrho (hp mu) (hreal mu) (himag mu)
        · exact abs_inverse_count_mul_add_cmp89Eq245AliasShift_le_three_pi_div_two
            hN (by
              rw [cmp89Eq245CenteredAliasVectors, Fintype.mem_piFinset] at hm
              exact hm mu) (hp mu)
        · exact hsmall
    _ = cmp89Eq245EntireAverageAliasStripConstant rho ^ d *
        ∏ mu, cmp89Eq251OneDimensionalAliasWeight 1 (m mu) := by
      rw [Finset.prod_mul_distrib, Fin.prod_const]

end

end YangMills.RG

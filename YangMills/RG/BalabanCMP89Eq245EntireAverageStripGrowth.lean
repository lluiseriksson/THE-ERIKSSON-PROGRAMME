/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251EntireAverageAmplitude

/-!
# Scale-uniform strip growth of the entire CMP89 average

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

The pole-free continuation used below CMP89 (2.51) is the normalized finite
average

`u_N(z) = N^(-1) * sum_{r < N} exp(-i*(r/N)*z)`.

Its frequencies are `r/N < 1`, not integers of size `N`.  Consequently every
summand has norm at most `exp rho` on `|Im z| <= rho`, and normalization by
`N` cancels the number of summands exactly.  The resulting bound is uniform
in the averaging scale `N`; no fine/block conversion or hidden `N` factor is
used.

This module proves only strip growth.  It does not yet prove a difference or
derivative bound, complex denominator nonvanishing, a strip radius, `B0`, a
contour shift, or the regional-Green estimate.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Exact norm of one normalized Fourier mode in the entire averaging
factor.  The exponent contains the physical frequency `r / N`. -/
theorem norm_cmp89Eq245EntireAverageBase_pow_eq
    {N r : ℕ} (hN : 0 < N) (z : ℂ) :
    ‖cmp89Eq245EntireAverageBase N z ^ r‖ =
      Real.exp (((r : ℝ) / (N : ℝ)) * z.im) := by
  rw [norm_pow, cmp89Eq245EntireAverageBase, Complex.norm_exp,
    ← Real.exp_nat_mul]
  congr 1
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp [Complex.mul_re, Complex.mul_im, hNreal, div_eq_mul_inv]
  ring

/-- Every Fourier mode of the normalized average has scale-uniform strip
growth. -/
theorem norm_cmp89Eq245EntireAverageBase_pow_le_exp
    {N r : ℕ} (hN : 0 < N) (hr : r < N)
    {z : ℂ} {rho : ℝ} (hrho : 0 ≤ rho) (hz : |z.im| ≤ rho) :
    ‖cmp89Eq245EntireAverageBase N z ^ r‖ ≤ Real.exp rho := by
  rw [norm_cmp89Eq245EntireAverageBase_pow_eq hN]
  apply Real.exp_le_exp.mpr
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hfreq0 : 0 ≤ (r : ℝ) / (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg r) hNreal.le
  have hfreq1 : (r : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNreal]
    exact_mod_cast Nat.le_of_lt hr
  have hzim : z.im ≤ rho := (le_abs_self z.im).trans hz
  by_cases hsign : z.im ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos hfreq0 hsign).trans hrho
  · exact (mul_le_of_le_one_left (le_of_not_ge hsign) hfreq1).trans hzim

/-- The normalized one-coordinate averaging factor has growth `exp rho` on
the strip, independently of `N`.  The factor `N` from the finite sum is
cancelled by the literal `N⁻¹` normalization. -/
theorem norm_cmp89Eq245EntireAverageFactor_le_exp
    {N : ℕ} (hN : 0 < N) {z : ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hz : |z.im| ≤ rho) :
    ‖cmp89Eq245EntireAverageFactor N z‖ ≤ Real.exp rho := by
  rw [cmp89Eq245EntireAverageFactor, norm_mul]
  calc
    ‖(N : ℂ)⁻¹‖ * ‖∑ r ∈ Finset.range N,
        cmp89Eq245EntireAverageBase N z ^ r‖ ≤
        ‖(N : ℂ)⁻¹‖ * ∑ r ∈ Finset.range N,
          ‖cmp89Eq245EntireAverageBase N z ^ r‖ := by
            gcongr
            exact norm_sum_le _ _
    _ ≤ ‖(N : ℂ)⁻¹‖ * ∑ _r ∈ Finset.range N, Real.exp rho := by
          gcongr with r hr
          exact norm_cmp89Eq245EntireAverageBase_pow_le_exp hN
            (Finset.mem_range.mp hr) hrho hz
    _ = Real.exp rho := by
          have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
          simp [norm_inv, hNreal]

/-- The `d`-coordinate entire averaging amplitude has strip growth
`exp rho ^ d`, with no scale-dependent constant. -/
theorem norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow
    {d N : ℕ} (hN : 0 < N) {z : Fin d → ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hz : ∀ mu, |(z mu).im| ≤ rho) :
    ‖cmp89Eq245EntireAverageAmplitude d N z‖ ≤ Real.exp rho ^ d := by
  rw [cmp89Eq245EntireAverageAmplitude, norm_prod]
  calc
    ∏ mu, ‖cmp89Eq245EntireAverageFactor N (z mu)‖ ≤
        ∏ _mu : Fin d, Real.exp rho := by
          exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
            (fun mu _ => norm_cmp89Eq245EntireAverageFactor_le_exp hN hrho (hz mu))
    _ = Real.exp rho ^ d := by simp

/-- The holomorphic opposite-momentum pairing used by the complexified
denominator costs at most `exp rho ^ (2*d)` on the symmetric strip. -/
theorem norm_cmp89Eq245EntireAverageAmplitude_mul_neg_le_exp_pow
    {d N : ℕ} (hN : 0 < N) {z : Fin d → ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hz : ∀ mu, |(z mu).im| ≤ rho) :
    ‖cmp89Eq245EntireAverageAmplitude d N z *
        cmp89Eq245EntireAverageAmplitude d N (-z)‖ ≤
      Real.exp rho ^ (2 * d) := by
  rw [norm_mul]
  calc
    ‖cmp89Eq245EntireAverageAmplitude d N z‖ *
        ‖cmp89Eq245EntireAverageAmplitude d N (-z)‖ ≤
      (Real.exp rho ^ d) * (Real.exp rho ^ d) := by
        gcongr
        · exact norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow hN hrho hz
        · apply norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow hN hrho
          intro mu
          simpa using hz mu
    _ = Real.exp rho ^ (2 * d) := by ring

end

end YangMills.RG

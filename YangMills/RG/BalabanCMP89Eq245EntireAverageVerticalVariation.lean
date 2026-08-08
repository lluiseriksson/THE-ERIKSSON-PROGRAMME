/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireAverageStripGrowth

/-!
# Scale-uniform vertical variation of the entire CMP89 average

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

The contour argument compares a complex momentum `z` with the point on the
real slice having the same real part.  This is materially sharper than an
arbitrary complex Lipschitz estimate: the real momentum and reciprocal alias
drop out of the difference.  For the normalized frequency `r/N`, one mode
costs at most `(r/N) * |Im z| * exp rho`, and averaging over `r < N` leaves the
uniform bound `rho * exp rho`.

No `N`, alias-cardinality, or fine/block conversion factor is introduced.
This module does not yet telescope products over coordinates, bound the
stabilized denominator, produce a strip radius or `B0`, shift a contour, or
construct the regional Green function.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The exponent of the `r`-th normalized Fourier mode. -/
def cmp89Eq245EntireAverageModeExponent (N r : ℕ) (z : ℂ) : ℂ :=
  (r : ℂ) * (Complex.I * (-((N : ℂ)⁻¹ * z)))

/-- A power of the geometric base is exactly the exponential at normalized
frequency `r/N`. -/
theorem cmp89Eq245EntireAverageBase_pow_eq_exp_modeExponent
    (N r : ℕ) (z : ℂ) :
    cmp89Eq245EntireAverageBase N z ^ r =
      Complex.exp (cmp89Eq245EntireAverageModeExponent N r z) := by
  rw [cmp89Eq245EntireAverageBase, ← Complex.exp_nat_mul]
  rfl

/-- Exact size of the exponent displacement from `z` to its vertical
projection on the real slice. -/
theorem norm_cmp89Eq245EntireAverageModeExponent_sub_realSlice_eq
    {N r : ℕ} (hN : 0 < N) (z : ℂ) :
    ‖cmp89Eq245EntireAverageModeExponent N r z -
        cmp89Eq245EntireAverageModeExponent N r (z.re : ℂ)‖ =
      ((r : ℝ) / (N : ℝ)) * |z.im| := by
  have hz : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [show
      cmp89Eq245EntireAverageModeExponent N r z -
          cmp89Eq245EntireAverageModeExponent N r (z.re : ℂ) =
        (r : ℂ) * Complex.I * (-(N : ℂ)⁻¹) * (z - (z.re : ℂ)) by
      unfold cmp89Eq245EntireAverageModeExponent
      ring]
  simp [hz, norm_inv, div_eq_mul_inv, Real.norm_eq_abs]

/-- General exponential-difference estimate used after the real momentum has
cancelled. -/
theorem norm_complex_exp_sub_exp_le_of_norm_sub_le
    {A B : ℂ} {rho : ℝ} (hrho : 0 ≤ rho)
    (hB : ‖Complex.exp B‖ ≤ 1) (hAB : ‖A - B‖ ≤ rho) :
    ‖Complex.exp A - Complex.exp B‖ ≤ rho * Real.exp rho := by
  have hfactor :
      Complex.exp A - Complex.exp B =
        Complex.exp B * (Complex.exp (A - B) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    ring_nf
  have htail :
      ‖Complex.exp (A - B) - 1‖ ≤
        ‖A - B‖ * Real.exp ‖A - B‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (A - B) 1
  rw [hfactor, norm_mul]
  calc
    ‖Complex.exp B‖ * ‖Complex.exp (A - B) - 1‖ ≤
        1 * (‖A - B‖ * Real.exp ‖A - B‖) := by gcongr
    _ ≤ 1 * (rho * Real.exp rho) := by gcongr
    _ = rho * Real.exp rho := one_mul _

/-- A single normalized mode varies from the matching real point by at most
`rho * exp rho`, uniformly in `N` and `r < N`. -/
theorem norm_cmp89Eq245EntireAverageBase_pow_sub_realSlice_le
    {N r : ℕ} (hN : 0 < N) (hr : r < N)
    {z : ℂ} {rho : ℝ} (hrho : 0 ≤ rho) (hz : |z.im| ≤ rho) :
    ‖cmp89Eq245EntireAverageBase N z ^ r -
        cmp89Eq245EntireAverageBase N (z.re : ℂ) ^ r‖ ≤
      rho * Real.exp rho := by
  rw [cmp89Eq245EntireAverageBase_pow_eq_exp_modeExponent,
    cmp89Eq245EntireAverageBase_pow_eq_exp_modeExponent]
  apply norm_complex_exp_sub_exp_le_of_norm_sub_le hrho
  · rw [← cmp89Eq245EntireAverageBase_pow_eq_exp_modeExponent,
      norm_cmp89Eq245EntireAverageBase_pow_eq hN]
    simp
  · rw [norm_cmp89Eq245EntireAverageModeExponent_sub_realSlice_eq hN]
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hfreq0 : 0 ≤ (r : ℝ) / (N : ℝ) :=
      div_nonneg (Nat.cast_nonneg r) hNreal.le
    have hfreq1 : (r : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNreal]
      exact_mod_cast Nat.le_of_lt hr
    calc
      (r : ℝ) / (N : ℝ) * |z.im| ≤ 1 * rho :=
        mul_le_mul hfreq1 hz (abs_nonneg z.im) zero_le_one
      _ = rho := one_mul rho

/-- The complete normalized one-coordinate average varies vertically by at
most `rho * exp rho`; normalization cancels the finite sum length exactly. -/
theorem norm_cmp89Eq245EntireAverageFactor_sub_realSlice_le
    {N : ℕ} (hN : 0 < N) {z : ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hz : |z.im| ≤ rho) :
    ‖cmp89Eq245EntireAverageFactor N z -
        cmp89Eq245EntireAverageFactor N (z.re : ℂ)‖ ≤
      rho * Real.exp rho := by
  rw [cmp89Eq245EntireAverageFactor, cmp89Eq245EntireAverageFactor,
    ← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
  calc
    ‖(N : ℂ)⁻¹‖ * ‖∑ r ∈ Finset.range N,
        (cmp89Eq245EntireAverageBase N z ^ r -
          cmp89Eq245EntireAverageBase N (z.re : ℂ) ^ r)‖ ≤
        ‖(N : ℂ)⁻¹‖ * ∑ r ∈ Finset.range N,
          ‖cmp89Eq245EntireAverageBase N z ^ r -
            cmp89Eq245EntireAverageBase N (z.re : ℂ) ^ r‖ := by
              gcongr
              exact norm_sum_le _ _
    _ ≤ ‖(N : ℂ)⁻¹‖ *
          ∑ _r ∈ Finset.range N, rho * Real.exp rho := by
            gcongr with r hr
            exact norm_cmp89Eq245EntireAverageBase_pow_sub_realSlice_le
              hN (Finset.mem_range.mp hr) hrho hz
    _ = rho * Real.exp rho := by
          have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
          simp [norm_inv, hNreal]

end

end YangMills.RG

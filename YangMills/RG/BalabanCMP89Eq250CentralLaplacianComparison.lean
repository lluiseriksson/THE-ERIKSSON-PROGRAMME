/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245ComplexSincDictionary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# PRE-VALIDATION: central Laplacian comparison below CMP89 (2.50)

The primary source is present, but this module's `.olean` has not yet been
materialized and its declarations have not yet been compiler-verified.

CMP89 (2.45) defines the fine-lattice symbol `Delta^xi`, while (2.49) uses
the unit-lattice symbol `Delta^1`.  The central alias in the positive
denominator estimate (2.50) requires a uniform positive lower bound on
`Delta^1(p) / Delta^xi(p)` for `|p_mu| <= pi`.

This module proves the explicit source-faithful comparison

`Delta^xi(p) <= (pi / 2)^2 * Delta^1(p)`

for `0 < xi <= 1`, and hence the reciprocal lower bound when the mass is
positive.  It does not yet combine this with the averaging-symbol lower bound,
sum the noncentral aliases, prove the full denominator estimate (2.50),
establish (2.51), or construct the uniform analytic strip.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- One coordinate of the scaled lattice-difference symbol in CMP89 (2.45). -/
def cmp89Eq245ScaledDifferenceNorm (xi p : ℝ) : ℝ :=
  ‖(Complex.exp (Complex.I * (-(xi * p) : ℂ)) - 1) / (xi : ℂ)‖

/-- One coordinate of the unit-lattice difference symbol in CMP89 (2.49). -/
def cmp89Eq249UnitDifferenceNorm (p : ℝ) : ℝ :=
  ‖Complex.exp (Complex.I * (-p : ℂ)) - 1‖

/-- The literal nonnegative fine-lattice symbol `Delta^xi` from CMP89
(2.45), with a real mass parameter. -/
def cmp89Eq245ScaledLaplacianSymbol
    (d : ℕ) (xi mass : ℝ) (p : Fin d → ℝ) : ℝ :=
  ∑ mu, cmp89Eq245ScaledDifferenceNorm xi (p mu) ^ 2 + mass ^ 2

/-- The literal nonnegative unit-lattice symbol `Delta^1` from CMP89
(2.49), with the same mass parameter. -/
def cmp89Eq249UnitLaplacianSymbol
    (d : ℕ) (mass : ℝ) (p : Fin d → ℝ) : ℝ :=
  ∑ mu, cmp89Eq249UnitDifferenceNorm (p mu) ^ 2 + mass ^ 2

/-- The scaled difference quotient is bounded above by the continuum
momentum, uniformly in the lattice spacing. -/
theorem cmp89Eq245ScaledDifferenceNorm_le_abs
    {xi p : ℝ} (hxi : 0 < xi) :
    cmp89Eq245ScaledDifferenceNorm xi p ≤ |p| := by
  have hraw :
      ‖Complex.exp (Complex.I * (-(xi * p) : ℂ)) - 1‖ ≤
        ‖-(xi * p)‖ := by
    convert Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(xi * p)) using 1
    all_goals norm_num
  rw [cmp89Eq245ScaledDifferenceNorm, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hxi]
  apply (div_le_iff₀ hxi).2
  calc
    ‖Complex.exp (Complex.I * (-(xi * p) : ℂ)) - 1‖ ≤
        ‖-(xi * p)‖ := hraw
    _ = |p| * xi := by
      rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hxi]
      ring

/-- Jordan's inequality gives the uniform lower comparison between continuum
momentum and the unit-lattice difference on the Brillouin interval. -/
theorem two_div_pi_mul_abs_le_cmp89Eq249UnitDifferenceNorm
    {p : ℝ} (hp : |p| ≤ Real.pi) :
    (2 / Real.pi) * |p| ≤ cmp89Eq249UnitDifferenceNorm p := by
  have hpHalf : |p / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    exact (div_le_div_iff_of_pos_right (show (0 : ℝ) < 2 by norm_num)).2 hp
  have hjordan := Real.mul_abs_le_abs_sin hpHalf
  rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at hjordan
  have hnorm :
      cmp89Eq249UnitDifferenceNorm p =
        2 * |Real.sin (p / 2)| := by
    rw [cmp89Eq249UnitDifferenceNorm]
    have h := Complex.norm_exp_I_mul_ofReal_sub_one (-p)
    rw [show Complex.exp (Complex.I * (-p : ℂ)) =
        Complex.exp (Complex.I * ((-p : ℝ) : ℂ)) by norm_num, h]
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_pos (show (0 : ℝ) < 2 by norm_num), neg_div,
      Real.sin_neg, abs_neg]
  rw [hnorm]
  linarith

/-- Coordinatewise comparison used to pass from the scaled to the unit
lattice symbol in the central alias of (2.50). -/
theorem cmp89Eq245ScaledDifferenceNorm_le_pi_div_two_mul_unit
    {xi p : ℝ} (hxi : 0 < xi) (hp : |p| ≤ Real.pi) :
    cmp89Eq245ScaledDifferenceNorm xi p ≤
      (Real.pi / 2) * cmp89Eq249UnitDifferenceNorm p := by
  have hscaled := cmp89Eq245ScaledDifferenceNorm_le_abs (xi := xi) (p := p) hxi
  have hunit := two_div_pi_mul_abs_le_cmp89Eq249UnitDifferenceNorm hp
  have hmul := mul_le_mul_of_nonneg_left hunit Real.pi_div_two_pos.le
  calc
    cmp89Eq245ScaledDifferenceNorm xi p ≤ |p| := hscaled
    _ = (Real.pi / 2) * ((2 / Real.pi) * |p|) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ (Real.pi / 2) * cmp89Eq249UnitDifferenceNorm p := hmul

/-- The complete scaled symbol is at most `(pi/2)^2` times the unit symbol,
uniformly in dimension and in the RG scale. -/
theorem cmp89Eq245ScaledLaplacianSymbol_le_pi_sq_mul_unit
    {d : ℕ} {xi mass : ℝ} {p : Fin d → ℝ}
    (hxi : 0 < xi) (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq245ScaledLaplacianSymbol d xi mass p ≤
      (Real.pi / 2) ^ 2 * cmp89Eq249UnitLaplacianSymbol d mass p := by
  have hc0 : 0 ≤ Real.pi / 2 := Real.pi_div_two_pos.le
  have hc1 : 1 ≤ (Real.pi / 2) ^ 2 := by
    exact one_le_pow₀ Real.one_le_pi_div_two
  have hsum :
      (∑ mu, cmp89Eq245ScaledDifferenceNorm xi (p mu) ^ 2) ≤
        (Real.pi / 2) ^ 2 *
          ∑ mu, cmp89Eq249UnitDifferenceNorm (p mu) ^ 2 := by
    calc
      (∑ mu, cmp89Eq245ScaledDifferenceNorm xi (p mu) ^ 2) ≤
          ∑ mu, ((Real.pi / 2) *
            cmp89Eq249UnitDifferenceNorm (p mu)) ^ 2 := by
        apply Finset.sum_le_sum
        intro mu _
        exact (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg hc0 (norm_nonneg _))).2
            (cmp89Eq245ScaledDifferenceNorm_le_pi_div_two_mul_unit
              hxi (hp mu))
      _ = (Real.pi / 2) ^ 2 *
          ∑ mu, cmp89Eq249UnitDifferenceNorm (p mu) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro mu _
        ring
  rw [cmp89Eq245ScaledLaplacianSymbol,
    cmp89Eq249UnitLaplacianSymbol, mul_add]
  exact add_le_add hsum (by
    simpa using mul_le_mul_of_nonneg_right hc1 (sq_nonneg mass))

/-- Reciprocal form of the central Laplacian comparison.  Positive mass is
the only input needed to make the quotient literal rather than `0 / 0`. -/
theorem inv_pi_div_two_sq_le_cmp89Eq249_unit_div_scaled
    {d : ℕ} {xi mass : ℝ} {p : Fin d → ℝ}
    (hxi : 0 < xi) (hmass : 0 < mass)
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    ((Real.pi / 2) ^ 2)⁻¹ ≤
      cmp89Eq249UnitLaplacianSymbol d mass p /
        cmp89Eq245ScaledLaplacianSymbol d xi mass p := by
  have hscaledPos :
      0 < cmp89Eq245ScaledLaplacianSymbol d xi mass p := by
    rw [cmp89Eq245ScaledLaplacianSymbol]
    exact add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (pow_pos hmass 2)
  have hcPos : 0 < (Real.pi / 2) ^ 2 :=
    pow_pos Real.pi_div_two_pos 2
  apply (le_div_iff₀ hscaledPos).2
  rw [inv_mul_le_iff₀ hcPos]
  exact cmp89Eq245ScaledLaplacianSymbol_le_pi_sq_mul_unit hxi hp

end

end YangMills.RG

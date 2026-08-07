/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic

/-!
# PRE-VALIDATION: the real sinc amplitude below CMP89 (2.45)

The primary source is present, but this module's `.olean` has not yet been
materialized and its declarations have not yet been compiler-verified.

CMP89 (2.45), printed p. 584, writes the zero-background averaging symbol as
a product of one-dimensional exponential quotients at lattice spacing
`xi = L^(-j)`.  On the real Brillouin cube `|p_mu| <= pi`, the norm of each
quotient is the corresponding quotient of sinc amplitudes.  The elementary
lower bound `2 / pi` per coordinate is the source input used in the positive
denominator estimate (2.50).

This module proves the real sinc-amplitude bound, including the literal source
specialization `xi = ((L : R)^j)^(-1)`.  It does not yet prove the equality
between that amplitude and the norm of the complex exponential quotient in
(2.45), compare the two Laplacian symbols, prove the full denominator bound
(2.50), establish the summability estimate (2.51), or construct the uniform
complex analytic strip.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The real one-coordinate amplitude of the averaging quotient in CMP89
(2.45), written with the removable singularities filled by `Real.sinc`. -/
def cmp89Eq245SincAverageFactor (xi p : ℝ) : ℝ :=
  Real.sinc (p / 2) / Real.sinc (xi * p / 2)

/-- The product amplitude of the CMP89 (2.45) averaging symbol in dimension
`d`. -/
def cmp89Eq245SincAverageAmplitude
    (d : ℕ) (xi : ℝ) (p : Fin d → ℝ) : ℝ :=
  ∏ mu, cmp89Eq245SincAverageFactor xi (p mu)

/-- On the half-period interval, the absolute sinc amplitude is uniformly at
least `2 / pi`. -/
theorem two_div_pi_le_abs_sinc_of_abs_le_pi_div_two
    {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    2 / Real.pi ≤ |Real.sinc x| := by
  by_cases hx0 : x = 0
  · subst x
    simp only [Real.sinc_zero, abs_one]
    exact (div_le_one Real.pi_pos).2 Real.two_le_pi
  · rw [Real.sinc_of_ne_zero hx0, abs_div]
    exact (le_div_iff₀ (abs_pos.mpr hx0)).2
      (Real.mul_abs_le_abs_sin hx)

/-- Every real one-coordinate source factor has amplitude at least `2 / pi`
when `0 < xi ≤ 1` and the momentum lies in the Brillouin interval. -/
theorem two_div_pi_le_abs_cmp89Eq245SincAverageFactor
    {xi p : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hp : |p| ≤ Real.pi) :
    2 / Real.pi ≤ |cmp89Eq245SincAverageFactor xi p| := by
  have hp_half : |p / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    exact (div_le_div_iff_of_pos_right (show (0 : ℝ) < 2 by norm_num)).2 hp
  have hscaled : |xi * p / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hxi,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    apply (div_le_div_iff_of_pos_right (show (0 : ℝ) < 2 by norm_num)).2
    calc
      xi * |p| ≤ 1 * |p| :=
        mul_le_mul_of_nonneg_right hxi1 (abs_nonneg p)
      _ ≤ Real.pi := by simpa using hp
  have hnum := two_div_pi_le_abs_sinc_of_abs_le_pi_div_two hp_half
  have hdenLower :=
    two_div_pi_le_abs_sinc_of_abs_le_pi_div_two hscaled
  have htwoPi : 0 < 2 / Real.pi := div_pos (by norm_num) Real.pi_pos
  have hdenPos : 0 < |Real.sinc (xi * p / 2)| :=
    htwoPi.trans_le hdenLower
  rw [cmp89Eq245SincAverageFactor, abs_div]
  apply (le_div_iff₀ hdenPos).2
  calc
    (2 / Real.pi) * |Real.sinc (xi * p / 2)| ≤
        (2 / Real.pi) * 1 :=
      mul_le_mul_of_nonneg_left
        (Real.abs_sinc_le_one (xi * p / 2)) htwoPi.le
    _ = 2 / Real.pi := mul_one _
    _ ≤ |Real.sinc (p / 2)| := hnum

/-- The full `d`-dimensional sinc amplitude in CMP89 (2.45) is uniformly
bounded below by `(2 / pi)^d`, independently of the RG scale. -/
theorem pow_two_div_pi_le_abs_cmp89Eq245SincAverageAmplitude
    {d : ℕ} {xi : ℝ} {p : Fin d → ℝ}
    (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    (2 / Real.pi) ^ d ≤
      |cmp89Eq245SincAverageAmplitude d xi p| := by
  rw [cmp89Eq245SincAverageAmplitude, Finset.abs_prod]
  have hnonneg : 0 ≤ 2 / Real.pi :=
    (div_pos (by norm_num) Real.pi_pos).le
  simpa using Finset.prod_le_prod
    (fun _mu _hmu => hnonneg)
    (fun mu _hmu =>
      two_div_pi_le_abs_cmp89Eq245SincAverageFactor
        hxi hxi1 (hp mu))

/-- The literal CMP89 scale `xi = L^(-j)` lies in `(0, 1]` for every nonzero
natural block size. -/
theorem cmp89Eq245_inverseScale_mem_Ioc
    (L j : ℕ) [NeZero L] :
    ((0 : ℝ) < ((L : ℝ) ^ j)⁻¹) ∧ (((L : ℝ) ^ j)⁻¹ ≤ 1) := by
  have hL : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne L))
  have hpow : (1 : ℝ) ≤ (L : ℝ) ^ j := one_le_pow₀ hL
  exact ⟨inv_pos.mpr (zero_lt_one.trans_le hpow),
    inv_le_one_of_one_le₀ hpow⟩

/-- Source-specialized uniform lower bound for the sinc amplitude of (2.45)
at `xi = L^(-j)`. -/
theorem pow_two_div_pi_le_abs_cmp89Eq245SincAverageAmplitude_inverseScale
    {d L j : ℕ} [NeZero L] {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    (2 / Real.pi) ^ d ≤
      |cmp89Eq245SincAverageAmplitude d (((L : ℝ) ^ j)⁻¹) p| := by
  obtain ⟨hxi, hxi1⟩ := cmp89Eq245_inverseScale_mem_Ioc L j
  exact pow_two_div_pi_le_abs_cmp89Eq245SincAverageAmplitude hxi hxi1 hp

end

end YangMills.RG

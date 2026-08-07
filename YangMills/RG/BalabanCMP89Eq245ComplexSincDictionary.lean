/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245SincAverageLower
import Mathlib.Analysis.Complex.Trigonometric

/-!
# PRE-VALIDATION: complex-to-sinc dictionary for CMP89 (2.45)

The primary source is present, but this module's `.olean` has not yet been
materialized and its declarations have not yet been compiler-verified.

CMP89 (2.45), printed p. 584, defines each coordinate of the averaging symbol
as the quotient of two exponential difference quotients.  This module fills
their removable singularities at zero, proves the exact norm dictionary to
the real sinc amplitude already sealed in
`BalabanCMP89Eq245SincAverageLower`, and transports its `(2 / pi)^d` lower
bound to the complex product.

The separate equality with the literal printed quotient is stated only where
its complex denominator is nonzero.  This module does not yet prove that
nonvanishing from the Brillouin hypotheses, compare the two Laplacian symbols,
prove the full denominator estimate (2.50), establish (2.51), or construct the
uniform analytic strip.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The exponential difference quotient with its removable value at zero.
The phase convention is the literal `exp (-i x)` convention of CMP89
(2.45). -/
def cmp89Eq245RemovableExpSlope (x : ℝ) : ℂ :=
  if x = 0 then 1 else
    (Complex.exp (Complex.I * (-x : ℂ)) - 1) / (x : ℂ)

/-- The removable complex one-coordinate averaging factor of CMP89 (2.45). -/
def cmp89Eq245ComplexAverageFactor (xi p : ℝ) : ℂ :=
  cmp89Eq245RemovableExpSlope p /
    cmp89Eq245RemovableExpSlope (xi * p)

/-- The literal printed exponential quotient in CMP89 (2.45), with the
denominator difference divided by `xi`. -/
def cmp89Eq245LiteralComplexAverageFactor (xi p : ℝ) : ℂ :=
  (Complex.exp (Complex.I * (-p : ℂ)) - 1) /
    ((Complex.exp (Complex.I * (-(xi * p) : ℂ)) - 1) / (xi : ℂ))

/-- The removable exponential slope has exactly the absolute sinc amplitude. -/
theorem norm_cmp89Eq245RemovableExpSlope (x : ℝ) :
    ‖cmp89Eq245RemovableExpSlope x‖ = |Real.sinc (x / 2)| := by
  by_cases hx : x = 0
  · subst x
    simp [cmp89Eq245RemovableExpSlope]
  · have hxhalf : x / 2 ≠ 0 := div_ne_zero hx (by norm_num)
    rw [cmp89Eq245RemovableExpSlope, if_neg hx, norm_div,
      Complex.norm_exp_I_mul_ofReal_sub_one,
      Real.sinc_of_ne_zero hxhalf]
    simp only [Real.norm_eq_abs, Real.sin_neg, neg_div, abs_neg,
      abs_div, abs_mul, abs_ofNat, Complex.norm_real]
    field_simp [abs_ne_zero.mpr hx]
    ring

/-- Exact norm dictionary from the removable complex factor to the real sinc
factor used in the preceding source brick. -/
theorem norm_cmp89Eq245ComplexAverageFactor (xi p : ℝ) :
    ‖cmp89Eq245ComplexAverageFactor xi p‖ =
      |cmp89Eq245SincAverageFactor xi p| := by
  rw [cmp89Eq245ComplexAverageFactor, norm_div,
    norm_cmp89Eq245RemovableExpSlope,
    norm_cmp89Eq245RemovableExpSlope,
    cmp89Eq245SincAverageFactor, abs_div]

/-- Away from the removable singularity and a zero printed denominator, the
complex factor is literally the exponential quotient printed in (2.45). -/
theorem cmp89Eq245ComplexAverageFactor_eq_literal
    {xi p : ℝ} (hxi : xi ≠ 0) (hp : p ≠ 0)
    (hden : Complex.exp (Complex.I * (-(xi * p) : ℂ)) - 1 ≠ 0) :
    cmp89Eq245ComplexAverageFactor xi p =
      cmp89Eq245LiteralComplexAverageFactor xi p := by
  rw [cmp89Eq245ComplexAverageFactor, cmp89Eq245RemovableExpSlope,
    if_neg hp, if_neg (mul_ne_zero hxi hp),
    cmp89Eq245LiteralComplexAverageFactor]
  field_simp
  ring

/-- The product of the removable complex factors in dimension `d`. -/
def cmp89Eq245ComplexAverageAmplitude
    (d : ℕ) (xi : ℝ) (p : Fin d → ℝ) : ℂ :=
  ∏ mu, cmp89Eq245ComplexAverageFactor xi (p mu)

/-- Product-level exact norm dictionary for the CMP89 (2.45) symbol. -/
theorem norm_cmp89Eq245ComplexAverageAmplitude
    (d : ℕ) (xi : ℝ) (p : Fin d → ℝ) :
    ‖cmp89Eq245ComplexAverageAmplitude d xi p‖ =
      |cmp89Eq245SincAverageAmplitude d xi p| := by
  rw [cmp89Eq245ComplexAverageAmplitude, cmp89Eq245SincAverageAmplitude,
    norm_prod, Finset.abs_prod]
  exact Finset.prod_congr rfl fun mu _ =>
    norm_cmp89Eq245ComplexAverageFactor xi (p mu)

/-- Source-specialized complex lower bound obtained through the exact norm
dictionary, uniformly in the RG scale. -/
theorem pow_two_div_pi_le_norm_cmp89Eq245ComplexAverageAmplitude_inverseScale
    {d L j : ℕ} [NeZero L] {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    (2 / Real.pi) ^ d ≤
      ‖cmp89Eq245ComplexAverageAmplitude d (((L : ℝ) ^ j)⁻¹) p‖ := by
  rw [norm_cmp89Eq245ComplexAverageAmplitude]
  exact pow_two_div_pi_le_abs_cmp89Eq245SincAverageAmplitude_inverseScale hp

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireAverageAmplitudeVariation
import YangMills.RG.BalabanCMP89Eq248EntireFourierSymbols

/-!
# Vertical variation of the entire CMP89 fine-lattice symbol

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

This module compares the entire fine-lattice symbol `Delta^xi(z)` with the
point on the real slice having the same real part.  The division by `xi` in
one lattice difference is cancelled against the `xi` in its exponential
variation.  The remaining bound keeps the real momentum visible; it is not
replaced by the cardinality or diameter of the reciprocal-alias fibre.

This is deliberately below the stabilized denominator.  No reciprocal of a
fine symbol is taken, the zero alias is not required to be nonvanishing, and
no alias sum, strip radius, `B0`, contour shift or regional-Green estimate is
claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Exponent in one coordinate of the entire scaled lattice difference. -/
def cmp89Eq245EntireScaledDifferenceExponent (xi : ℝ) (z : ℂ) : ℂ :=
  Complex.I * (-((xi : ℂ) * z))

/-- Exact vertical displacement of the scaled-difference exponent. -/
theorem norm_cmp89Eq245EntireScaledDifferenceExponent_sub_realSlice_eq
    (xi : ℝ) (z : ℂ) :
    ‖cmp89Eq245EntireScaledDifferenceExponent xi z -
        cmp89Eq245EntireScaledDifferenceExponent xi (z.re : ℂ)‖ =
      |xi| * |z.im| := by
  have hz : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [show
      cmp89Eq245EntireScaledDifferenceExponent xi z -
          cmp89Eq245EntireScaledDifferenceExponent xi (z.re : ℂ) =
        -(Complex.I * (xi : ℂ)) * (z - (z.re : ℂ)) by
      unfold cmp89Eq245EntireScaledDifferenceExponent
      ring]
  simp [hz, Real.norm_eq_abs]

/-- A single scaled lattice difference varies vertically by at most
`rho*exp(rho)`, uniformly for `0 < xi <= 1`. -/
theorem norm_cmp89Eq245EntireScaledDifference_sub_realSlice_le
    {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    {z : ℂ} {rho : ℝ} (hrho : 0 ≤ rho) (hz : |z.im| ≤ rho) :
    ‖cmp89Eq245EntireScaledDifference xi z -
        cmp89Eq245EntireScaledDifference xi (z.re : ℂ)‖ ≤
      rho * Real.exp rho := by
  have hscaledRho : 0 ≤ xi * rho := mul_nonneg hxi.le hrho
  have hscaledRhoLe : xi * rho ≤ rho := by nlinarith
  have hexp :
      ‖Complex.exp (cmp89Eq245EntireScaledDifferenceExponent xi z) -
          Complex.exp
            (cmp89Eq245EntireScaledDifferenceExponent xi (z.re : ℂ))‖ ≤
        (xi * rho) * Real.exp (xi * rho) := by
    apply norm_complex_exp_sub_exp_le_of_norm_sub_le hscaledRho
    · rw [Complex.norm_exp]
      simp [cmp89Eq245EntireScaledDifferenceExponent, Complex.mul_re]
    · rw [norm_cmp89Eq245EntireScaledDifferenceExponent_sub_realSlice_eq,
        abs_of_pos hxi]
      exact mul_le_mul_of_nonneg_left hz hxi.le
  change
    ‖(Complex.exp (cmp89Eq245EntireScaledDifferenceExponent xi z) - 1) /
          (xi : ℂ) -
        (Complex.exp
            (cmp89Eq245EntireScaledDifferenceExponent xi (z.re : ℂ)) - 1) /
          (xi : ℂ)‖ ≤ _
  rw [← sub_div,
    show
      (Complex.exp (cmp89Eq245EntireScaledDifferenceExponent xi z) - 1) -
          (Complex.exp
            (cmp89Eq245EntireScaledDifferenceExponent xi (z.re : ℂ)) - 1) =
        Complex.exp (cmp89Eq245EntireScaledDifferenceExponent xi z) -
          Complex.exp
            (cmp89Eq245EntireScaledDifferenceExponent xi (z.re : ℂ)) by
      ring,
    norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxi]
  calc
    ‖Complex.exp (cmp89Eq245EntireScaledDifferenceExponent xi z) -
        Complex.exp
          (cmp89Eq245EntireScaledDifferenceExponent xi (z.re : ℂ))‖ / xi ≤
        ((xi * rho) * Real.exp (xi * rho)) / xi :=
      div_le_div_of_nonneg_right hexp hxi.le
    _ = rho * Real.exp (xi * rho) := by field_simp
    _ ≤ rho * Real.exp rho := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hscaledRhoLe) hrho

/-- On the real slice, the entire difference has the literal physical norm. -/
theorem norm_cmp89Eq245EntireScaledDifference_ofReal_eq
    (xi q : ℝ) :
    ‖cmp89Eq245EntireScaledDifference xi (q : ℂ)‖ =
      cmp89Eq245ScaledDifferenceNorm xi q := by
  simp only [cmp89Eq245EntireScaledDifference,
    cmp89Eq245ScaledDifferenceNorm]

/-- Product-rule estimate with both factor budgets visible. -/
theorem norm_mul_sub_mul_le_eps_mul_two_mul_add
    {x y x0 y0 : ℂ} {eps R : ℝ}
    (heps : 0 ≤ eps) (hR : 0 ≤ R)
    (hx : ‖x - x0‖ ≤ eps) (hy : ‖y - y0‖ ≤ eps)
    (hx0 : ‖x0‖ ≤ R) (hy0 : ‖y0‖ ≤ R) :
    ‖x * y - x0 * y0‖ ≤ eps * (2 * R + eps) := by
  have hyNorm : ‖y‖ ≤ R + eps := by
    calc
      ‖y‖ = ‖(y - y0) + y0‖ := by ring_nf
      _ ≤ ‖y - y0‖ + ‖y0‖ := norm_add_le _ _
      _ ≤ eps + R := add_le_add hy hy0
      _ = R + eps := add_comm _ _
  rw [show x * y - x0 * y0 = (x - x0) * y + x0 * (y - y0) by ring]
  calc
    ‖(x - x0) * y + x0 * (y - y0)‖ ≤
        ‖x - x0‖ * ‖y‖ + ‖x0‖ * ‖y - y0‖ := by
      simpa only [norm_mul] using
        (norm_add_le ((x - x0) * y) (x0 * (y - y0)))
    _ ≤ eps * (R + eps) + R * eps := by gcongr
    _ = eps * (2 * R + eps) := by ring

/-- One coordinate of the opposite-momentum Laplacian pairing retains the
real momentum rather than paying an alias-cardinality bound. -/
theorem norm_cmp89Eq245EntireScaledDifference_pair_sub_realSlice_le
    {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    {z : ℂ} {rho : ℝ} (hrho : 0 ≤ rho) (hz : |z.im| ≤ rho) :
    ‖cmp89Eq245EntireScaledDifference xi z *
          cmp89Eq245EntireScaledDifference xi (-z) -
        cmp89Eq245EntireScaledDifference xi (z.re : ℂ) *
          cmp89Eq245EntireScaledDifference xi (-(z.re : ℂ))‖ ≤
      (rho * Real.exp rho) *
        (2 * |z.re| + rho * Real.exp rho) := by
  apply norm_mul_sub_mul_le_eps_mul_two_mul_add
      (mul_nonneg hrho (Real.exp_pos rho).le) (abs_nonneg z.re)
  · exact norm_cmp89Eq245EntireScaledDifference_sub_realSlice_le
      hxi hxi1 hrho hz
  · simpa using
      (norm_cmp89Eq245EntireScaledDifference_sub_realSlice_le
        hxi hxi1 hrho (z := -z) (by simpa using hz))
  · rw [norm_cmp89Eq245EntireScaledDifference_ofReal_eq]
    exact cmp89Eq245ScaledDifferenceNorm_le_abs hxi
  · have hneg :=
      cmp89Eq245ScaledDifferenceNorm_le_abs (xi := xi) (p := -z.re) hxi
    rw [← norm_cmp89Eq245EntireScaledDifference_ofReal_eq] at hneg
    simpa using hneg

/-- Explicit scale-uniform vertical budget for the complete entire
fine-lattice symbol. -/
def cmp89Eq245EntireScaledLaplacianVerticalBudget
    (d : ℕ) (rho : ℝ) (z : Fin d → ℂ) : ℝ :=
  ∑ mu, (rho * Real.exp rho) *
    (2 * |(z mu).re| + rho * Real.exp rho)

/-- The entire fine-lattice symbol differs from its matching real slice by
the sum of the coordinatewise budgets.  The mass term cancels exactly. -/
theorem norm_cmp89Eq245EntireScaledLaplacianSymbol_sub_realSlice_le
    {d : ℕ} {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    {mass : ℝ} {z : Fin d → ℂ} {rho : ℝ}
    (hrho : 0 ≤ rho) (hz : ∀ mu, |(z mu).im| ≤ rho) :
    ‖cmp89Eq245EntireScaledLaplacianSymbol d xi mass z -
        cmp89Eq245EntireScaledLaplacianSymbol d xi mass
          (cmp89Eq245ComplexMomentumRealSlice z)‖ ≤
      cmp89Eq245EntireScaledLaplacianVerticalBudget d rho z := by
  have hcancel :
      cmp89Eq245EntireScaledLaplacianSymbol d xi mass z -
          cmp89Eq245EntireScaledLaplacianSymbol d xi mass
            (cmp89Eq245ComplexMomentumRealSlice z) =
        ∑ mu,
          (cmp89Eq245EntireScaledDifference xi (z mu) *
              cmp89Eq245EntireScaledDifference xi (-z mu) -
            cmp89Eq245EntireScaledDifference xi ((z mu).re : ℂ) *
              cmp89Eq245EntireScaledDifference xi (-((z mu).re : ℂ))) := by
    rw [cmp89Eq245EntireScaledLaplacianSymbol,
      cmp89Eq245EntireScaledLaplacianSymbol]
    simp only [cmp89Eq245ComplexMomentumRealSlice]
    calc
      (∑ mu, cmp89Eq245EntireScaledDifference xi (z mu) *
            cmp89Eq245EntireScaledDifference xi (-z mu)) + (mass : ℂ) ^ 2 -
          ((∑ mu, cmp89Eq245EntireScaledDifference xi ((z mu).re : ℂ) *
              cmp89Eq245EntireScaledDifference xi (-((z mu).re : ℂ))) +
            (mass : ℂ) ^ 2) =
        (∑ mu, cmp89Eq245EntireScaledDifference xi (z mu) *
            cmp89Eq245EntireScaledDifference xi (-z mu)) -
          ∑ mu, cmp89Eq245EntireScaledDifference xi ((z mu).re : ℂ) *
            cmp89Eq245EntireScaledDifference xi (-((z mu).re : ℂ)) := by ring
      _ = ∑ mu,
          (cmp89Eq245EntireScaledDifference xi (z mu) *
              cmp89Eq245EntireScaledDifference xi (-z mu) -
            cmp89Eq245EntireScaledDifference xi ((z mu).re : ℂ) *
              cmp89Eq245EntireScaledDifference xi (-((z mu).re : ℂ))) := by
        rw [Finset.sum_sub_distrib]
  rw [hcancel]
  calc
    ‖∑ mu,
        (cmp89Eq245EntireScaledDifference xi (z mu) *
            cmp89Eq245EntireScaledDifference xi (-z mu) -
          cmp89Eq245EntireScaledDifference xi ((z mu).re : ℂ) *
            cmp89Eq245EntireScaledDifference xi (-((z mu).re : ℂ)))‖ ≤
        ∑ mu, ‖cmp89Eq245EntireScaledDifference xi (z mu) *
            cmp89Eq245EntireScaledDifference xi (-z mu) -
          cmp89Eq245EntireScaledDifference xi ((z mu).re : ℂ) *
            cmp89Eq245EntireScaledDifference xi (-((z mu).re : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ cmp89Eq245EntireScaledLaplacianVerticalBudget d rho z := by
      rw [cmp89Eq245EntireScaledLaplacianVerticalBudget]
      exact Finset.sum_le_sum fun mu _ =>
        norm_cmp89Eq245EntireScaledDifference_pair_sub_realSlice_le
          hxi hxi1 hrho (hz mu)

end

end YangMills.RG

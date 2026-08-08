/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251AliasAmplitudeUpper

/-!
# PRE-VALIDATION: entire averaging amplitude below CMP89 (2.51)

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

CMP89 (2.45), printed p. 584, uses the averaging quotient at the physical
inverse integer scale `xi = 1 / N`.  Dividing exponential differences is not
a suitable complex continuation: its apparent poles must first be removed.
At the physical scale the quotient is exactly a finite geometric average.
This module therefore constructs that finite sum as an entire function and
proves its exact equality, on every printed real alias, with the already
sealed removable real-slice symbol.

The construction does not complexify a squared norm.  The later complex
denominator must use the holomorphic pairing `u(z) * u(-z)`, whose real slice
is the required squared amplitude.  No uniform analytic strip, complex
denominator lower bound, contour displacement, or regional-Green estimate is
claimed here.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The exponential ratio occurring in the finite geometric representation
of the one-coordinate averaging symbol at inverse integer scale `1 / N`. -/
def cmp89Eq245EntireAverageBase (N : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (-((N : ℂ)⁻¹ * z)))

/-- The pole-free, entire one-coordinate continuation of CMP89 (2.45) at the
physical scale `xi = 1 / N`. -/
def cmp89Eq245EntireAverageFactor (N : ℕ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ *
    ∑ r ∈ Finset.range N, cmp89Eq245EntireAverageBase N z ^ r

/-- The finite geometric averaging factor is entire. -/
@[fun_prop]
theorem differentiable_cmp89Eq245EntireAverageFactor (N : ℕ) :
    Differentiable ℂ (cmp89Eq245EntireAverageFactor N) := by
  unfold cmp89Eq245EntireAverageFactor cmp89Eq245EntireAverageBase
  fun_prop

/-- Product of the entire coordinate factors in dimension `d`. -/
def cmp89Eq245EntireAverageAmplitude
    (d N : ℕ) (z : Fin d → ℂ) : ℂ :=
  ∏ mu, cmp89Eq245EntireAverageFactor N (z mu)

/-- The finite-dimensional averaging amplitude is entire jointly in all
momentum coordinates. -/
theorem differentiable_cmp89Eq245EntireAverageAmplitude (d N : ℕ) :
    Differentiable ℂ (cmp89Eq245EntireAverageAmplitude d N) := by
  unfold cmp89Eq245EntireAverageAmplitude
  fun_prop

/-- At a real momentum where the printed denominator is nonzero, the finite
geometric continuation is exactly the removable factor already used in the
real-variable proof of (2.51). -/
theorem cmp89Eq245EntireAverageFactor_ofReal_eq
    {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hden : cmp89Eq245RemovableExpSlope ((N : ℝ)⁻¹ * q) ≠ 0) :
    cmp89Eq245EntireAverageFactor N (q : ℂ) =
      cmp89Eq245ComplexAverageFactor (N : ℝ)⁻¹ q := by
  by_cases hq : q = 0
  · subst q
    simp [cmp89Eq245EntireAverageFactor, cmp89Eq245EntireAverageBase,
      cmp89Eq245ComplexAverageFactor, cmp89Eq245RemovableExpSlope,
      Nat.ne_of_gt hN]
  · have hNnat : N ≠ 0 := Nat.ne_of_gt hN
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hNnat
    have hNcomplex : (N : ℂ) ≠ 0 := by exact_mod_cast hNnat
    have hxi : (N : ℝ)⁻¹ ≠ 0 := inv_ne_zero hNreal
    have hscaled : (N : ℝ)⁻¹ * q ≠ 0 := mul_ne_zero hxi hq
    let x : ℂ := cmp89Eq245EntireAverageBase N (q : ℂ)
    have hx_exp :
        x = Complex.exp
          (Complex.I * (-(((N : ℝ)⁻¹ * q : ℝ) : ℂ))) := by
      simp [x, cmp89Eq245EntireAverageBase]
    have hx_ne_one : x ≠ 1 := by
      intro hx
      apply hden
      rw [cmp89Eq245RemovableExpSlope, if_neg hscaled]
      rw [← hx_exp, hx]
      simp
    have hx_pow :
        x ^ N = Complex.exp (Complex.I * (-(q : ℂ))) := by
      rw [hx_exp, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp [hNreal]
    have hx_exp_mul :
        Complex.exp
            (Complex.I *
              (-((↑((N : ℝ)⁻¹) : ℂ) * (q : ℂ)))) = x := by
      calc
        _ = Complex.exp
            (Complex.I * (-(((N : ℝ)⁻¹ * q : ℝ) : ℂ))) := by
              congr 1
              push_cast
              ring
        _ = x := hx_exp.symm
    rw [cmp89Eq245EntireAverageFactor,
      cmp89Eq245ComplexAverageFactor_eq_literal hxi hq,
      cmp89Eq245LiteralComplexAverageFactor,
      show cmp89Eq245EntireAverageBase N (q : ℂ) = x by rfl,
      geom_sum_eq hx_ne_one N, hx_pow, hx_exp_mul]
    push_cast
    field_simp [hNreal, hNcomplex, sub_ne_zero.mpr hx_ne_one]

/-- Exact real-slice dictionary on every alias printed in CMP89 (2.45).
The expanded-zone sinc lower bound supplies the nonvanishing needed to use
the geometric quotient, so no global nonvanishing assumption is hidden. -/
theorem cmp89Eq245EntireAverageAmplitude_ofReal_scaled_alias_eq
    {d N : ℕ} (hN : 0 < N) {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq245EntireAverageAmplitude d N
        (fun mu => (p mu + 2 * Real.pi * (m mu : ℝ) : ℂ)) =
      cmp89Eq245ComplexAverageAmplitude d (N : ℝ)⁻¹
        (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) := by
  rw [cmp89Eq245EntireAverageAmplitude,
    cmp89Eq245ComplexAverageAmplitude]
  apply Finset.prod_congr rfl
  intro mu hmu
  have hmi : m mu ∈ cmp89Eq245CenteredAliasIntegers N := by
    rw [cmp89Eq245CenteredAliasVectors, Fintype.mem_piFinset] at hm
    exact hm mu
  have hsinc := one_div_three_pi_le_abs_sinc_scaled_alias
    hN hmi (hp mu)
  have hsincPos :
      0 < |Real.sinc (((N : ℝ)⁻¹ *
        (p mu + 2 * Real.pi * (m mu : ℝ))) / 2)| := by
    exact (div_pos (by norm_num) (mul_pos (by norm_num) Real.pi_pos)).trans_le
      hsinc
  have hdenNorm :
      0 < ‖cmp89Eq245RemovableExpSlope
        ((N : ℝ)⁻¹ * (p mu + 2 * Real.pi * (m mu : ℝ)))‖ := by
    rw [norm_cmp89Eq245RemovableExpSlope]
    exact hsincPos
  exact cmp89Eq245EntireAverageFactor_ofReal_eq hN
    (norm_pos_iff.mp hdenNorm)

end

end YangMills.RG

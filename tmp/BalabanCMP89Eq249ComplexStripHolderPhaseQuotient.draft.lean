/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireAverageVerticalVariation
import YangMills.RG.BalabanCMP89Eq249NoncentralComplexGap
import YangMills.RG.BalabanCMP89Eq251ComplexContourPhase
import YangMills.RG.BalabanCMP89MassZeroCentralFineSymbolNonvanishing

/-!
# PRE-VALIDATION: complex-strip Holder phase quotient

This source is a static H2a draft.  Its `.olean` has not been materialized and
none of the declarations below has been compiler-verified.

The result keeps the Holder cancellation at general `0 <= alpha <= 1` after a
full coordinate-strip displacement.  The real phase quotient is reused from
CMP89 (2.49), while the vertical change is produced from the literal imaginary
part of the same phase.  The final correction

`rho * exp (2*rho*||u||_2) * ||u||_2^(1-alpha)`

is visible.  No local-pair hypothesis, CMP95 seminorm, complete noncentral
quotient, alias sum, `B0`, window-15 producer or terminal field is supplied or
claimed here.  In particular the later replacement
`||u||_2^(1-alpha) <= 1` must be derived from the visually verified CMP95
(1.109) carrier, never accepted as a free premise.
-/

namespace YangMills.RG

noncomputable section

/-- The entire phase splits into its literal real and imaginary scalar phases.
This is an identity, not a strip estimate. -/
theorem cmp89Eq251EntirePhase_eq_real_add_I_imag_draft
    {d : ℕ} (z : Fin d → ℂ) (u : Fin d → ℝ) :
    cmp89Eq251EntirePhase z u =
      (cmp89Eq251Phase (fun mu => (z mu).re) u : ℂ) +
        Complex.I * (cmp89Eq251Phase (fun mu => (z mu).im) u : ℂ) := by
  apply Complex.ext
  · simp [cmp89Eq251EntirePhase, cmp89Eq251Phase, Complex.mul_re]
  · simp [cmp89Eq251EntirePhase, cmp89Eq251Phase, Complex.mul_im]

/-- On a four-dimensional coordinate strip, the imaginary scalar phase costs
at most `2*rho*||u||_2`.  The factor two is the exact `l1 <= 2*l2` conversion
already used by the complex-gap route. -/
theorem abs_cmp89Eq251Phase_le_two_mul_strip_draft
    {rho : ℝ} (hrho : 0 ≤ rho) {b : Fin 4 → ℝ}
    (hb : ∀ mu, |b mu| ≤ rho) (u : Fin 4 → ℝ) :
    |cmp89Eq251Phase b u| ≤
      2 * rho * cmp89Eq251EuclideanNorm u := by
  calc
    |cmp89Eq251Phase b u| = |∑ mu, b mu * u mu| := rfl
    _ ≤ ∑ mu, |b mu * u mu| := by
      simpa only [Finset.mem_univ, true_and] using
        (Finset.abs_sum_le_sum_abs
          (fun mu : Fin 4 => b mu * u mu) Finset.univ)
    _ = ∑ mu, |b mu| * |u mu| := by
      apply Finset.sum_congr rfl
      intro mu _
      rw [abs_mul]
    _ ≤ ∑ mu, rho * |u mu| := by
      exact Finset.sum_le_sum fun mu _ =>
        mul_le_mul_of_nonneg_right (hb mu) (abs_nonneg _)
    _ = rho * ∑ mu, |u mu| := by rw [Finset.mul_sum]
    _ ≤ rho * (2 * cmp89Eq251EuclideanNorm u) :=
      mul_le_mul_of_nonneg_left
        (sum_abs_le_two_mul_cmp89Eq251EuclideanNorm_fin_four u) hrho
    _ = 2 * rho * cmp89Eq251EuclideanNorm u := by ring

/-- The complex phase exponential differs from its real-slice exponential by
the explicit vertical-strip budget.  The real part is fixed to `q`; no family
of phase bounds is accepted. -/
theorem norm_exp_I_cmp89Eq251EntirePhase_sub_realPhase_le_draft
    {rho : ℝ} (hrho : 0 ≤ rho) {z : Fin 4 → ℂ} {q : Fin 4 → ℝ}
    (hreal : ∀ mu, (z mu).re = q mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) (u : Fin 4 → ℝ) :
    ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z u) -
        Complex.exp (Complex.I * (cmp89Eq251Phase q u : ℂ))‖ ≤
      (2 * rho * cmp89Eq251EuclideanNorm u) *
        Real.exp (2 * rho * cmp89Eq251EuclideanNorm u) := by
  let radius := 2 * rho * cmp89Eq251EuclideanNorm u
  have hradius : 0 ≤ radius := by
    dsimp [radius]
    positivity
  apply norm_complex_exp_sub_exp_le_of_norm_sub_le hradius
  · rw [Complex.norm_exp]
    simp
  · have hrealPhase :
        cmp89Eq251Phase (fun mu => (z mu).re) u =
          cmp89Eq251Phase q u := by
      unfold cmp89Eq251Phase
      apply Finset.sum_congr rfl
      intro mu _
      rw [hreal mu]
    rw [cmp89Eq251EntirePhase_eq_real_add_I_imag_draft, hrealPhase]
    have hrewrite :
        Complex.I *
              ((cmp89Eq251Phase q u : ℂ) + Complex.I *
                (cmp89Eq251Phase (fun mu => (z mu).im) u : ℂ)) -
            Complex.I * (cmp89Eq251Phase q u : ℂ) =
          -(cmp89Eq251Phase (fun mu => (z mu).im) u : ℂ) := by
      ring
    rw [hrewrite, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact abs_cmp89Eq251Phase_le_two_mul_strip_draft hrho himag u

/-- Global H2a estimate.  It needs no local-pair restriction: the residual
power `||u||_2^(1-alpha)` remains literal for H2b to consume from the concrete
CMP95 seminorm carrier. -/
theorem norm_cmp89Eq251_complexStripPhaseFactor_div_displacement_rpow_le_draft
    {alpha rho : ℝ} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hrho : 0 ≤ rho) {z : Fin 4 → ℂ} {q u : Fin 4 → ℝ}
    (hreal : ∀ mu, (z mu).re = q mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) (hu : u ≠ 0) :
    ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z u) - 1‖ /
        cmp89Eq251EuclideanNorm u ^ alpha ≤
      2 * Real.exp (2 * rho * cmp89Eq251EuclideanNorm u) *
        (cmp89Eq251EuclideanNorm q ^ alpha +
          rho * cmp89Eq251EuclideanNorm u ^ (1 - alpha)) := by
  let U := cmp89Eq251EuclideanNorm u
  let Q := cmp89Eq251EuclideanNorm q
  let radius := 2 * rho * U
  have hmomentum : 0 < cmp89Eq251MomentumSquare u :=
    cmp89Eq251MomentumSquare_pos_of_ne_zero hu
  have hU : 0 < U := by
    dsimp [U, cmp89Eq251EuclideanNorm]
    exact Real.sqrt_pos.2 hmomentum
  have hden : 0 < U ^ alpha := Real.rpow_pos_of_pos hU alpha
  have hradius : 0 ≤ radius := by
    dsimp [radius]
    positivity
  have hexpOne : 1 ≤ Real.exp radius := Real.one_le_exp hradius
  have hvertical :
      ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z u) -
          Complex.exp (Complex.I * (cmp89Eq251Phase q u : ℂ))‖ ≤
        radius * Real.exp radius := by
    simpa [radius, U] using
      norm_exp_I_cmp89Eq251EntirePhase_sub_realPhase_le_draft
        hrho hreal himag u
  have hrealPhase :
      ‖Complex.exp (Complex.I * (cmp89Eq251Phase q u : ℂ)) - 1‖ ≤
        2 * (Q ^ alpha * U ^ alpha) := by
    simpa [Q, U] using
      norm_cmp89Eq251_phaseFactor_le halpha0 halpha1 q u
  have hnumerator :
      ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z u) - 1‖ ≤
        radius * Real.exp radius + 2 * (Q ^ alpha * U ^ alpha) := by
    calc
      ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z u) - 1‖ ≤
          ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z u) -
              Complex.exp (Complex.I * (cmp89Eq251Phase q u : ℂ))‖ +
            ‖Complex.exp (Complex.I * (cmp89Eq251Phase q u : ℂ)) - 1‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le
            (Complex.exp (Complex.I * cmp89Eq251EntirePhase z u) -
              Complex.exp (Complex.I * (cmp89Eq251Phase q u : ℂ)))
            (Complex.exp (Complex.I * (cmp89Eq251Phase q u : ℂ)) - 1)
      _ ≤ radius * Real.exp radius + 2 * (Q ^ alpha * U ^ alpha) :=
        add_le_add hvertical hrealPhase
  apply (div_le_iff₀ hden).2
  refine hnumerator.trans ?_
  have hQpow : 0 ≤ Q ^ alpha := Real.rpow_nonneg
    (cmp89Eq251EuclideanNorm_nonneg q) alpha
  have hUpow : 0 ≤ U ^ alpha := Real.rpow_nonneg hU.le alpha
  have hProduct : U ^ (1 - alpha) * U ^ alpha = U := by
    rw [← Real.rpow_add hU]
    convert Real.rpow_one U using 1 <;> ring
  have hrealGrowth :
      2 * (Q ^ alpha * U ^ alpha) ≤
        2 * Real.exp radius * Q ^ alpha * U ^ alpha := by
    have hnonneg : 0 ≤ Q ^ alpha * U ^ alpha :=
      mul_nonneg hQpow hUpow
    nlinarith [mul_nonneg (sub_nonneg.mpr hexpOne) hnonneg]
  calc
    radius * Real.exp radius + 2 * (Q ^ alpha * U ^ alpha) =
        2 * rho * U * Real.exp radius +
          2 * (Q ^ alpha * U ^ alpha) := by rfl
    _ ≤ 2 * rho * U * Real.exp radius +
        2 * Real.exp radius * Q ^ alpha * U ^ alpha := by
      exact add_le_add_left hrealGrowth _
    _ = 2 * Real.exp radius * Q ^ alpha * U ^ alpha +
        2 * Real.exp radius * rho * U := by ring
    _ = 2 * Real.exp radius * Q ^ alpha * U ^ alpha +
        2 * Real.exp radius * rho *
          (U ^ (1 - alpha) * U ^ alpha) := by rw [hProduct]
    _ = 2 * Real.exp radius *
        (Q ^ alpha + rho * U ^ (1 - alpha)) * U ^ alpha := by
      ring

end

end YangMills.RG

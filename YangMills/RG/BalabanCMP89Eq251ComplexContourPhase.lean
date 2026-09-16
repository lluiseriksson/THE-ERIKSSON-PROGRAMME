/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249StabilizedComplexIntegrand

/-!
# Complex contour-phase dictionary below CMP89 (2.49)

Cold validation: exact source checkpoint
`e0b32533411b5ff8be5d55d432d076a7ca7172ae` passed GitHub Actions run
`31273452649` with restore and save of `.lake/build` both skipped. The focal
completed 8,443 jobs, and all ten audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The two phase factors in the stabilized CMP89 (2.49) numerator are not an
arbitrary bounded multiplier. Their product is exactly the difference of the
two physical Fourier phases with displacements `x-y` and `x'-y`. This module
records that identity before any contour estimate.

It also proves the exact imaginary-part dictionary for a reciprocal alias and
the resulting explicit exponential growth under a coordinate strip. The
alias shift is real, so it contributes no imaginary growth. No free family of
phase bounds is accepted.

These are the algebraic and scalar inputs for the later contour displacement.
They do not yet choose a contour direction, extract spatial decay, bound the
complete stabilized numerator, construct `B0`, or attain window 15.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The coordinate `ell^1` size that controls an imaginary Fourier phase. -/
def cmp89Eq251DisplacementL1 {d : ℕ} (displacement : Fin d → ℝ) : ℝ :=
  ∑ mu, |displacement mu|

/-- Explicit growth of one Fourier phase on a coordinate strip of width
`rho`. -/
def cmp89Eq251ContourPhaseGrowth {d : ℕ}
    (rho : ℝ) (displacement : Fin d → ℝ) : ℝ :=
  Real.exp (rho * cmp89Eq251DisplacementL1 displacement)

/-- The entire phase is additive in its physical displacement. -/
theorem cmp89Eq251EntirePhase_add
    {d : ℕ} (z : Fin d → ℂ) (u v : Fin d → ℝ) :
    cmp89Eq251EntirePhase z (fun mu => u mu + v mu) =
      cmp89Eq251EntirePhase z u + cmp89Eq251EntirePhase z v := by
  simp [cmp89Eq251EntirePhase, mul_add, Finset.sum_add_distrib]

/-- Reciprocal aliases are real translations, so the imaginary part of the
phase sees only the unshifted complex momentum. -/
theorem cmp89Eq251EntireAliasPhase_im
    {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℤ)
    (displacement : Fin d → ℝ) :
    (cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m) displacement).im =
      ∑ mu, (z mu).im * displacement mu := by
  simp [cmp89Eq251EntirePhase, cmp89Eq248EntireAliasMomentum,
    cmp89Eq245AliasShift, Complex.mul_im]

/-- Exact norm of an aliased Fourier phase. -/
theorem norm_exp_I_cmp89Eq251EntireAliasPhase
    {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℤ)
    (displacement : Fin d → ℝ) :
    ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m) displacement)‖ =
      Real.exp (-(∑ mu, (z mu).im * displacement mu)) := by
  rw [Complex.norm_exp, Complex.I_mul_re,
    cmp89Eq251EntireAliasPhase_im]

/-- A coordinate strip gives an explicit alias-independent phase-growth
bound. -/
theorem norm_exp_I_cmp89Eq251EntireAliasPhase_le_growth
    {d : ℕ} {rho : ℝ}
    {z : Fin d → ℂ} (himag : ∀ mu, |(z mu).im| ≤ rho)
    (m : Fin d → ℤ) (displacement : Fin d → ℝ) :
    ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m) displacement)‖ ≤
      cmp89Eq251ContourPhaseGrowth rho displacement := by
  have hterm : ∀ mu : Fin d,
      -(z mu).im * displacement mu ≤ rho * |displacement mu| := by
    intro mu
    calc
      -(z mu).im * displacement mu ≤
          |-(z mu).im * displacement mu| := le_abs_self _
      _ = |(z mu).im| * |displacement mu| := by
        rw [abs_mul, abs_neg]
      _ ≤ rho * |displacement mu| :=
        mul_le_mul_of_nonneg_right (himag mu) (abs_nonneg _)
  rw [norm_exp_I_cmp89Eq251EntireAliasPhase,
    cmp89Eq251ContourPhaseGrowth, cmp89Eq251DisplacementL1]
  apply Real.exp_le_exp.mpr
  calc
    -(∑ mu, (z mu).im * displacement mu) =
        ∑ mu, (-(z mu).im * displacement mu) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro mu _
      ring
    _ ≤ ∑ mu, rho * |displacement mu| :=
      Finset.sum_le_sum fun mu _ => hterm mu
    _ = rho * ∑ mu, |displacement mu| := by
      rw [Finset.mul_sum]

/-- The product of the Holder-difference phase and the transport phase is
exactly the difference of the two physical endpoint phases. -/
theorem cmp89Eq251_phaseDifference_mul_transport
    {d : ℕ} (q : Fin d → ℂ)
    (holderDisplacement transportDisplacement : Fin d → ℝ) :
    (Complex.exp (Complex.I *
          cmp89Eq251EntirePhase q holderDisplacement) - 1) *
        Complex.exp (Complex.I *
          cmp89Eq251EntirePhase q transportDisplacement) =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase q
          (fun mu => holderDisplacement mu + transportDisplacement mu)) -
        Complex.exp (Complex.I *
          cmp89Eq251EntirePhase q transportDisplacement) := by
  rw [cmp89Eq251EntirePhase_add, mul_add, Complex.exp_add]
  ring

/-- The same endpoint identity with the literal Holder normalization left in
place. -/
theorem cmp89Eq251_phaseQuotient_mul_transport
    {d : ℕ} (alpha : ℝ) (q : Fin d → ℂ)
    (holderDisplacement transportDisplacement : Fin d → ℝ) :
    ((Complex.exp (Complex.I *
          cmp89Eq251EntirePhase q holderDisplacement) - 1) /
        ((cmp89Eq251EuclideanNorm holderDisplacement ^ alpha : ℝ) : ℂ)) *
        Complex.exp (Complex.I *
          cmp89Eq251EntirePhase q transportDisplacement) =
      (Complex.exp (Complex.I * cmp89Eq251EntirePhase q
          (fun mu => holderDisplacement mu + transportDisplacement mu)) -
        Complex.exp (Complex.I *
          cmp89Eq251EntirePhase q transportDisplacement)) /
        ((cmp89Eq251EuclideanNorm holderDisplacement ^ alpha : ℝ) : ℂ) := by
  rw [div_mul_eq_mul_div, cmp89Eq251_phaseDifference_mul_transport]

/-- The bare stabilized numerator branch is therefore a difference of the
two physical endpoint phases, not an opaque phase product. -/
theorem cmp89Eq251ComplexBareAliasNumerator_eq_phaseDifference
    {d L j : ℕ} {alpha : ℝ} (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holderDisplacement transportDisplacement : Fin d → ℝ) :
    cmp89Eq251ComplexBareAliasNumerator d L j alpha z m mu
        holderDisplacement transportDisplacement =
      ((Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m)
            (fun nu => holderDisplacement nu + transportDisplacement nu)) -
          Complex.exp (Complex.I * cmp89Eq251EntirePhase
            (cmp89Eq248EntireAliasMomentum z m)
            transportDisplacement)) /
          ((cmp89Eq251EuclideanNorm holderDisplacement ^ alpha : ℝ) : ℂ)) *
        cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹)
          (-(cmp89Eq248EntireAliasMomentum z m mu)) *
        cmp89Eq245EntireAverageAmplitude d (L ^ j)
          (cmp89Eq248EntireAliasMomentum z m) := by
  rw [cmp89Eq251ComplexBareAliasNumerator,
    cmp89Eq251_phaseQuotient_mul_transport]

/-- Before choosing a contour direction, the exact phase difference is
bounded by the sum of the two explicit endpoint growth factors. -/
theorem norm_cmp89Eq251_endpointPhaseDifference_le
    {d : ℕ} {rho : ℝ}
    {z : Fin d → ℂ} (himag : ∀ mu, |(z mu).im| ≤ rho)
    (m : Fin d → ℤ) (u v : Fin d → ℝ) :
    ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m) u) -
        Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m) v)‖ ≤
      cmp89Eq251ContourPhaseGrowth rho u +
        cmp89Eq251ContourPhaseGrowth rho v := by
  exact (norm_sub_le _ _).trans
    (add_le_add
      (norm_exp_I_cmp89Eq251EntireAliasPhase_le_growth himag m u)
      (norm_exp_I_cmp89Eq251EntireAliasPhase_le_growth himag m v))

end

end YangMills.RG

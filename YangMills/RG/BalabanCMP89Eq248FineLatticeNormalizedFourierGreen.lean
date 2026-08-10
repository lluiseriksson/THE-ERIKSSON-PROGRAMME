/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq248FineLatticeFourierGreenLeftDerivative

/-!
# PRE-VALIDATION: normalized fine-lattice Fourier Green

Source is present, the corresponding `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

CMP89 (2.48)--(2.49) obtains the fine left derivative by applying one
physical fine-lattice difference to the Green kernel.  The pointwise identity
is already sealed.  This module constructs integrability of the Green value
on the real Brillouin cube from the same complete-polydisc nonvanishing gate,
then moves that finite difference through the literal source-normalized
integral.

No Green integrability or integral identity is accepted as a premise.  The
identification of the resulting Fourier Green with the repository's literal
operator `G_j Q_j^*`, physical `B0`, window 15 and terminal fields remain
open.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

attribute [local fun_prop]
  differentiable_cmp89Eq245EntireAverageAmplitude

/-- A bare reciprocal-alias Green endpoint is entire in complex momentum. -/
@[fun_prop]
theorem differentiable_cmp89Eq248ComplexBareGreenEndpointNumerator
    (d L j : ℕ) (m : Fin d → ℤ)
    (endpointDisplacement : Fin d → ℝ) :
    Differentiable ℂ (fun z : Fin d → ℂ =>
      cmp89Eq248ComplexBareGreenEndpointNumerator
        d L j z m endpointDisplacement) := by
  unfold cmp89Eq248ComplexBareGreenEndpointNumerator
  fun_prop

/-- The assembled Green numerator is differentiable wherever every literal
noncentral fine symbol is nonzero. -/
theorem differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointNumerator
    {d L j : ℕ} {mass : ℝ} {z : Fin d → ℂ}
    {endpointDisplacement : Fin d → ℝ}
    (hfine : ∀ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
        (cmp89Eq249ZeroAlias d),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq248ComplexStabilizedGreenEndpointNumerator
        d L j mass w endpointDisplacement) z := by
  let aliases := (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
    (cmp89Eq249ZeroAlias d)
  have hcentral : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq248ComplexBareGreenEndpointNumerator d L j w
        (cmp89Eq249ZeroAlias d) endpointDisplacement) z :=
    (differentiable_cmp89Eq248ComplexBareGreenEndpointNumerator
      d L j (cmp89Eq249ZeroAlias d) endpointDisplacement) z
  have hcentralFine : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq249CentralEntireFineSymbol d L j mass w) z := by
    exact (differentiable_cmp89Eq245EntireScaledLaplacianSymbol
      d (((L : ℝ) ^ j)⁻¹) mass) z
  have hsum : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      ∑ m ∈ aliases,
        cmp89Eq248ComplexBareGreenEndpointNumerator d L j w m
            endpointDisplacement /
          cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum w m)) z := by
    apply DifferentiableAt.fun_sum
    intro m hm
    have hbare :=
      (differentiable_cmp89Eq248ComplexBareGreenEndpointNumerator
        d L j m endpointDisplacement) z
    have hshift := differentiable_cmp89Eq248EntireAliasMomentum m
    have hden :=
      (differentiable_cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass).comp hshift
    have hdenInv := (hden z).inv (hfine m (by simpa [aliases] using hm))
    simpa [div_eq_mul_inv] using hbare.mul hdenInv
  simpa only [cmp89Eq248ComplexStabilizedGreenEndpointNumerator, aliases] using
    hcentral.add (hcentralFine.mul hsum)

/-- The stabilized Green integrand is differentiable at every point where
its noncentral fine symbols and common denominator are nonzero. -/
theorem differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
    {d L j : ℕ} {mass a : ℝ} {z : Fin d → ℂ}
    {endpointDisplacement : Fin d → ℝ}
    (hfine : ∀ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
        (cmp89Eq249ZeroAlias d),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
        d L j mass a w endpointDisplacement) z := by
  have hnum :=
    differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointNumerator
      (mass := mass) (z := z)
      (endpointDisplacement := endpointDisplacement) hfine
  have hden :=
    differentiableAt_cmp89Eq249CentralStabilizedAliasDenominator
      (mass := mass) (a := a) (z := z) hfine
  have hdenInv := hden.inv hstabilized
  simpa [cmp89Eq248ComplexStabilizedGreenEndpointIntegrand,
    div_eq_mul_inv] using hnum.mul hdenInv

/-- The common scalar radius produces both non-singularity inputs for the
Green value on the complete four-dimensional polydisc. -/
theorem differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_of_commonRadius
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ nu, |p nu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ nu, (z nu).re = p nu)
    (himag : ∀ nu, |(z nu).im| ≤ rho)
    {endpointDisplacement : Fin 4 → ℝ} :
    DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
        4 L j mass a w endpointDisplacement) z := by
  have hfine : ∀ m ∈
      (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
        (cmp89Eq249ZeroAlias 4),
      cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
    intro m hm
    exact cmp89Eq251NoncentralFineSymbol_ne_zero_of_commonRadius
      hrho hradius hm hp hreal himag
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z ≠ 0 :=
    cmp89Eq249CentralStabilizedAliasDenominator_ne_zero
      ha hmassPos hrho hradius hmass hwindow hp hreal himag hamplitude
  exact
    differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
      hfine hstabilized

/-- The literal stabilized Fourier Green value is integrable on the real
Brillouin cube.  This is derived from complete-polydisc nonvanishing and
compactness, not supplied by the caller. -/
theorem integrable_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_real
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (endpointU : Fin 4 → ℤ) :
    Integrable (fun x : Fin 4 → ℝ =>
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) endpointU))
      cmp89Eq249FourDimensionalBrillouinMeasure := by
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  let endpointDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (cmp89Eq249FineLatticeSpacing L j) endpointU
  have hcont : ContinuousOn (fun x : Fin 4 → ℝ =>
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        endpointDisplacement)
      (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi)) := by
    intro x hx
    have hp : ∀ nu,
        |cmp89Eq251PhysicalBrillouinParameter x nu| ≤ Real.pi := by
      intro nu
      rw [abs_le]
      have hxLower := hx.1 nu
      have hxUpper := hx.2 nu
      simp only [cmp89Eq251PhysicalBrillouinParameter]
      constructor <;> linarith [Real.pi_pos]
    have houter :=
      differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_of_commonRadius
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hmassPos hrho hamplitude hradius hwindow hmass
        (p := cmp89Eq251PhysicalBrillouinParameter x) hp
        (z := fun nu =>
          (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        (by intro nu; simp)
        (by intro nu; simpa using hrho)
        (endpointDisplacement := endpointDisplacement)
    have hinner : ContinuousAt (fun y : Fin 4 → ℝ =>
        fun nu => (cmp89Eq251PhysicalBrillouinParameter y nu : ℂ)) x := by
      apply Continuous.continuousAt
      apply continuous_pi
      intro nu
      simp only [cmp89Eq251PhysicalBrillouinParameter]
      fun_prop
    exact (houter.continuousAt.comp hinner).continuousWithinAt
  have hIcc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        endpointDisplacement)
      (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hcont.integrableOn_compact
      (isCompact_Icc : IsCompact
        (Set.Icc (fun _ : Fin 4 => 0) (fun _ => 2 * Real.pi)))
  have hIoc : IntegrableOn (fun x : Fin 4 → ℝ =>
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        endpointDisplacement)
      (Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi))
      (volume : Measure (Fin 4 → ℝ)) :=
    hIcc.congr_set_ae Measure.univ_pi_Ioc_ae_eq_Icc
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi] at hIoc
  simpa [endpointDisplacement,
    cmp89Eq249FourDimensionalBrillouinMeasure, IntegrableOn,
    Set.uIoc_of_le htwoPi] using hIoc

/-- Source-normalized stabilized Fourier Green value at one physical
fine-lattice displacement. -/
def cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
    (L j : ℕ) [NeZero L] (mass a : ℝ) (endpointU : Fin 4 → ℤ) : ℂ :=
  cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) endpointU)

/-- The normalized fine-lattice left-derivative kernel is the exact forward
difference quotient of the two internally constructed normalized Green
values. -/
theorem cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_forwardDifference
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (u : Fin 4 → ℤ) :
    (cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen L j mass a
          (cmp89Eq248FineLatticeForwardCoordinateShift mu u) -
        cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
          L j mass a u) /
        (cmp89Eq249FineLatticeSpacing L j : ℂ) =
      cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
        L j mass a mu u := by
  let xi := cmp89Eq249FineLatticeSpacing L j
  let measure := cmp89Eq249FourDimensionalBrillouinMeasure
  let shifted : (Fin 4 → ℝ) → ℂ := fun x =>
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      (cmp89Eq249PhysicalFineLatticeDisplacement xi
        (cmp89Eq248FineLatticeForwardCoordinateShift mu u))
  let base : (Fin 4 → ℝ) → ℂ := fun x =>
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      (cmp89Eq249PhysicalFineLatticeDisplacement xi u)
  let deriv : (Fin 4 → ℝ) → ℂ := fun x =>
    cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
      L j mass a
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu u
  have hshifted : Integrable shifted measure := by
    simpa [shifted, measure, xi] using
      (integrable_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_real
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hmassPos hrho hamplitude hradius hwindow hmass
        (cmp89Eq248FineLatticeForwardCoordinateShift mu u))
  have hbase : Integrable base measure := by
    simpa [base, measure, xi] using
      (integrable_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_real
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hmassPos hrho hamplitude hradius hwindow hmass u)
  have hpoint : ∀ x, (shifted x - base x) / (xi : ℂ) = deriv x := by
    intro x
    simpa [shifted, base, deriv, xi] using
      (cmp89Eq248ComplexStabilizedGreenEndpoint_forwardDifference
        (L := L) (j := j) (mass := mass) (a := a)
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu u)
  let normalization : ℂ := ((((2 * Real.pi) ^ 4)⁻¹ : ℝ) : ℂ)
  unfold cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
    cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
  change
    (normalization * ∫ x, shifted x ∂measure -
        normalization * ∫ x, base x ∂measure) / (xi : ℂ) =
      normalization * ∫ x, deriv x ∂measure
  calc
    _ = normalization *
        (((∫ x, shifted x ∂measure) - ∫ x, base x ∂measure) / (xi : ℂ)) := by
      ring
    _ = normalization *
        ((∫ x, shifted x - base x ∂measure) / (xi : ℂ)) := by
      rw [MeasureTheory.integral_sub hshifted hbase]
    _ = normalization *
        (∫ x, (shifted x - base x) / (xi : ℂ) ∂measure) := by
      apply congrArg (fun value : ℂ => normalization * value)
      simpa [div_eq_mul_inv] using
        (MeasureTheory.integral_mul_const
          (fun x => shifted x - base x) ((xi : ℂ)⁻¹)
          (μ := measure)).symm
    _ = normalization * ∫ x, deriv x ∂measure := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x

end

end YangMills.RG

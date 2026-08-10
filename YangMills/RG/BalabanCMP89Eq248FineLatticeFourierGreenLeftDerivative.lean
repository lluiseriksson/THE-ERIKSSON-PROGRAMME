/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249FineLatticeStabilizedFourierLeftDerivativeKernel

/-!
# PRE-VALIDATION: fine-lattice Fourier Green and its left derivative

Source is present, the corresponding `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

CMP89 (2.48)--(2.49) obtains the displayed left derivative from a Green
kernel by one physical fine-lattice difference.  This module constructs the
literal stabilized Fourier Green integrand, with the same reciprocal aliases
and common denominator as the already sealed derivative integrand, and proves
the pointwise difference identity.

The sign is not inferred from the word `left`: the printed factor is
`D_xi(-q_mu) = (exp(i*xi*q_mu)-1)/xi`, so the endpoint is shifted by the
positive coordinate vector before subtraction.

Honest scope: this is a pointwise Fourier identity.  It does not move the
difference through the Brillouin integral, identify the Fourier Green with
the repository's literal operator `G_j Q_j^*`, produce the physical `B0`,
attain window 15, discharge a terminal field or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Add one unit fine-lattice step in the displayed derivative coordinate. -/
def cmp89Eq248FineLatticeForwardCoordinateShift {d : ℕ}
    (mu : Fin d) (u : Fin d → ℤ) : Fin d → ℤ :=
  fun nu => u nu + (Pi.single mu (1 : ℤ) : Fin d → ℤ) nu

/-- Physical fine-lattice scaling turns the integer coordinate step into the
literal real step `xi` in that coordinate. -/
theorem cmp89Eq249PhysicalFineLatticeDisplacement_forwardCoordinateShift
    {d : ℕ} (xi : ℝ) (mu : Fin d) (u : Fin d → ℤ) :
    cmp89Eq249PhysicalFineLatticeDisplacement xi
        (cmp89Eq248FineLatticeForwardCoordinateShift mu u) =
      fun nu => cmp89Eq249PhysicalFineLatticeDisplacement xi u nu +
        (Pi.single mu xi : Fin d → ℝ) nu := by
  funext nu
  by_cases hnu : nu = mu
  · subst nu
    simp [cmp89Eq248FineLatticeForwardCoordinateShift,
      cmp89Eq249PhysicalFineLatticeDisplacement]
    ring
  · simp [cmp89Eq248FineLatticeForwardCoordinateShift,
      cmp89Eq249PhysicalFineLatticeDisplacement, hnu]

/-- One positive fine coordinate step adds exactly `xi*q_mu` to every alias
phase.  This is the sign carried by the printed `D_xi(-q_mu)`. -/
theorem cmp89Eq251EntireAliasPhase_forwardCoordinateShift
    {d : ℕ} (xi : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (u : Fin d → ℤ) :
    cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m)
        (cmp89Eq249PhysicalFineLatticeDisplacement xi
          (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) =
      cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m)
          (cmp89Eq249PhysicalFineLatticeDisplacement xi u) +
        (xi : ℂ) * cmp89Eq248EntireAliasMomentum z m mu := by
  classical
  rw [cmp89Eq249PhysicalFineLatticeDisplacement_forwardCoordinateShift,
    cmp89Eq251EntirePhase_add]
  rw [show cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m)
        (Pi.single mu xi : Fin d → ℝ) =
      cmp89Eq248EntireAliasMomentum z m mu * (xi : ℂ) by
    rw [cmp89Eq251EntirePhase, Finset.sum_eq_single mu]
    · simp
    · intro nu _ hnu
      simp [hnu]
    · simp]
  ring

/-- The phase difference quotient is exactly the entire fine difference
symbol appearing in CMP89 (2.49). -/
theorem cmp89Eq251_exp_aliasPhase_forwardDifference_div_spacing
    {d : ℕ} {xi : ℝ} (hxi : xi ≠ 0) (z : Fin d → ℂ)
    (m : Fin d → ℤ) (mu : Fin d) (u : Fin d → ℤ) :
    (Complex.exp (Complex.I *
          cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m)
            (cmp89Eq249PhysicalFineLatticeDisplacement xi
              (cmp89Eq248FineLatticeForwardCoordinateShift mu u))) -
        Complex.exp (Complex.I *
          cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m)
            (cmp89Eq249PhysicalFineLatticeDisplacement xi u))) / (xi : ℂ) =
      Complex.exp (Complex.I *
          cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m)
            (cmp89Eq249PhysicalFineLatticeDisplacement xi u)) *
        cmp89Eq245EntireScaledDifference xi
          (-(cmp89Eq248EntireAliasMomentum z m mu)) := by
  rw [cmp89Eq251EntireAliasPhase_forwardCoordinateShift,
    mul_add, Complex.exp_add]
  unfold cmp89Eq245EntireScaledDifference
  have hxiC : (xi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxi
  field_simp [hxiC]

/-- One reciprocal-alias contribution to the Green endpoint before applying
the fine left difference. -/
def cmp89Eq248ComplexBareGreenEndpointNumerator
    (d L j : ℕ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (endpointDisplacement : Fin d → ℝ) : ℂ :=
  let q := cmp89Eq248EntireAliasMomentum z m
  Complex.exp (Complex.I * cmp89Eq251EntirePhase q endpointDisplacement) *
    cmp89Eq245EntireAverageAmplitude d (L ^ j) q

/-- The fine difference of one bare Green alias is exactly the already
sealed bare derivative endpoint at `alpha = 0`. -/
theorem cmp89Eq248ComplexBareGreenEndpoint_forwardDifference
    {d L j : ℕ} [NeZero L] (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (u : Fin d → ℤ) :
    (cmp89Eq248ComplexBareGreenEndpointNumerator d L j z m
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) -
        cmp89Eq248ComplexBareGreenEndpointNumerator d L j z m
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) u)) /
        (cmp89Eq249FineLatticeSpacing L j : ℂ) =
      cmp89Eq251ComplexBareEndpointNumerator d L j 0 z m mu
        (fun _ => 0)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) u) := by
  let xi := cmp89Eq249FineLatticeSpacing L j
  let q := cmp89Eq248EntireAliasMomentum z m
  have hxi : xi ≠ 0 := ne_of_gt (cmp89Eq249FineLatticeSpacing_pos L j)
  have hphase := cmp89Eq251_exp_aliasPhase_forwardDifference_div_spacing
    hxi z m mu u
  unfold cmp89Eq248ComplexBareGreenEndpointNumerator
    cmp89Eq251ComplexBareEndpointNumerator
  simp only [Real.rpow_zero, Complex.ofReal_one, div_one]
  change
    ((Complex.exp (Complex.I * cmp89Eq251EntirePhase q
          (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (cmp89Eq248FineLatticeForwardCoordinateShift mu u))) *
          cmp89Eq245EntireAverageAmplitude d (L ^ j) q -
        Complex.exp (Complex.I * cmp89Eq251EntirePhase q
          (cmp89Eq249PhysicalFineLatticeDisplacement xi u)) *
          cmp89Eq245EntireAverageAmplitude d (L ^ j) q) / (xi : ℂ)) =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase q
          (cmp89Eq249PhysicalFineLatticeDisplacement xi u)) *
        cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹) (-q mu) *
          cmp89Eq245EntireAverageAmplitude d (L ^ j) q
  calc
    _ = ((Complex.exp (Complex.I * cmp89Eq251EntirePhase q
            (cmp89Eq249PhysicalFineLatticeDisplacement xi
              (cmp89Eq248FineLatticeForwardCoordinateShift mu u))) -
          Complex.exp (Complex.I * cmp89Eq251EntirePhase q
            (cmp89Eq249PhysicalFineLatticeDisplacement xi u))) / (xi : ℂ)) *
          cmp89Eq245EntireAverageAmplitude d (L ^ j) q := by ring
    _ = Complex.exp (Complex.I * cmp89Eq251EntirePhase q
            (cmp89Eq249PhysicalFineLatticeDisplacement xi u)) *
          cmp89Eq245EntireScaledDifference xi (-q mu) *
          cmp89Eq245EntireAverageAmplitude d (L ^ j) q := by
        rw [hphase]
    _ = _ := by
      simp [xi, cmp89Eq249FineLatticeSpacing]

/-- The reciprocal-alias Green numerators assembled with the same removable
central cancellation as the derivative endpoint. -/
def cmp89Eq248ComplexStabilizedGreenEndpointNumerator
    (d L j : ℕ) (mass : ℝ) (z : Fin d → ℂ)
    (endpointDisplacement : Fin d → ℝ) : ℂ :=
  cmp89Eq248ComplexBareGreenEndpointNumerator d L j z
      (cmp89Eq249ZeroAlias d) endpointDisplacement +
    cmp89Eq249CentralEntireFineSymbol d L j mass z *
      ∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
          (cmp89Eq249ZeroAlias d),
        cmp89Eq248ComplexBareGreenEndpointNumerator d L j z m
            endpointDisplacement /
          cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum z m)

/-- Pointwise stabilized Green integrand before the fine left difference. -/
def cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ)
    (endpointDisplacement : Fin d → ℝ) : ℂ :=
  cmp89Eq248ComplexStabilizedGreenEndpointNumerator d L j mass z
      endpointDisplacement /
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z

/-- The assembled numerator commutes with the physical fine difference. -/
theorem cmp89Eq248ComplexStabilizedGreenEndpointNumerator_forwardDifference
    {d L j : ℕ} [NeZero L] {mass : ℝ} (z : Fin d → ℂ)
    (mu : Fin d) (u : Fin d → ℤ) :
    (cmp89Eq248ComplexStabilizedGreenEndpointNumerator d L j mass z
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) -
        cmp89Eq248ComplexStabilizedGreenEndpointNumerator d L j mass z
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) u)) /
        (cmp89Eq249FineLatticeSpacing L j : ℂ) =
      cmp89Eq251ComplexStabilizedEndpointNumerator d L j mass 0 z mu
        (fun _ => 0)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) u) := by
  let xi := cmp89Eq249FineLatticeSpacing L j
  let aliases := (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
    (cmp89Eq249ZeroAlias d)
  let fine := fun m : Fin d → ℤ =>
    cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
      (cmp89Eq248EntireAliasMomentum z m)
  let green := fun m : Fin d → ℤ => fun endpoint =>
    cmp89Eq248ComplexBareGreenEndpointNumerator d L j z m endpoint
  let deriv := fun m : Fin d → ℤ =>
    cmp89Eq251ComplexBareEndpointNumerator d L j 0 z m mu
      (fun _ => 0)
      (cmp89Eq249PhysicalFineLatticeDisplacement xi u)
  have hbare : ∀ m : Fin d → ℤ,
      (green m (cmp89Eq249PhysicalFineLatticeDisplacement xi
          (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) -
        green m (cmp89Eq249PhysicalFineLatticeDisplacement xi u)) /
          (xi : ℂ) = deriv m := by
    intro m
    exact cmp89Eq248ComplexBareGreenEndpoint_forwardDifference z m mu u
  have hsum :
      ((∑ m ∈ aliases,
          green m (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) / fine m) -
        ∑ m ∈ aliases,
          green m (cmp89Eq249PhysicalFineLatticeDisplacement xi u) / fine m) /
          (xi : ℂ) =
        ∑ m ∈ aliases, deriv m / fine m := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_div]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m _
    calc
      ((green m (cmp89Eq249PhysicalFineLatticeDisplacement xi
              (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) -
            green m (cmp89Eq249PhysicalFineLatticeDisplacement xi u)) /
          fine m) / (xi : ℂ) =
        ((green m (cmp89Eq249PhysicalFineLatticeDisplacement xi
              (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) -
            green m (cmp89Eq249PhysicalFineLatticeDisplacement xi u)) /
            (xi : ℂ)) / fine m := by ring
      _ = deriv m / fine m := by rw [hbare m]
  unfold cmp89Eq248ComplexStabilizedGreenEndpointNumerator
    cmp89Eq251ComplexStabilizedEndpointNumerator
  change
    ((green (cmp89Eq249ZeroAlias d)
          (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) +
          cmp89Eq249CentralEntireFineSymbol d L j mass z *
            ∑ m ∈ aliases,
              green m (cmp89Eq249PhysicalFineLatticeDisplacement xi
                (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) / fine m -
        (green (cmp89Eq249ZeroAlias d)
          (cmp89Eq249PhysicalFineLatticeDisplacement xi u) +
          cmp89Eq249CentralEntireFineSymbol d L j mass z *
            ∑ m ∈ aliases,
              green m (cmp89Eq249PhysicalFineLatticeDisplacement xi u) / fine m)) /
          (xi : ℂ)) =
      deriv (cmp89Eq249ZeroAlias d) +
        cmp89Eq249CentralEntireFineSymbol d L j mass z *
          ∑ m ∈ aliases, deriv m / fine m
  calc
    _ = (green (cmp89Eq249ZeroAlias d)
            (cmp89Eq249PhysicalFineLatticeDisplacement xi
              (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) -
          green (cmp89Eq249ZeroAlias d)
            (cmp89Eq249PhysicalFineLatticeDisplacement xi u)) /
            (xi : ℂ) +
        cmp89Eq249CentralEntireFineSymbol d L j mass z *
          (((∑ m ∈ aliases,
              green m (cmp89Eq249PhysicalFineLatticeDisplacement xi
                (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) / fine m) -
            ∑ m ∈ aliases,
              green m (cmp89Eq249PhysicalFineLatticeDisplacement xi u) / fine m) /
              (xi : ℂ)) := by ring
    _ = _ := by rw [hbare, hsum]

/-- The literal stabilized Fourier Green has the already sealed fine-lattice
left-derivative integrand as its exact pointwise forward difference. -/
theorem cmp89Eq248ComplexStabilizedGreenEndpoint_forwardDifference
    {L j : ℕ} [NeZero L] {mass a : ℝ} (z : Fin 4 → ℂ)
    (mu : Fin 4) (u : Fin 4 → ℤ) :
    (cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a z
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) -
        cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a z
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) u)) /
        (cmp89Eq249FineLatticeSpacing L j : ℂ) =
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a z mu u := by
  let xi := cmp89Eq249FineLatticeSpacing L j
  let numerator := cmp89Eq251ComplexStabilizedEndpointNumerator
    4 L j mass 0 z mu (fun _ => 0)
      (cmp89Eq249PhysicalFineLatticeDisplacement xi u)
  let denominator := cmp89Eq249CentralStabilizedAliasDenominator
    4 L j mass a z
  have hxi : (xi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (cmp89Eq249FineLatticeSpacing_pos L j))
  have hnum :=
    cmp89Eq248ComplexStabilizedGreenEndpointNumerator_forwardDifference
      (d := 4) (L := L) (j := j) (mass := mass) z mu u
  unfold cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
    cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
    cmp89Eq251ComplexStabilizedEndpointIntegrand
  change
    ((cmp89Eq248ComplexStabilizedGreenEndpointNumerator 4 L j mass z
          (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) /
          denominator -
        cmp89Eq248ComplexStabilizedGreenEndpointNumerator 4 L j mass z
          (cmp89Eq249PhysicalFineLatticeDisplacement xi u) /
          denominator) / (xi : ℂ)) = numerator / denominator
  rw [← sub_div]
  have hnum' :
      cmp89Eq248ComplexStabilizedGreenEndpointNumerator 4 L j mass z
          (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (cmp89Eq248FineLatticeForwardCoordinateShift mu u)) -
        cmp89Eq248ComplexStabilizedGreenEndpointNumerator 4 L j mass z
          (cmp89Eq249PhysicalFineLatticeDisplacement xi u) =
        (xi : ℂ) * numerator := by
    have h := (div_eq_iff hxi).mp hnum
    simpa [mul_comm] using h
  rw [hnum']
  simp only [div_eq_mul_inv]
  calc
    ((xi : ℂ) * numerator * denominator⁻¹) * (xi : ℂ)⁻¹ =
        ((xi : ℂ) * (xi : ℂ)⁻¹) *
          (numerator * denominator⁻¹) := by ring
    _ = numerator * denominator⁻¹ := by rw [mul_inv_cancel₀ hxi, one_mul]

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointSplit
import YangMills.RG.BalabanCMP89Eq251CommonStripHolomorphy

/-!
# PRE-VALIDATION: common-strip holomorphy of each CMP89 endpoint

The source in this module is present, but its `.olean` has not yet been
materialized and its result has not yet been verified by the Lean compiler.

After the exact endpoint split, each endpoint must be shifted separately.
This module derives its holomorphy from the literal endpoint numerator.  The
only singular inputs are the same noncentral fine symbols and common
stabilized denominator already produced by the sealed common-radius theorem.

No endpoint function, extra radius or additional denominator condition is
accepted.  Boundary seams, contour integrals, `B0`, the owner dictionary and
window-15 attainment remain separate.
-/

namespace YangMills.RG

noncomputable section

attribute [local fun_prop]
  differentiable_cmp89Eq245EntireAverageAmplitude

/-- A bare physical endpoint numerator is entire in complex momentum. -/
@[fun_prop]
theorem differentiable_cmp89Eq251ComplexBareEndpointNumerator
    (d L j : ℕ) (alpha : ℝ) (m : Fin d → ℤ) (mu : Fin d)
    (holderDisplacement endpointDisplacement : Fin d → ℝ) :
    Differentiable ℂ (fun z : Fin d → ℂ =>
      cmp89Eq251ComplexBareEndpointNumerator d L j alpha z m mu
        holderDisplacement endpointDisplacement) := by
  unfold cmp89Eq251ComplexBareEndpointNumerator
  fun_prop

/-- The assembled endpoint numerator is differentiable wherever every
noncentral fine symbol that occurs literally in its finite sum is nonzero. -/
theorem differentiableAt_cmp89Eq251ComplexStabilizedEndpointNumerator
    {d L j : ℕ} {mass alpha : ℝ} {z : Fin d → ℂ} {mu : Fin d}
    {holderDisplacement endpointDisplacement : Fin d → ℝ}
    (hfine : ∀ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
        (cmp89Eq249ZeroAlias d),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq251ComplexStabilizedEndpointNumerator d L j mass alpha w mu
        holderDisplacement endpointDisplacement) z := by
  let aliases := (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
    (cmp89Eq249ZeroAlias d)
  have hcentral : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq251ComplexBareEndpointNumerator d L j alpha w
        (cmp89Eq249ZeroAlias d) mu holderDisplacement
        endpointDisplacement) z :=
    (differentiable_cmp89Eq251ComplexBareEndpointNumerator d L j alpha
      (cmp89Eq249ZeroAlias d) mu holderDisplacement endpointDisplacement) z
  have hcentralFine : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq249CentralEntireFineSymbol d L j mass w) z := by
    exact (differentiable_cmp89Eq245EntireScaledLaplacianSymbol
      d (((L : ℝ) ^ j)⁻¹) mass) z
  have hsum : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      ∑ m ∈ aliases,
        cmp89Eq251ComplexBareEndpointNumerator d L j alpha w m mu
            holderDisplacement endpointDisplacement /
          cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum w m)) z := by
    apply DifferentiableAt.fun_sum
    intro m hm
    have hbare :=
      (differentiable_cmp89Eq251ComplexBareEndpointNumerator d L j alpha
        m mu holderDisplacement endpointDisplacement) z
    have hshift := differentiable_cmp89Eq248EntireAliasMomentum m
    have hden :=
      (differentiable_cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass).comp hshift
    have hdenInv := (hden z).inv (hfine m (by simpa [aliases] using hm))
    simpa [div_eq_mul_inv] using hbare.mul hdenInv
  simpa only [cmp89Eq251ComplexStabilizedEndpointNumerator, aliases] using
    hcentral.add (hcentralFine.mul hsum)

/-- One endpoint integrand is differentiable wherever its literal numerator
and common stabilized denominator are non-singular. -/
theorem differentiableAt_cmp89Eq251ComplexStabilizedEndpointIntegrand
    {d L j : ℕ} {mass a alpha : ℝ} {z : Fin d → ℂ} {mu : Fin d}
    {holderDisplacement endpointDisplacement : Fin d → ℝ}
    (hfine : ∀ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
        (cmp89Eq249ZeroAlias d),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a alpha w mu
        holderDisplacement endpointDisplacement) z := by
  have hnum :=
    differentiableAt_cmp89Eq251ComplexStabilizedEndpointNumerator
      (mass := mass) (alpha := alpha) (z := z) (mu := mu)
      (holderDisplacement := holderDisplacement)
      (endpointDisplacement := endpointDisplacement) hfine
  have hden :=
    differentiableAt_cmp89Eq249CentralStabilizedAliasDenominator
      (mass := mass) (a := a) (z := z) hfine
  have hdenInv := hden.inv hstabilized
  simpa [cmp89Eq251ComplexStabilizedEndpointIntegrand, div_eq_mul_inv] using
    hnum.mul hdenInv

/-- The sealed common scalar radius supplies exactly the two non-singularity
inputs needed by each physical endpoint integrand. -/
theorem differentiableAt_cmp89Eq251ComplexStabilizedEndpointIntegrand_of_commonRadius
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ nu, |p nu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ nu, (z nu).re = p nu)
    (himag : ∀ nu, |(z nu).im| ≤ rho)
    {mu : Fin 4}
    {holderDisplacement endpointDisplacement : Fin 4 → ℝ} :
    DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
      cmp89Eq251ComplexStabilizedEndpointIntegrand
        4 L j mass a alpha w mu holderDisplacement endpointDisplacement) z := by
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
  exact differentiableAt_cmp89Eq251ComplexStabilizedEndpointIntegrand
    hfine hstabilized

end

end YangMills.RG

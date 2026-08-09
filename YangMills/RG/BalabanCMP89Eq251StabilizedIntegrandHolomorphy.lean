/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249StabilizedComplexIntegrand

/-!
# Holomorphy of the stabilized CMP89 integrand on its literal domain

PRE-VALIDATION: source is present; its `.olean` has not yet been materialized,
and the result is not yet compiler-verified.

This module derives complex differentiability of the stabilized CMP89 (2.49)
integrand from the already constructed entire Fourier factors.  The only
domain inputs are nonvanishing of the noncentral fine symbols that remain in
the stabilized numerator and nonvanishing of the stabilized denominator.

In particular, no unit-symbol, reduced-denominator or central-fine-symbol
nonvanishing hypothesis is reintroduced after those factors have been
cancelled algebraically.  Producing the two surviving nonvanishing inputs
uniformly on the common strip is a separate physical brick.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Translation by one reciprocal alias is entire in the coarse complex
momentum. -/
theorem differentiable_cmp89Eq248EntireAliasMomentum
    {d : ℕ} (m : Fin d → ℤ) :
    Differentiable ℂ (fun z : Fin d → ℂ =>
      cmp89Eq248EntireAliasMomentum z m) := by
  unfold cmp89Eq248EntireAliasMomentum
  fun_prop

/-- The bilinear endpoint phase is entire in complex momentum. -/
theorem differentiable_cmp89Eq251EntirePhase
    {d : ℕ} (displacement : Fin d → ℝ) :
    Differentiable ℂ (fun z : Fin d → ℂ =>
      cmp89Eq251EntirePhase z displacement) := by
  unfold cmp89Eq251EntirePhase
  fun_prop

/-- Every bare reciprocal-alias numerator is entire.  Division by the fixed
Holder weight is harmless even when that scalar is zero, because it is a
constant function of momentum. -/
theorem differentiable_cmp89Eq251ComplexBareAliasNumerator
    (d L j : ℕ) (alpha : ℝ) (m : Fin d → ℤ) (mu : Fin d)
    (holderDisplacement transportDisplacement : Fin d → ℝ) :
    Differentiable ℂ (fun z : Fin d → ℂ =>
      cmp89Eq251ComplexBareAliasNumerator d L j alpha z m mu
        holderDisplacement transportDisplacement) := by
  unfold cmp89Eq251ComplexBareAliasNumerator
  fun_prop

/-- The stabilized numerator is differentiable at a point whenever each
noncentral fine symbol that remains in its literal finite sum is nonzero. -/
theorem differentiableAt_cmp89Eq251ComplexStabilizedNumerator
    {d L j : ℕ} {mass alpha : ℝ} {z : Fin d → ℂ} {mu : Fin d}
    {holderDisplacement transportDisplacement : Fin d → ℝ}
    (hfine : ∀ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
        (cmp89Eq249ZeroAlias d),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq251ComplexStabilizedNumerator d L j mass alpha w mu
        holderDisplacement transportDisplacement) z := by
  let aliases := (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
    (cmp89Eq249ZeroAlias d)
  have hcentral : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq251ComplexBareAliasNumerator d L j alpha w
        (cmp89Eq249ZeroAlias d) mu holderDisplacement
        transportDisplacement) z :=
    (differentiable_cmp89Eq251ComplexBareAliasNumerator d L j alpha
      (cmp89Eq249ZeroAlias d) mu holderDisplacement
      transportDisplacement) z
  have hcentralFine : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq249CentralEntireFineSymbol d L j mass w) z := by
    exact (differentiable_cmp89Eq245EntireScaledLaplacianSymbol
      d (((L : ℝ) ^ j)⁻¹) mass) z
  have hsum : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      ∑ m ∈ aliases,
        cmp89Eq251ComplexBareAliasNumerator d L j alpha w m mu
            holderDisplacement transportDisplacement /
          cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum w m)) z := by
    apply DifferentiableAt.fun_sum
    intro m hm
    have hbare :=
      (differentiable_cmp89Eq251ComplexBareAliasNumerator d L j alpha m mu
        holderDisplacement transportDisplacement) z
    have hshift := differentiable_cmp89Eq248EntireAliasMomentum m
    have hden :=
      (differentiable_cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass).comp hshift
    exact hbare.div (hden z) (hfine m (by simpa [aliases] using hm))
  simpa only [cmp89Eq251ComplexStabilizedNumerator, aliases] using
    hcentral.add (hcentralFine.mul hsum)

/-- The central stabilized denominator is differentiable at a point whenever
the noncentral fine symbols in its literal alias sum are nonzero there. -/
theorem differentiableAt_cmp89Eq249CentralStabilizedAliasDenominator
    {d L j : ℕ} {mass a : ℝ} {z : Fin d → ℂ}
    (hfine : ∀ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
        (cmp89Eq249ZeroAlias d),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a w) z := by
  let aliases := (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
    (cmp89Eq249ZeroAlias d)
  have hcentralFine : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq249CentralEntireFineSymbol d L j mass w) z := by
    exact (differentiable_cmp89Eq245EntireScaledLaplacianSymbol
      d (((L : ℝ) ^ j)⁻¹) mass) z
  have hcentralAverage : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq249CentralEntireAveragePair d L j w) z := by
    exact (differentiable_cmp89Eq245EntireAveragePair d (L ^ j)) z
  have hsum : DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      ∑ m ∈ aliases,
        cmp89Eq248ComplexAliasDenominatorSummand d L j mass w m) z := by
    apply DifferentiableAt.fun_sum
    intro m hm
    have hshift := differentiable_cmp89Eq248EntireAliasMomentum m
    have hnum :=
      (differentiable_cmp89Eq245EntireAveragePair d (L ^ j)).comp hshift
    have hden :=
      (differentiable_cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass).comp hshift
    simpa only [cmp89Eq248ComplexAliasDenominatorSummand] using
      (hnum z).div (hden z) (hfine m (by simpa [aliases] using hm))
  simpa only [cmp89Eq249CentralStabilizedAliasDenominator,
    cmp89Eq249ComplexNoncentralAliasSum, aliases] using
    hcentralFine.add
      (hcentralAverage.const_mul (a : ℂ)) |>.add
        ((hcentralFine.const_mul (a : ℂ)).mul hsum)

/-- The complete stabilized integrand is differentiable at every point where
its two literal surviving denominator families are nonzero. -/
theorem differentiableAt_cmp89Eq251ComplexStabilizedIntegrand
    {d L j : ℕ} {mass a alpha : ℝ} {z : Fin d → ℂ} {mu : Fin d}
    {holderDisplacement transportDisplacement : Fin d → ℝ}
    (hfine : ∀ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
        (cmp89Eq249ZeroAlias d),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0) :
    DifferentiableAt ℂ (fun w : Fin d → ℂ =>
      cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha w mu
        holderDisplacement transportDisplacement) z := by
  have hnum :=
    differentiableAt_cmp89Eq251ComplexStabilizedNumerator
      (mass := mass) (alpha := alpha) (z := z) (mu := mu)
      (holderDisplacement := holderDisplacement)
      (transportDisplacement := transportDisplacement) hfine
  have hden :=
    differentiableAt_cmp89Eq249CentralStabilizedAliasDenominator
      (mass := mass) (a := a) (z := z) hfine
  simpa only [cmp89Eq251ComplexStabilizedIntegrand] using
    hnum.div hden hstabilized

end

end YangMills.RG

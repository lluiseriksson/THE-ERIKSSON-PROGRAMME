/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexRadius

/-!
# Stabilized complete complex integrand below CMP89 (2.49)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the compiler.

The expression printed in CMP89 (2.49) contains the unit-lattice symbol both
in its numerator and in the complete denominator.  Cancelling that common
factor exposes a second removable factor on the zero reciprocal alias.  This
module performs both cancellations only after assembling the literal finite
alias fibre:

* the central branch contains no fine-symbol quotient;
* every noncentral branch retains the literal ratio `Delta_0 / Delta_m`;
* the common denominator is the already sealed stabilized denominator.

The resulting expression is defined across the two removable central zeros.
An equality theorem identifies it with the printed rational integrand on the
domain where the latter is defined.  No family of integrands or free bound is
accepted as input.

This is an algebraic extension, not yet the uniform strip bound.  Noncentral
fine-symbol nonvanishing, the flowing `mass^2 <= 1` condition, the physical
`B0`, contour displacement, the Fourier/physical rate dictionary and window
15 remain separate.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Entire bilinear phase `z dot displacement` used in CMP89 (2.49). -/
def cmp89Eq251EntirePhase {d : ℕ}
    (z : Fin d → ℂ) (displacement : Fin d → ℝ) : ℂ :=
  ∑ mu, z mu * (displacement mu : ℂ)

/-- The literal numerator of one reciprocal-alias branch after removing the
unit-lattice and fine-symbol denominator factors. -/
def cmp89Eq251ComplexBareAliasNumerator
    (d L j : ℕ) (alpha : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holderDisplacement transportDisplacement : Fin d → ℝ) : ℂ :=
  let q := cmp89Eq248EntireAliasMomentum z m
  ((Complex.exp (Complex.I * cmp89Eq251EntirePhase q holderDisplacement) - 1) /
      ((cmp89Eq251EuclideanNorm holderDisplacement ^ alpha : ℝ) : ℂ)) *
    Complex.exp (Complex.I * cmp89Eq251EntirePhase q transportDisplacement) *
    cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹) (-q mu) *
    cmp89Eq245EntireAverageAmplitude d (L ^ j) q

/-- One branch of the displayed rational integrand in CMP89 (2.49), before
the removable unit and central fine-symbol cancellations. -/
def cmp89Eq251ComplexDisplayedAliasTerm
    (d L j : ℕ) (mass a alpha : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holderDisplacement transportDisplacement : Fin d → ℝ) : ℂ :=
  cmp89Eq251ComplexBareAliasNumerator d L j alpha z m mu
      holderDisplacement transportDisplacement *
      cmp89Eq249EntireUnitLaplacianSymbol d mass z /
    (cmp89Eq249ComplexFullAliasDenominator d L j mass a z *
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
        (cmp89Eq248EntireAliasMomentum z m))

/-- The literal finite alias sum displayed under the integral in CMP89
(2.49), with its two physical displacement vectors kept separate. -/
def cmp89Eq251ComplexDisplayedIntegrand
    (d L j : ℕ) (mass a alpha : ℝ) (z : Fin d → ℂ) (mu : Fin d)
    (holderDisplacement transportDisplacement : Fin d → ℝ) : ℂ :=
  ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
    cmp89Eq251ComplexDisplayedAliasTerm d L j mass a alpha z m mu
      holderDisplacement transportDisplacement

/-- The assembled numerator after the common unit-symbol cancellation and
the central fine-symbol cancellation.  Only the noncentral branches retain a
fine-symbol quotient. -/
def cmp89Eq251ComplexStabilizedNumerator
    (d L j : ℕ) (mass alpha : ℝ) (z : Fin d → ℂ) (mu : Fin d)
    (holderDisplacement transportDisplacement : Fin d → ℝ) : ℂ :=
  cmp89Eq251ComplexBareAliasNumerator d L j alpha z
      (cmp89Eq249ZeroAlias d) mu holderDisplacement transportDisplacement +
    cmp89Eq249CentralEntireFineSymbol d L j mass z *
      ∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
          (cmp89Eq249ZeroAlias d),
        cmp89Eq251ComplexBareAliasNumerator d L j alpha z m mu
            holderDisplacement transportDisplacement /
          cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum z m)

/-- The complete stabilized complex extension of the CMP89 (2.49)
integrand. -/
def cmp89Eq251ComplexStabilizedIntegrand
    (d L j : ℕ) (mass a alpha : ℝ) (z : Fin d → ℂ) (mu : Fin d)
    (holderDisplacement transportDisplacement : Fin d → ℝ) : ℂ :=
  cmp89Eq251ComplexStabilizedNumerator d L j mass alpha z mu
      holderDisplacement transportDisplacement /
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z

/-- The zero reciprocal alias does not translate complex momentum. -/
@[simp]
theorem cmp89Eq248EntireAliasMomentum_zero
    {d : ℕ} (z : Fin d → ℂ) :
    cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d) = z := by
  funext mu
  simp [cmp89Eq248EntireAliasMomentum, cmp89Eq249ZeroAlias,
    cmp89Eq245AliasShift]

/-- Termwise cancellation for an arbitrary alias on the domain of the
printed rational expression. -/
theorem cmp89Eq251ComplexDisplayedAliasTerm_eq_stabilizedTerm
    {d L j : ℕ} [NeZero L] {mass a alpha : ℝ} {z : Fin d → ℂ}
    {m : Fin d → ℤ} {mu : Fin d}
    {holderDisplacement transportDisplacement : Fin d → ℝ}
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hcentral : cmp89Eq249CentralEntireFineSymbol d L j mass z ≠ 0)
    (hfinite : cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0) :
    cmp89Eq251ComplexDisplayedAliasTerm d L j mass a alpha z m mu
        holderDisplacement transportDisplacement =
      cmp89Eq249CentralEntireFineSymbol d L j mass z *
          (cmp89Eq251ComplexBareAliasNumerator d L j alpha z m mu
              holderDisplacement transportDisplacement /
            cmp89Eq245EntireScaledLaplacianSymbol
              d (((L : ℝ) ^ j)⁻¹) mass
                (cmp89Eq248EntireAliasMomentum z m)) /
        cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z := by
  have hstabilized := cmp89Eq249CentralFine_mul_reduced_eq_stabilized
    d L j mass a z hcentral
  rw [cmp89Eq251ComplexDisplayedAliasTerm,
    cmp89Eq249ComplexFullAliasDenominator, ← hstabilized]
  field_simp [hunit, hcentral, hfinite, hreduced]

/-- On the zero alias the remaining `Delta_0 / Delta_0` factor cancels
exactly, leaving the bare central numerator over the stabilized denominator. -/
theorem cmp89Eq251ComplexDisplayedCentralTerm_eq_stabilized
    {d L j : ℕ} [NeZero L] {mass a alpha : ℝ} {z : Fin d → ℂ}
    {mu : Fin d} {holderDisplacement transportDisplacement : Fin d → ℝ}
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hcentral : cmp89Eq249CentralEntireFineSymbol d L j mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0) :
    cmp89Eq251ComplexDisplayedAliasTerm d L j mass a alpha z
        (cmp89Eq249ZeroAlias d) mu holderDisplacement transportDisplacement =
      cmp89Eq251ComplexBareAliasNumerator d L j alpha z
          (cmp89Eq249ZeroAlias d) mu holderDisplacement transportDisplacement /
        cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z := by
  have hfinite :
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) ≠ 0 := by
    simpa [cmp89Eq249CentralEntireFineSymbol] using hcentral
  rw [cmp89Eq251ComplexDisplayedAliasTerm_eq_stabilizedTerm
    hunit hcentral hfinite hreduced]
  field_simp [hfinite]

/-- Exact equality of the printed finite rational integrand and its assembled
stabilized extension wherever every denominator in the printed formula is
defined.  The stabilized right side itself remains defined across the two
cancelled central zeros. -/
theorem cmp89Eq251ComplexDisplayedIntegrand_eq_stabilized
    {d L j : ℕ} [NeZero L] {mass a alpha : ℝ} {z : Fin d → ℂ}
    {mu : Fin d} {holderDisplacement transportDisplacement : Fin d → ℝ}
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0)
    (hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    cmp89Eq251ComplexDisplayedIntegrand d L j mass a alpha z mu
        holderDisplacement transportDisplacement =
      cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha z mu
        holderDisplacement transportDisplacement := by
  let aliases := cmp89Eq245CenteredAliasVectors d (L ^ j)
  let zeroAlias := cmp89Eq249ZeroAlias d
  let bare := fun m =>
    cmp89Eq251ComplexBareAliasNumerator d L j alpha z m mu
      holderDisplacement transportDisplacement
  let fine := fun m =>
    cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
      (cmp89Eq248EntireAliasMomentum z m)
  let displayed := fun m =>
    cmp89Eq251ComplexDisplayedAliasTerm d L j mass a alpha z m mu
      holderDisplacement transportDisplacement
  let centralFine := cmp89Eq249CentralEntireFineSymbol d L j mass z
  let stabilized := cmp89Eq249CentralStabilizedAliasDenominator
    d L j mass a z
  have hzero : zeroAlias ∈ aliases := cmp89Eq249ZeroAlias_mem d L j
  have hcentral : centralFine ≠ 0 := by
    have h := hfine zeroAlias hzero
    simpa [centralFine, fine, zeroAlias,
      cmp89Eq249CentralEntireFineSymbol] using h
  have hcentralTerm : displayed zeroAlias = bare zeroAlias / stabilized := by
    exact cmp89Eq251ComplexDisplayedCentralTerm_eq_stabilized
      hunit hcentral hreduced
  have hnoncentral :
      (∑ m ∈ aliases.erase zeroAlias, displayed m) =
        ∑ m ∈ aliases.erase zeroAlias,
          centralFine * (bare m / fine m) / stabilized := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmem : m ∈ aliases := (Finset.mem_erase.mp hm).2
    exact cmp89Eq251ComplexDisplayedAliasTerm_eq_stabilizedTerm
      hunit hcentral (hfine m hmem) hreduced
  have hstabilized : stabilized ≠ 0 := by
    have hEq := cmp89Eq249CentralFine_mul_reduced_eq_stabilized
      d L j mass a z hcentral
    change cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0
    rw [← hEq]
    exact mul_ne_zero hcentral hreduced
  rw [cmp89Eq251ComplexDisplayedIntegrand,
    cmp89Eq251ComplexStabilizedIntegrand,
    cmp89Eq251ComplexStabilizedNumerator]
  change (∑ m ∈ aliases, displayed m) =
    (bare zeroAlias + centralFine * ∑ m ∈ aliases.erase zeroAlias,
      bare m / fine m) / stabilized
  rw [← Finset.sum_erase_add _ _ hzero, hnoncentral, hcentralTerm]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  field_simp [hstabilized]
  ring

end

end YangMills.RG

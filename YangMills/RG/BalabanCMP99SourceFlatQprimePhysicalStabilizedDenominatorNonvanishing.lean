/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq248ComplexAliasDenominatorPeriodicity
import YangMills.RG.BalabanCMP89Eq249NoncentralRealGap
import YangMills.RG.BalabanCMP99SourceGeneratedFullComplexAPositive
import YangMills.RG.BalabanCMP99SourceFlatQprimeCenteredAliasFibreNonvanishing

/-!
# Physical stabilized denominator nonvanishing

The mass-uniform real lower bound first proves that the stabilized denominator
is nonzero at the centered coarse representative.  For a nonzero coarse mode,
the already sealed central fine symbol then recovers the reduced denominator.
Only the complete multiplied denominator is transported through the exact
physical `2*pi` periods.  At the literal physical representative the reduced
denominator and central fine symbol are recovered separately, and their exact
product reconstructs the stabilized denominator.

For the zero coarse mode the literal physical representative is zero, so the
same real lower bound applies directly.  In particular, this module never
declares or uses periodicity of the stabilized denominator.

The last theorem specializes the coefficient to the literal internally
generated Step-7b value.  This is item 5, gate 5 only: it does not identify the
generated Green, attain window 15, discharge a terminal field, or inhabit
`TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- The explicit stabilized real-slice floor is strictly positive whenever
the averaging coefficient is strictly positive. -/
theorem cmp89Eq249CentralStabilizedLowerConstant_pos
    {d : ℕ} {a : ℝ} (ha : 0 < a) :
    0 < cmp89Eq249CentralStabilizedLowerConstant d a := by
  rw [cmp89Eq249CentralStabilizedLowerConstant]
  positivity

private theorem complex_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro hzero
  rw [hzero] at hz
  norm_num at hz

/-- At every centered coarse representative, the mass-zero stabilized
denominator has positive real part and hence is nonzero. -/
theorem cmp89Eq249CentralStabilizedAliasDenominator_massZero_ne_zero_centered
    {d M N' : ℕ} [NeZero M] [NeZero N'] {a : ℝ} (ha : 0 < a)
    (ell : FinBox d N') :
    cmp89Eq249CentralStabilizedAliasDenominator d M 1 0 a
        (fun mu =>
          (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ)) ≠ 0 := by
  let p := cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell
  have hp : ∀ mu, |p mu| ≤ Real.pi :=
    abs_cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_le_pi ell
  have hfloor :
      cmp89Eq249CentralStabilizedLowerConstant d a ≤
        (cmp89Eq249CentralStabilizedAliasDenominator d M 1 0 a
          (fun mu => (p mu : ℂ))).re :=
    cmp89Eq249CentralStabilizedLowerConstant_le_re_massUniform
      (d := d) (L := M) (j := 1) (mass := 0) (a := a) (p := p) ha.le hp
  have hre :
      0 < (cmp89Eq249CentralStabilizedAliasDenominator d M 1 0 a
        (fun mu => (p mu : ℂ))).re :=
    (cmp89Eq249CentralStabilizedLowerConstant_pos ha).trans_le hfloor
  simpa only [p] using complex_ne_zero_of_re_pos hre

/-- Coordinatewise integer physical periods preserve the complete multiplied
denominator.  This is deliberately not a periodicity theorem for the
stabilized denominator. -/
theorem cmp89Eq249ComplexFullAliasDenominator_add_intPeriods
    {d L j : ℕ} [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (w : Fin d → ℤ) :
    cmp89Eq249ComplexFullAliasDenominator d L j mass a
        (fun mu => z mu + (w mu : ℂ) * (2 * Real.pi : ℂ)) =
      cmp89Eq249ComplexFullAliasDenominator d L j mass a z := by
  classical
  let F : (Fin d → ℂ) → ℂ := fun q =>
    cmp89Eq249ComplexFullAliasDenominator d L j mass a q
  have hcoordinate : ∀ mu,
      Function.Periodic F (Pi.single mu (2 * Real.pi : ℂ)) := by
    intro mu q
    simpa [F, cmp89Eq248PhysicalCoordinatePeriodShift] using
      (cmp89Eq249ComplexFullAliasDenominator_physicalPeriodShift
        (d := d) (L := L) (j := j) mass a mu q)
  have hsum : Function.Periodic F
      (∑ mu : Fin d, (w mu) • Pi.single mu (2 * Real.pi : ℂ)) := by
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => simp [Function.Periodic]
    | @insert mu s hmu ih =>
        rw [Finset.sum_insert hmu]
        exact ((hcoordinate mu).zsmul (w mu)).add_period ih
  have hperiod := hsum z
  have hvector :
      z + (∑ mu : Fin d, (w mu) • Pi.single mu (2 * Real.pi : ℂ)) =
        fun mu => z mu + (w mu : ℂ) * (2 * Real.pi : ℂ) := by
    funext mu
    simp [Pi.single_apply, zsmul_eq_mul]
  rw [hvector] at hperiod
  exact hperiod

/-- Consumer-facing Gate-5 theorem at the literal uncentered physical coarse
momentum.  The complete denominator is the only transported object; the
stabilized denominator is rebuilt from its two literal factors. -/
theorem cmp89Eq249CentralStabilizedAliasDenominator_massZero_ne_zero_physical
    {d M N' : ℕ} [NeZero M] [NeZero N'] {a : ℝ} (ha : 0 < a)
    (ell : FinBox d N') :
    cmp89Eq249CentralStabilizedAliasDenominator d M 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0 := by
  by_cases hell : ell = 0
  · subst ell
    let p : Fin d → ℝ := fun _ => 0
    have hp : ∀ mu, |p mu| ≤ Real.pi := by
      intro mu
      simp [p, Real.pi_pos.le]
    have hfloor :
        cmp89Eq249CentralStabilizedLowerConstant d a ≤
          (cmp89Eq249CentralStabilizedAliasDenominator d M 1 0 a
            (fun mu => (p mu : ℂ))).re :=
      cmp89Eq249CentralStabilizedLowerConstant_le_re_massUniform
        (d := d) (L := M) (j := 1) (mass := 0) (a := a) (p := p) ha.le hp
    have hre :
        0 < (cmp89Eq249CentralStabilizedAliasDenominator d M 1 0 a
          (fun mu => (p mu : ℂ))).re :=
      (cmp89Eq249CentralStabilizedLowerConstant_pos ha).trans_le hfloor
    have hne := complex_ne_zero_of_re_pos hre
    have hphysicalZero :
        cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            (0 : FinBox d N') =
          fun _ => 0 := by
      funext mu
      simp [cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum]
    rw [hphysicalZero]
    simpa [p] using hne
  · let p := cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell
    let z : Fin d → ℂ := fun mu => (p mu : ℂ)
    let physical := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
    have hpCube : ∀ mu, |p mu| ≤ Real.pi :=
      abs_cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_le_pi ell
    have hp : p ≠ 0 :=
      cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_ne_zero hell
    have hstabilizedCentered :
        cmp89Eq249CentralStabilizedAliasDenominator d M 1 0 a z ≠ 0 := by
      simpa only [p, z] using
        (cmp89Eq249CentralStabilizedAliasDenominator_massZero_ne_zero_centered
          (d := d) (M := M) (N' := N') ha ell)
    have hcentralCentered :
        cmp89Eq249CentralEntireFineSymbol d M 1 0 z ≠ 0 := by
      simpa only [z] using
        (cmp89Eq249CentralEntireFineSymbol_massZero_ne_zero_ofReal
          (N := M) hpCube hp)
    have hreducedCentered :
        cmp89Eq247ComplexReducedAliasDenominator d M 1 0 a z ≠ 0 := by
      intro hreduced
      apply hstabilizedCentered
      rw [← cmp89Eq249CentralFine_mul_reduced_eq_stabilized
        d M 1 0 a z hcentralCentered, hreduced, mul_zero]
    have hunitCentered :
        cmp89Eq249EntireUnitLaplacianSymbol d 0 z ≠ 0 := by
      have hpos :=
        cmp89Eq245ScaledLaplacianSymbol_massZero_pos_of_ne_zero
          (d := d) (N := 1) (p := p) hpCube hp
      change cmp89Eq249EntireUnitLaplacianSymbol d 0
        (fun mu => (p mu : ℂ)) ≠ 0
      rw [cmp89Eq249EntireUnitLaplacianSymbol_ofReal_eq]
      apply Complex.ofReal_ne_zero.mpr
      rw [← cmp89Eq245ScaledLaplacianSymbol_one_eq_unit]
      simpa using ne_of_gt hpos
    have hfullCentered :
        cmp89Eq249ComplexFullAliasDenominator d M 1 0 a z ≠ 0 := by
      rw [cmp89Eq249ComplexFullAliasDenominator]
      exact mul_ne_zero hreducedCentered hunitCentered
    rcases
        cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_eq_centered_add_intPeriods
          ell with
      ⟨w, hw⟩
    have hfullPhysical :
        cmp89Eq249ComplexFullAliasDenominator d M 1 0 a physical ≠ 0 := by
      change cmp89Eq249ComplexFullAliasDenominator d M 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0
      rw [hw, cmp89Eq249ComplexFullAliasDenominator_add_intPeriods]
      simpa only [z, p] using hfullCentered
    have hreducedPhysical :
        cmp89Eq247ComplexReducedAliasDenominator d M 1 0 a physical ≠ 0 := by
      intro hreduced
      apply hfullPhysical
      rw [cmp89Eq249ComplexFullAliasDenominator, hreduced, zero_mul]
    have hcentralPhysical :
        cmp89Eq249CentralEntireFineSymbol d M 1 0 physical ≠ 0 := by
      let central : CMP89Eq246AliasIndex d M 1 :=
        ⟨cmp89Eq249ZeroAlias d,
          zero_mem_cmp89Eq245CenteredAliasVectors_pow d M 1⟩
      have h :=
        cmp89Eq246EntireAliasFineSymbol_massZero_ne_zero_physical
          (d := d) (M := M) (N' := N') hell central
      simpa [physical, cmp89Eq246EntireAliasFineSymbol,
        cmp89Eq249CentralEntireFineSymbol,
        central,
        cmp89Eq248EntireAliasMomentum_zero] using h
    have hproduct := mul_ne_zero hcentralPhysical hreducedPhysical
    rw [cmp89Eq249CentralFine_mul_reduced_eq_stabilized
      d M 1 0 a physical hcentralPhysical] at hproduct
    exact hproduct

/-- Literal generated Step-7b specialization: positivity of the coefficient is
constructed internally and is not an input. -/
theorem cmp99SourceGeneratedFlatPhysicalStabilizedAliasDenominator_ne_zero
    (M Q depth : ℕ) [NeZero M] [NeZero Q] :
    ∀ ell : FinBox 4 (2 * (M * Q)),
      cmp89Eq249CentralStabilizedAliasDenominator
          4 (M ^ (depth + 1)) 1 0
          (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0 := by
  intro ell
  exact
    cmp89Eq249CentralStabilizedAliasDenominator_massZero_ne_zero_physical
      (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
      (a := cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
      (cmp99SourceGeneratedFullComplexA_pos_physical M depth) ell

end

end YangMills.RG

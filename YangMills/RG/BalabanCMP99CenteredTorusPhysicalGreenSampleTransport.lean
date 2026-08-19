/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This scratch file closes the remaining pointwise dictionary between the
centered torus Green sample and the literal uncentered CMP99 physical
momentum.  It constructs the displayed-domain certificates at both
momenta and transports only the displayed Green through the integer-period
identity.  In particular, it does not declare the stabilized quotient
periodic outside its non-singular domain.

The zero and nonzero coarse fibres are separated explicitly.  No Fourier
reflection, Green bound, `B0`, window-15 attainment or terminal field is
asserted here.
-/

import YangMills.RG.BalabanCMP89Eq248CenteredGreenTorus
import YangMills.RG.BalabanCMP89Eq248DisplayedGreenVectorPeriodicity
import YangMills.RG.BalabanCMP99CenteredTorusSampleDictionary
import YangMills.RG.BalabanCMP99SourceFlatQprimeCenteredAliasFibreNonvanishing
import YangMills.RG.BalabanCMP99SourceFlatQprimeCrossFibreAliasQuotient
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- The three hypotheses under which the literal displayed Green agrees
with its stabilized extension.  Keeping this package local makes visible
that periodicity is used only after both endpoint domains are constructed.
-/
abbrev CMP99MassZeroDisplayedGreenDomain
    (K : ℕ) [NeZero K] (a : ℝ) (z : Fin 4 → ℂ) : Prop :=
  cmp89Eq249EntireUnitLaplacianSymbol 4 0 z ≠ 0 ∧
    cmp89Eq247ComplexReducedAliasDenominator 4 K 1 0 a z ≠ 0 ∧
      ∀ m ∈ cmp89Eq245CenteredAliasVectors 4 (K ^ 1),
        cmp89Eq245EntireScaledLaplacianSymbol 4
            (((K : ℝ) ^ 1)⁻¹) 0
            (cmp89Eq248EntireAliasMomentum z m) ≠ 0

/-- For a nonzero coarse mode, the centered representative belongs to the
complete mass-zero displayed domain.  All three facts are produced from
the literal centered alias geometry and the positive stabilizing
coefficient. -/
theorem cmp99MassZeroDisplayedGreenDomain_centered
    {K N' : ℕ} [NeZero K] [NeZero N'] {a : ℝ} (ha : 0 < a)
    {ell : FinBox 4 N'} (hell : ell ≠ 0) :
    CMP99MassZeroDisplayedGreenDomain K a
      (fun mu =>
        (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ)) := by
  let p := cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell
  let z : Fin 4 → ℂ := fun mu => (p mu : ℂ)
  have hpCube : ∀ mu, |p mu| ≤ Real.pi :=
    abs_cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_le_pi ell
  have hp : p ≠ 0 :=
    cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_ne_zero hell
  have hunit : cmp89Eq249EntireUnitLaplacianSymbol 4 0 z ≠ 0 := by
    have hpos :=
      cmp89Eq245ScaledLaplacianSymbol_massZero_pos_of_ne_zero
        (d := 4) (N := 1) (p := p) hpCube hp
    change cmp89Eq249EntireUnitLaplacianSymbol 4 0
      (fun mu => (p mu : ℂ)) ≠ 0
    rw [cmp89Eq249EntireUnitLaplacianSymbol_ofReal_eq]
    apply Complex.ofReal_ne_zero.mpr
    rw [← cmp89Eq245ScaledLaplacianSymbol_one_eq_unit]
    simpa using ne_of_gt hpos
  have hfine :
      ∀ m ∈ cmp89Eq245CenteredAliasVectors 4 (K ^ 1),
        cmp89Eq245EntireScaledLaplacianSymbol 4
            (((K : ℝ) ^ 1)⁻¹) 0
            (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
    intro m hm
    have h :=
      cmp89Eq245EntireAliasFibre_massZero_ne_zero_centered
        (d := 4) (M := K) (N' := N') hell
        ⟨m, by simpa only [pow_one] using hm⟩
    simpa only [pow_one, z, p] using h
  have hcentral :
      cmp89Eq249CentralEntireFineSymbol 4 K 1 0 z ≠ 0 := by
    let central : CMP89Eq246AliasIndex 4 K 1 :=
      cmp89Eq249CentralAliasIndex 4 K 1
    have h := hfine central.1 central.property
    simpa [central, cmp89Eq249CentralEntireFineSymbol,
      cmp89Eq248EntireAliasMomentum_zero] using h
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 K 1 0 a z ≠ 0 := by
    simpa only [z, p] using
      (cmp89Eq249CentralStabilizedAliasDenominator_massZero_ne_zero_centered
        (d := 4) (M := K) (N' := N') ha ell)
  have hreduced :
      cmp89Eq247ComplexReducedAliasDenominator 4 K 1 0 a z ≠ 0 := by
    intro hz
    apply hstabilized
    rw [← cmp89Eq249CentralFine_mul_reduced_eq_stabilized
      4 K 1 0 a z hcentral, hz, mul_zero]
  exact ⟨hunit, hreduced, hfine⟩

/-- For a nonzero coarse mode, the literal uncentered physical momentum
also belongs to the complete displayed domain.  The fine fibre uses its
sealed physical producer; the unit and reduced factors are recovered from
the transported complete denominator, so no factor is silently declared
periodic. -/
theorem cmp99MassZeroDisplayedGreenDomain_physical
    {K N' : ℕ} [NeZero K] [NeZero N'] {a : ℝ} (ha : 0 < a)
    {ell : FinBox 4 N'} (hell : ell ≠ 0) :
    CMP99MassZeroDisplayedGreenDomain K a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) := by
  let z : Fin 4 → ℂ := fun mu =>
    (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ)
  let physical := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  rcases cmp99MassZeroDisplayedGreenDomain_centered
      (K := K) (N' := N') ha hell with
    ⟨hunitCentered, hreducedCentered, hfineCentered⟩
  have hfullCentered :
      cmp89Eq249ComplexFullAliasDenominator 4 K 1 0 a z ≠ 0 := by
    rw [cmp89Eq249ComplexFullAliasDenominator]
    exact mul_ne_zero hreducedCentered hunitCentered
  rcases
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_eq_centered_add_intPeriods
        ell with
    ⟨w, hw⟩
  have hfullPhysical :
      cmp89Eq249ComplexFullAliasDenominator 4 K 1 0 a physical ≠ 0 := by
    change cmp89Eq249ComplexFullAliasDenominator 4 K 1 0 a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0
    rw [hw, cmp89Eq249ComplexFullAliasDenominator_add_intPeriods]
    simpa only [z] using hfullCentered
  have hunitPhysical :
      cmp89Eq249EntireUnitLaplacianSymbol 4 0 physical ≠ 0 := by
    intro hunit
    apply hfullPhysical
    rw [cmp89Eq249ComplexFullAliasDenominator, hunit, mul_zero]
  have hreducedPhysical :
      cmp89Eq247ComplexReducedAliasDenominator 4 K 1 0 a physical ≠ 0 := by
    intro hreduced
    apply hfullPhysical
    rw [cmp89Eq249ComplexFullAliasDenominator, hreduced, zero_mul]
  have hfinePhysical :
      ∀ m ∈ cmp89Eq245CenteredAliasVectors 4 (K ^ 1),
        cmp89Eq245EntireScaledLaplacianSymbol 4
            (((K : ℝ) ^ 1)⁻¹) 0
            (cmp89Eq248EntireAliasMomentum physical m) ≠ 0 := by
    intro m hm
    let mi : CMP89Eq246AliasIndex 4 K 1 := ⟨m, hm⟩
    have h :=
      cmp89Eq246EntireAliasFineSymbol_massZero_ne_zero_physical
        (d := 4) (M := K) (N' := N') hell mi
    simpa [cmp89Eq246EntireAliasFineSymbol, physical, mi] using h
  exact ⟨hunitPhysical, hreducedPhysical, hfinePhysical⟩

/-- A nonzero centered stabilized Green sample equals the literal CMP99
physical sample.  The proof exits the quotient to the displayed sum at the
centered point, uses the arbitrary integer-vector period there, and enters
the stabilized quotient again only after constructing the physical domain.
-/
theorem cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_centered_eq_physical
    {K N' : ℕ} [NeZero K] [NeZero N'] {a : ℝ} (ha : 0 < a)
    {ell : FinBox 4 N'} (hell : ell ≠ 0)
    (endpointU : Fin 4 → ℤ) :
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 K 1 0 a
        (fun mu =>
          (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ))
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((K ^ 1 : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 K 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((K ^ 1 : ℕ) : ℝ)⁻¹) endpointU) := by
  let z : Fin 4 → ℂ := fun mu =>
    (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ)
  let physical := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  rcases cmp99MassZeroDisplayedGreenDomain_centered
      (K := K) (N' := N') ha hell with
    ⟨hunitCentered, hreducedCentered, hfineCentered⟩
  rcases cmp99MassZeroDisplayedGreenDomain_physical
      (K := K) (N' := N') ha hell with
    ⟨hunitPhysical, hreducedPhysical, hfinePhysical⟩
  rcases
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_eq_centered_add_intPeriods
        ell with
    ⟨w, hw⟩
  have hshift :
      cmp89Eq248PhysicalVectorIntPeriodShift w z = physical := by
    change cmp89Eq248PhysicalVectorIntPeriodShift w z =
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
    rw [hw]
    funext mu
    simp [cmp89Eq248PhysicalVectorIntPeriodShift, z]
  have hdisplayed :
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand 4 K 1 0 a physical
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((K ^ 1 : ℕ) : ℝ)⁻¹) endpointU) =
        cmp89Eq248ComplexDisplayedGreenEndpointIntegrand 4 K 1 0 a z
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((K ^ 1 : ℕ) : ℝ)⁻¹) endpointU) := by
    rw [← hshift]
    exact
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_physicalFine_vectorIntPeriodShift_draft
        (L := K) (j := 1) 0 a w z endpointU
  change
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 K 1 0 a z _ =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 K 1 0 a physical _
  calc
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 K 1 0 a z _ =
        cmp89Eq248ComplexDisplayedGreenEndpointIntegrand 4 K 1 0 a z _ :=
      (cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_eq_stabilized
        hunitCentered hreducedCentered hfineCentered).symm
    _ = cmp89Eq248ComplexDisplayedGreenEndpointIntegrand 4 K 1 0 a physical _ :=
      hdisplayed.symm
    _ = cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 K 1 0 a physical _ :=
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_eq_stabilized
        hunitPhysical hreducedPhysical hfinePhysical

/-- The descended centered Green evaluated at the positive finite-torus
sample is the literal uncentered CMP99 physical Green sample.  The zero
fibre is discharged definitionally; no nonzero-domain theorem is applied
there. -/
theorem cmp89Eq248CenteredGreenTorus_unitSample_eq_physical
    {K N' : ℕ} [NeZero K] [NeZero N'] {a rho : ℝ}
    (ha : 0 < a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (endpointU : Fin 4 → ℤ) (ell : FinBox 4 N') :
    cmp89Eq248CenteredGreenTorus
        (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
        ha.le hrho hamplitude hradius hwindow
        (by norm_num [CMP89Eq251UniformMassWindow])
        endpointU (cmp99SourceFlatQprimeUnitTorusSample ell) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 K 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((K ^ 1 : ℕ) : ℝ)⁻¹) endpointU) := by
  let t := cmp99SourceFlatQprimeCenteredUnitCubeRepresentative ell
  have hcover :=
    cmp89Eq248CenteredGreenTorus_covering_apply
      (L := K) (j := 1) (mass := 0) (a := a) (rho := rho)
      ha.le hrho hamplitude hradius hwindow
      (by norm_num [CMP89Eq251UniformMassWindow]) endpointU t
  have hsample :=
    cmp89CenteredUnitCubeToTorus_centeredRepresentative_eq_sample ell
  rw [hsample] at hcover
  have hmom :
      (fun mu => (cmp89Eq248CenteredCubeMomentum t mu : ℂ)) =
        fun mu =>
          (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ) := by
    have hnegative :=
      cmp89Eq248NegativeTwoPiTorusMomentum_centeredRepresentative ell
    funext mu
    rw [← congrFun hnegative mu]
    simp only [t]
    unfold cmp89Eq248CenteredCubeMomentum
      cmp89Eq248NegativeTwoPiTorusMomentum
    push_cast
    ring
  rw [cmp89Eq248CenteredGreenCube, hmom] at hcover
  rw [hcover]
  by_cases hell : ell = 0
  · subst ell
    have haliasZero :
        cmp99SourceFlatQprimeSignedCenteredAliasEquiv N' (0 : Fin N') =
          ⟨0, zero_mem_cmp89Eq245CenteredAliasIntegers
            (Nat.pos_of_ne_zero (NeZero.ne N'))⟩ := by
      apply (cmp99SourceCenteredAliasResidueEquiv N').injective
      rw [cmp99SourceCenteredAliasResidueEquiv_apply,
        cmp99SourceCenteredAliasResidueEquiv_apply]
      simpa using
        (cmp99SourceFlatQprimeSignedCenteredAliasEquiv_cast_eq_neg
          N' (0 : Fin N'))
    have hz :
        (fun mu =>
          (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum
            (0 : FinBox 4 N') mu : ℂ)) =
          cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            (0 : FinBox 4 N') := by
      funext mu
      simp [cmp99SourceFlatQprimeCenteredCoarseBaseMomentum,
        cmp99SourceFlatQprimeCenteredCoarseAlias,
        cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum, haliasZero]
    exact congrArg
      (fun z =>
        cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 K 1 0 a z
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((K ^ 1 : ℕ) : ℝ)⁻¹) endpointU)) hz
  · exact
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_centered_eq_physical
        (K := K) (N' := N') ha hell endpointU

end

end YangMills.RG

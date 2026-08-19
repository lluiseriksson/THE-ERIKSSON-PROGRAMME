/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This scratch file isolates the mass-uniform replacement for the old
`mass > 0` Green holomorphy producer.  It is deliberately outside the
tracked source tree while Step 8b.22 awaits its cold terminal verdict. -/

import YangMills.RG.BalabanCMP89Eq248FineLatticeNormalizedFourierGreen
import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexFloorMassUniform
import YangMills.RG.BalabanCMP89Eq248StabilizedGreenEndpointPeriodicity
import YangMills.RG.BalabanCMP89Eq251FineLatticePhasePeriodicity
import YangMills.RG.BalabanCMP89Eq251StabilizedBoundarySeam

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- Static candidate for the mass-uniform common-radius Green producer. -/
theorem differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_of_commonRadius_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
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
    cmp89Eq249CentralStabilizedAliasDenominator_ne_zero_massUniform
      ha hrho hradius hmass hwindow hp hreal himag hamplitude
  exact
    differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
      hfine hstabilized

/-- Static candidate for the real-slice continuity consumed by a seam
extension.  Continuity is derived from the literal complex endpoint. -/
theorem continuousAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_real_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ nu, |p nu| ≤ Real.pi)
    {endpointDisplacement : Fin 4 → ℝ} :
    ContinuousAt (fun q : Fin 4 → ℝ =>
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
        (fun nu => (q nu : ℂ)) endpointDisplacement) p := by
  have houter :=
    differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_of_commonRadius_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass hp
      (z := fun nu => (p nu : ℂ))
      (by intro nu; simp)
      (by intro nu; simpa using hrho)
      (endpointDisplacement := endpointDisplacement)
  have hinner : ContinuousAt (fun q : Fin 4 → ℝ =>
      fun nu => (q nu : ℂ)) p := by
    apply Continuous.continuousAt
    apply continuous_pi
    intro nu
    exact Complex.continuous_ofReal.comp (continuous_apply nu)
  exact houter.continuousAt.comp hinner

/-- Static candidate for the complete displayed rational domain on a lower
Brillouin face.  The fine-symbol proof already works at mass zero; only the
stabilized-denominator producer is replaced. -/
theorem cmp89Eq251DisplayedDomain_of_boundaryFace_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (nu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    cmp89Eq249EntireUnitLaplacianSymbol 4 mass z ≠ 0 ∧
      cmp89Eq247ComplexReducedAliasDenominator 4 L j mass a z ≠ 0 ∧
      ∀ m ∈ cmp89Eq245CenteredAliasVectors 4 (L ^ j),
        cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
  have hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors 4 (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
    intro m hm
    exact cmp89Eq251FineSymbol_ne_zero_of_boundaryFace
      hrho hradius nu hm hp hface hreal himag
  have hcentral :
      cmp89Eq249CentralEntireFineSymbol 4 L j mass z ≠ 0 := by
    have h := hfine (cmp89Eq249ZeroAlias 4)
      (cmp89Eq249ZeroAlias_mem 4 L j)
    simpa [cmp89Eq249CentralEntireFineSymbol,
      cmp89Eq248EntireAliasMomentum_zero] using h
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z ≠ 0 :=
    cmp89Eq249CentralStabilizedAliasDenominator_ne_zero_massUniform
      ha hrho hradius hmass hwindow hp hreal himag hamplitude
  have hreduced :
      cmp89Eq247ComplexReducedAliasDenominator 4 L j mass a z ≠ 0 := by
    intro hreducedZero
    apply hstabilized
    rw [← cmp89Eq249CentralFine_mul_reduced_eq_stabilized
      4 L j mass a z hcentral, hreducedZero, mul_zero]
  have hunitFine :
      cmp89Eq245EntireScaledLaplacianSymbol 4 (((1 : ℝ) ^ 0)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias 4)) ≠ 0 :=
    cmp89Eq251FineSymbol_ne_zero_of_boundaryFace
      (L := 1) (j := 0) hrho hradius nu
        (cmp89Eq249ZeroAlias_mem 4 1 0) hp hface hreal himag
  have hunit : cmp89Eq249EntireUnitLaplacianSymbol 4 mass z ≠ 0 := by
    simpa [cmp89Eq249EntireUnitLaplacianSymbol,
      cmp89Eq248EntireAliasMomentum_zero] using hunitFine
  exact ⟨hunit, hreduced, hfine⟩

/-- Bare Green momentum factor with the endpoint on the physical fine
lattice `(1/N) Z^d`. -/
def cmp89Eq248ComplexFineLatticeBareGreenMomentumFactor_draft
    (d N : ℕ) (q : Fin d → ℂ) (endpointU : Fin d → ℤ) : ℂ :=
  Complex.exp (Complex.I * cmp89Eq251EntirePhase q
      (cmp89Eq249PhysicalFineLatticeDisplacement ((N : ℝ)⁻¹) endpointU)) *
    cmp89Eq245EntireAverageAmplitude d N q

/-- The centered-alias wrap is cancelled by the literal fine-site integer;
no unit-lattice replacement of the endpoint is used. -/
theorem cmp89Eq248ComplexFineLatticeBareGreenMomentumFactor_coordinateAliasPeriodShift_draft
    {d N : ℕ} (hN : 0 < N) (nu : Fin d) (q : Fin d → ℂ)
    (endpointU : Fin d → ℤ) :
    cmp89Eq248ComplexFineLatticeBareGreenMomentumFactor_draft d N
        (cmp89Eq251CoordinateAliasPeriodShift N nu q) endpointU =
      cmp89Eq248ComplexFineLatticeBareGreenMomentumFactor_draft
        d N q endpointU := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  unfold cmp89Eq248ComplexFineLatticeBareGreenMomentumFactor_draft
  rw [exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift_physicalFine,
    cmp89Eq245EntireAverageAmplitude_coordinateAliasPeriodShift hN]

/-- Displayed Green momentum term with fixed common denominators and a
physical fine-lattice endpoint. -/
def cmp89Eq248ComplexFineLatticeDisplayedGreenMomentumTerm_draft
    (d N : ℕ) (mass : ℝ) (unit full : ℂ) (q : Fin d → ℂ)
    (endpointU : Fin d → ℤ) : ℂ :=
  cmp89Eq248ComplexFineLatticeBareGreenMomentumFactor_draft
      d N q endpointU * unit /
    (full * cmp89Eq245EntireScaledLaplacianSymbol
      d ((N : ℝ)⁻¹) mass q)

/-- With common denominators fixed, the displayed fine-lattice Green term
has the exact centered-alias wrap period. -/
theorem cmp89Eq248ComplexFineLatticeDisplayedGreenMomentumTerm_coordinateAliasPeriodShift_draft
    {d N : ℕ} (hN : 0 < N) (mass : ℝ) (unit full : ℂ)
    (nu : Fin d) (q : Fin d → ℂ) (endpointU : Fin d → ℤ) :
    cmp89Eq248ComplexFineLatticeDisplayedGreenMomentumTerm_draft
        d N mass unit full
        (cmp89Eq251CoordinateAliasPeriodShift N nu q) endpointU =
      cmp89Eq248ComplexFineLatticeDisplayedGreenMomentumTerm_draft
        d N mass unit full q endpointU := by
  rw [cmp89Eq248ComplexFineLatticeDisplayedGreenMomentumTerm_draft,
    cmp89Eq248ComplexFineLatticeDisplayedGreenMomentumTerm_draft,
    cmp89Eq248ComplexFineLatticeBareGreenMomentumFactor_coordinateAliasPeriodShift_draft
      hN,
    cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
      hN]

/-- Exact dictionary from one literal displayed Green alias to the
fine-lattice momentum term. -/
theorem cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm_eq_fineLatticeMomentumTerm_draft
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (endpointU : Fin d → ℤ) :
    cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm d L j mass a z m
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq248ComplexFineLatticeDisplayedGreenMomentumTerm_draft
        d (L ^ j) mass
        (cmp89Eq249EntireUnitLaplacianSymbol d mass z)
        (cmp89Eq249ComplexFullAliasDenominator d L j mass a z)
        (cmp89Eq248EntireAliasMomentum z m) endpointU := by
  simp [cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm,
    cmp89Eq248ComplexBareGreenEndpointNumerator,
    cmp89Eq248ComplexFineLatticeDisplayedGreenMomentumTerm_draft,
    cmp89Eq248ComplexFineLatticeBareGreenMomentumFactor_draft]

/-- The complete displayed Green sum is physically `2*pi` periodic at every
fine-lattice displacement `u/(L^j)`. -/
theorem cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_physicalFinePeriodShift_draft
    {d L j : ℕ} [NeZero L] (mass a : ℝ)
    (nu : Fin d) (z : Fin d → ℂ) (endpointU : Fin d → ℤ) :
    cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  let unit := cmp89Eq249EntireUnitLaplacianSymbol d mass z
  let full := cmp89Eq249ComplexFullAliasDenominator d L j mass a z
  let F := fun q : Fin d → ℂ =>
    cmp89Eq248ComplexFineLatticeDisplayedGreenMomentumTerm_draft
      d (L ^ j) mass unit full q endpointU
  have hsum := cmp89Eq248AliasFactor_physicalShift_finsetSum_eq
    hN nu z F
      (fun q =>
        cmp89Eq248ComplexFineLatticeDisplayedGreenMomentumTerm_coordinateAliasPeriodShift_draft
          hN mass unit full nu q endpointU)
  rw [cmp89Eq248ComplexDisplayedGreenEndpointIntegrand,
    cmp89Eq248ComplexDisplayedGreenEndpointIntegrand]
  calc
    (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm d L j mass a
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)) =
      ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm_eq_fineLatticeMomentumTerm_draft,
          cmp89Eq249EntireUnitLaplacianSymbol_physicalPeriodShift,
          cmp89Eq249ComplexFullAliasDenominator_physicalPeriodShift]
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum z m) := hsum
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm d L j mass a z m
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm_eq_fineLatticeMomentumTerm_draft]

/-- The stabilized Green inherits the physical fine-lattice period on the
literal non-singular domain. -/
theorem cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFinePeriodShift_of_nonzero_draft
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {z : Fin d → ℂ}
    (nu : Fin d) (endpointU : Fin d → ℤ)
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0)
    (hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) := by
  have hunitShift :
      cmp89Eq249EntireUnitLaplacianSymbol d mass
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) ≠ 0 := by
    rw [cmp89Eq249EntireUnitLaplacianSymbol_physicalPeriodShift]
    exact hunit
  have hreducedShift :
      cmp89Eq247ComplexReducedAliasDenominator d L j mass a
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) ≠ 0 := by
    rw [cmp89Eq247ComplexReducedAliasDenominator_physicalPeriodShift]
    exact hreduced
  have hfineShift :=
    cmp89Eq245EntireScaledLaplacianSymbol_nonzero_physicalPeriodShift
      nu z hfine
  calc
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) :=
          (cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_eq_stabilized
            hunitShift hreducedShift hfineShift).symm
    _ = cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) :=
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_physicalFinePeriodShift_draft
        mass a nu z endpointU
    _ = cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) :=
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_eq_stabilized
        hunit hreduced hfine

/-- Static candidate for the mass-uniform fine-lattice Green face seam.  It
specializes to `mass = 0`; no global periodicity is asserted. -/
theorem cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFine_boundarySeam_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (nu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho)
    (endpointU : Fin 4 → ℤ) :
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) := by
  rcases cmp89Eq251DisplayedDomain_of_boundaryFace_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass nu hp hface hreal himag with
    ⟨hunit, hreduced, hfine⟩
  exact
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFinePeriodShift_of_nonzero_draft
      nu endpointU hunit hreduced hfine

end

end YangMills.RG

/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Physical fine-lattice periodicity for the complete Holder numerator at general
alpha.  Both the Holder and transport displacements retain the literal
spacing `(L^j)^(-1)`.  This is the missing seam dictionary below H3; it is not
a contour shift, bound, owner dictionary, regional B0, window-15 claim or
terminal field.
-/

import YangMills.RG.BalabanCMP89Eq251FineLatticeDisplayedEndpointPeriodicity
import YangMills.RG.BalabanCMP89Eq251DisplayedIntegrandPeriodicity

namespace YangMills.RG

noncomputable section

/-- Complete bare Holder momentum factor with both integer displacements
interpreted at physical spacing `1/N`. -/
def cmp89Eq249ComplexFineLatticeBareHolderMomentumFactor_draft
    (d N : ℕ) (alpha : ℝ) (q : Fin d → ℂ) (mu : Fin d)
    (holderU transportU : Fin d → ℤ) : ℂ :=
  ((Complex.exp (Complex.I * cmp89Eq251EntirePhase q
          (cmp89Eq249PhysicalFineLatticeDisplacement
            ((N : ℝ)⁻¹) holderU)) - 1) /
      ((cmp89Eq251EuclideanNorm
        (cmp89Eq249PhysicalFineLatticeDisplacement
          ((N : ℝ)⁻¹) holderU) : ℂ) ^ alpha)) *
    Complex.exp (Complex.I * cmp89Eq251EntirePhase q
      (cmp89Eq249PhysicalFineLatticeDisplacement
        ((N : ℝ)⁻¹) transportU)) *
    cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹) (-q mu) *
    cmp89Eq245EntireAverageAmplitude d N q

/-- Each literal phase and symbol in the complete fine-lattice Holder factor
has the exact centered-alias wrap period. -/
theorem
    cmp89Eq249ComplexFineLatticeBareHolderMomentumFactor_coordinateAliasPeriodShift_draft
    {d N : ℕ} (hN : 0 < N) (alpha : ℝ)
    (nu : Fin d) (q : Fin d → ℂ) (mu : Fin d)
    (holderU transportU : Fin d → ℤ) :
    cmp89Eq249ComplexFineLatticeBareHolderMomentumFactor_draft d N alpha
        (cmp89Eq251CoordinateAliasPeriodShift N nu q) mu holderU transportU =
      cmp89Eq249ComplexFineLatticeBareHolderMomentumFactor_draft d N alpha
        q mu holderU transportU := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hdiff :
      cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹)
          (-(cmp89Eq251CoordinateAliasPeriodShift N nu q) mu) =
        cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹) (-q mu) := by
    by_cases hmu : mu = nu
    · subst mu
      simpa [cmp89Eq251CoordinateAliasPeriodShift, add_comm] using
        (cmp89Eq245EntireScaledDifference_invNat_add_int_aliasPeriod
          hN (-1 : ℤ) (-q nu))
    · simp [cmp89Eq251CoordinateAliasPeriodShift, hmu]
  unfold cmp89Eq249ComplexFineLatticeBareHolderMomentumFactor_draft
  rw [exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift_physicalFine
        hN nu q holderU,
    exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift_physicalFine
        hN nu q transportU,
    hdiff, cmp89Eq245EntireAverageAmplitude_coordinateAliasPeriodShift hN]

/-- One complete displayed momentum term with the common denominators fixed. -/
def cmp89Eq249ComplexFineLatticeDisplayedHolderMomentumTerm_draft
    (d N : ℕ) (mass alpha : ℝ) (unit full : ℂ)
    (q : Fin d → ℂ) (mu : Fin d) (holderU transportU : Fin d → ℤ) : ℂ :=
  cmp89Eq249ComplexFineLatticeBareHolderMomentumFactor_draft
      d N alpha q mu holderU transportU * unit /
    (full * cmp89Eq245EntireScaledLaplacianSymbol d ((N : ℝ)⁻¹) mass q)

/-- The complete displayed fine-lattice momentum term has the exact wrap
period, with no endpoint split and no loss of the Holder numerator. -/
theorem
    cmp89Eq249ComplexFineLatticeDisplayedHolderMomentumTerm_coordinateAliasPeriodShift_draft
    {d N : ℕ} (hN : 0 < N) (mass alpha : ℝ) (unit full : ℂ)
    (nu : Fin d) (q : Fin d → ℂ) (mu : Fin d)
    (holderU transportU : Fin d → ℤ) :
    cmp89Eq249ComplexFineLatticeDisplayedHolderMomentumTerm_draft d N mass
        alpha unit full (cmp89Eq251CoordinateAliasPeriodShift N nu q) mu
        holderU transportU =
      cmp89Eq249ComplexFineLatticeDisplayedHolderMomentumTerm_draft d N mass
        alpha unit full q mu holderU transportU := by
  rw [cmp89Eq249ComplexFineLatticeDisplayedHolderMomentumTerm_draft,
    cmp89Eq249ComplexFineLatticeDisplayedHolderMomentumTerm_draft,
    cmp89Eq249ComplexFineLatticeBareHolderMomentumFactor_coordinateAliasPeriodShift_draft
      hN,
    cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
      hN]

/-- Exact dictionary from the literal complete displayed alias branch to the
fine-lattice Holder momentum term at general alpha. -/
theorem cmp89Eq251ComplexDisplayedAliasTerm_eq_fineLatticeHolderMomentumTerm_draft
    (d L j : ℕ) (mass a alpha : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holderU transportU : Fin d → ℤ) :
    cmp89Eq251ComplexDisplayedAliasTerm d L j mass a alpha z m mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU) =
      cmp89Eq249ComplexFineLatticeDisplayedHolderMomentumTerm_draft d (L ^ j)
        mass alpha (cmp89Eq249EntireUnitLaplacianSymbol d mass z)
        (cmp89Eq249ComplexFullAliasDenominator d L j mass a z)
        (cmp89Eq248EntireAliasMomentum z m) mu holderU transportU := by
  simp [cmp89Eq251ComplexDisplayedAliasTerm,
    cmp89Eq251ComplexBareEndpointNumerator,
    cmp89Eq249ComplexFineLatticeDisplayedHolderMomentumTerm_draft,
    cmp89Eq249ComplexFineLatticeBareHolderMomentumFactor_draft]

/-- The complete displayed Holder sum is periodic under a physical `2*pi`
coordinate shift when both displacements lie on `(L^j)^(-1) Z^d`. -/
theorem cmp89Eq251ComplexDisplayedIntegrand_physicalFineHolderPeriodShift_draft
    {d L j : ℕ} [NeZero L] (mass a alpha : ℝ)
    (nu : Fin d) (z : Fin d → ℂ) (mu : Fin d)
    (holderU transportU : Fin d → ℤ) :
    cmp89Eq251ComplexDisplayedIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU) =
      cmp89Eq251ComplexDisplayedIntegrand d L j mass a alpha z mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU) := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  let unit := cmp89Eq249EntireUnitLaplacianSymbol d mass z
  let full := cmp89Eq249ComplexFullAliasDenominator d L j mass a z
  let F := fun q : Fin d → ℂ =>
    cmp89Eq249ComplexFineLatticeDisplayedHolderMomentumTerm_draft d (L ^ j)
      mass alpha unit full q mu holderU transportU
  have hsum := cmp89Eq248AliasFactor_physicalShift_finsetSum_eq
    hN nu z F
      (fun q =>
        cmp89Eq249ComplexFineLatticeDisplayedHolderMomentumTerm_coordinateAliasPeriodShift_draft
          hN mass alpha unit full nu q mu holderU transportU)
  rw [cmp89Eq251ComplexDisplayedIntegrand,
    cmp89Eq251ComplexDisplayedIntegrand]
  calc
    (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq251ComplexDisplayedAliasTerm d L j mass a alpha
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m mu
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) transportU)) =
      ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq251ComplexDisplayedAliasTerm_eq_fineLatticeHolderMomentumTerm_draft,
          cmp89Eq249EntireUnitLaplacianSymbol_physicalPeriodShift,
          cmp89Eq249ComplexFullAliasDenominator_physicalPeriodShift]
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum z m) := hsum
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq251ComplexDisplayedAliasTerm d L j mass a alpha z m mu
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) transportU) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq251ComplexDisplayedAliasTerm_eq_fineLatticeHolderMomentumTerm_draft]

/-- On the literal non-singular domain, the stabilized complete Holder
integrand inherits the fine-lattice period at general alpha. -/
theorem
    cmp89Eq251ComplexStabilizedIntegrand_physicalFineHolderPeriodShift_of_nonzero_draft
    {d L j : ℕ} [NeZero L] {mass a alpha : ℝ} {z : Fin d → ℂ}
    (nu mu : Fin d) (holderU transportU : Fin d → ℤ)
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0)
    (hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU) =
      cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha z mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU) := by
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
    _ = cmp89Eq251ComplexDisplayedIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU) :=
          (cmp89Eq251ComplexDisplayedIntegrand_eq_stabilized
            hunitShift hreducedShift hfineShift).symm
    _ = cmp89Eq251ComplexDisplayedIntegrand d L j mass a alpha z mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU) :=
      cmp89Eq251ComplexDisplayedIntegrand_physicalFineHolderPeriodShift_draft
        mass a alpha nu z mu holderU transportU
    _ = cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha z mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) transportU) :=
      cmp89Eq251ComplexDisplayedIntegrand_eq_stabilized
        hunit hreduced hfine

end

end YangMills.RG

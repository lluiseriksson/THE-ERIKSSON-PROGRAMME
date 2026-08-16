/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointPeriodicity
import YangMills.RG.BalabanCMP89Eq248FineLatticeFourierGreenLeftDerivative

/-!
# Physical-period dictionary for the stabilized Green endpoint

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations have not yet been compiler verified.

The central-stabilized denominator is not periodic by itself: a physical
`2*pi` shift changes which centered alias is central.  This file therefore
follows the source-faithful route already sealed for the differentiated
endpoint.  It exposes the displayed rational Green sum on its non-singular
domain, reindexes that complete finite sum, and only then returns to the
stabilized extension.

The endpoint displacement is carried by an integer lattice vector, so the
phase period is derived rather than assumed.  No row/column identification,
cross-fibre Fourier-negation carry, Brillouin integral, regional `B0`,
window-15 conclusion, terminal-field producer or `TermSource` inhabitant is
claimed here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- One displayed Green endpoint branch before the removable central
cancellation. -/
def cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (endpointDisplacement : Fin d → ℝ) : ℂ :=
  cmp89Eq248ComplexBareGreenEndpointNumerator d L j z m
      endpointDisplacement *
      cmp89Eq249EntireUnitLaplacianSymbol d mass z /
    (cmp89Eq249ComplexFullAliasDenominator d L j mass a z *
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
        (cmp89Eq248EntireAliasMomentum z m))

/-- The literal displayed Green endpoint is the complete finite alias sum. -/
def cmp89Eq248ComplexDisplayedGreenEndpointIntegrand
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ)
    (endpointDisplacement : Fin d → ℝ) : ℂ :=
  ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
    cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm d L j mass a z m
      endpointDisplacement

/-- One displayed Green branch parameterized by an already-aliased momentum
and by its common unit/full denominators. -/
def cmp89Eq248ComplexDisplayedGreenEndpointMomentumTerm
    (d N : ℕ) (mass : ℝ) (unit full : ℂ) (q : Fin d → ℂ)
    (endpointU : Fin d → ℤ) : ℂ :=
  (Complex.exp (Complex.I * cmp89Eq251EntirePhase q
      (cmp89Eq251LatticeDisplacement endpointU)) *
      cmp89Eq245EntireAverageAmplitude d N q) * unit /
    (full * cmp89Eq245EntireScaledLaplacianSymbol d ((N : ℝ)⁻¹) mass q)

/-- With common denominators fixed, one displayed Green momentum term has the
exact centered-alias period. -/
theorem cmp89Eq248ComplexDisplayedGreenEndpointMomentumTerm_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (mass : ℝ) (unit full : ℂ)
    (nu : Fin d) (q : Fin d → ℂ) (endpointU : Fin d → ℤ) :
    cmp89Eq248ComplexDisplayedGreenEndpointMomentumTerm d N mass unit full
        (cmp89Eq251CoordinateAliasPeriodShift N nu q) endpointU =
      cmp89Eq248ComplexDisplayedGreenEndpointMomentumTerm d N mass unit full
        q endpointU := by
  unfold cmp89Eq248ComplexDisplayedGreenEndpointMomentumTerm
  rw [exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift
      N nu q endpointU,
    cmp89Eq245EntireAverageAmplitude_coordinateAliasPeriodShift hN,
    cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
      hN]

/-- Exact dictionary from the displayed Green alias branch to the named
momentum term. -/
theorem cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm_eq_momentumTerm
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (endpointU : Fin d → ℤ) :
    cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm d L j mass a z m
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq248ComplexDisplayedGreenEndpointMomentumTerm d (L ^ j) mass
        (cmp89Eq249EntireUnitLaplacianSymbol d mass z)
        (cmp89Eq249ComplexFullAliasDenominator d L j mass a z)
        (cmp89Eq248EntireAliasMomentum z m) endpointU := by
  simp [cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm,
    cmp89Eq248ComplexBareGreenEndpointNumerator,
    cmp89Eq248ComplexDisplayedGreenEndpointMomentumTerm]

/-- The literal displayed Green finite alias sum is invariant under one
physical `2*pi` coordinate shift. -/
theorem cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_physicalPeriodShift
    {d L j : ℕ} [NeZero L] (mass a : ℝ)
    (nu : Fin d) (z : Fin d → ℂ) (endpointU : Fin d → ℤ) :
    cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z)
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a z
        (cmp89Eq251LatticeDisplacement endpointU) := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  let unit := cmp89Eq249EntireUnitLaplacianSymbol d mass z
  let full := cmp89Eq249ComplexFullAliasDenominator d L j mass a z
  let F := fun q : Fin d → ℂ =>
    cmp89Eq248ComplexDisplayedGreenEndpointMomentumTerm d (L ^ j) mass
      unit full q endpointU
  have hsum := cmp89Eq248AliasFactor_physicalShift_finsetSum_eq
    hN nu z F
      (fun q =>
        cmp89Eq248ComplexDisplayedGreenEndpointMomentumTerm_coordinateAliasPeriodShift
          hN mass unit full nu q endpointU)
  rw [cmp89Eq248ComplexDisplayedGreenEndpointIntegrand,
    cmp89Eq248ComplexDisplayedGreenEndpointIntegrand]
  calc
    (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm d L j mass a
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m
          (cmp89Eq251LatticeDisplacement endpointU)) =
      ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm_eq_momentumTerm,
          cmp89Eq249EntireUnitLaplacianSymbol_physicalPeriodShift,
          cmp89Eq249ComplexFullAliasDenominator_physicalPeriodShift]
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum z m) := hsum
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm d L j mass a z m
          (cmp89Eq251LatticeDisplacement endpointU) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm_eq_momentumTerm]

/-- Termwise cancellation for a displayed Green alias on the non-singular
domain of the rational expression. -/
theorem cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm_eq_stabilizedTerm
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {z : Fin d → ℂ}
    {m : Fin d → ℤ} {endpointDisplacement : Fin d → ℝ}
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hcentral : cmp89Eq249CentralEntireFineSymbol d L j mass z ≠ 0)
    (hfinite : cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0) :
    cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm d L j mass a z m
        endpointDisplacement =
      cmp89Eq249CentralEntireFineSymbol d L j mass z *
          (cmp89Eq248ComplexBareGreenEndpointNumerator d L j z m
              endpointDisplacement /
            cmp89Eq245EntireScaledLaplacianSymbol
              d (((L : ℝ) ^ j)⁻¹) mass
                (cmp89Eq248EntireAliasMomentum z m)) /
        cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z := by
  have hstabilized := cmp89Eq249CentralFine_mul_reduced_eq_stabilized
    d L j mass a z hcentral
  rw [cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm,
    cmp89Eq249ComplexFullAliasDenominator, ← hstabilized]
  field_simp [hunit, hcentral, hfinite, hreduced]

/-- On the zero alias, the displayed Green central fine-symbol ratio
cancels. -/
theorem cmp89Eq248ComplexDisplayedGreenEndpointCentralTerm_eq_stabilized
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {z : Fin d → ℂ}
    {endpointDisplacement : Fin d → ℝ}
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hcentral : cmp89Eq249CentralEntireFineSymbol d L j mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0) :
    cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm d L j mass a z
        (cmp89Eq249ZeroAlias d) endpointDisplacement =
      cmp89Eq248ComplexBareGreenEndpointNumerator d L j z
          (cmp89Eq249ZeroAlias d) endpointDisplacement /
        cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z := by
  have hfinite :
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) ≠ 0 := by
    simpa [cmp89Eq249CentralEntireFineSymbol] using hcentral
  rw [cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm_eq_stabilizedTerm
    hunit hcentral hfinite hreduced]
  have hFineEq :
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) =
        cmp89Eq249CentralEntireFineSymbol d L j mass z := by
    rw [cmp89Eq248EntireAliasMomentum_zero]
    rfl
  rw [hFineEq]
  field_simp [hcentral]

/-- The displayed Green endpoint and its stabilized extension agree exactly
where every denominator of the displayed formula is defined. -/
theorem cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_eq_stabilized
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {z : Fin d → ℂ}
    {endpointDisplacement : Fin d → ℝ}
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0)
    (hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a z
        endpointDisplacement =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d L j mass a z
        endpointDisplacement := by
  let aliases := cmp89Eq245CenteredAliasVectors d (L ^ j)
  let zeroAlias := cmp89Eq249ZeroAlias d
  let bare := fun m =>
    cmp89Eq248ComplexBareGreenEndpointNumerator d L j z m
      endpointDisplacement
  let fine := fun m =>
    cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
      (cmp89Eq248EntireAliasMomentum z m)
  let centralFine := cmp89Eq249CentralEntireFineSymbol d L j mass z
  let stabilized :=
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z
  let displayed := fun m =>
    cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm d L j mass a z m
      endpointDisplacement
  have hzero : zeroAlias ∈ aliases := by
    exact zero_mem_cmp89Eq245CenteredAliasVectors_pow d L j
  have hcentral : centralFine ≠ 0 := by
    simpa [centralFine, fine, zeroAlias, cmp89Eq249CentralEntireFineSymbol]
      using hfine zeroAlias hzero
  have hcentralTerm : displayed zeroAlias = bare zeroAlias / stabilized := by
    exact cmp89Eq248ComplexDisplayedGreenEndpointCentralTerm_eq_stabilized
      hunit hcentral hreduced
  have hnoncentral :
      (∑ m ∈ aliases.erase zeroAlias, displayed m) =
        ∑ m ∈ aliases.erase zeroAlias,
          centralFine * (bare m / fine m) / stabilized := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmem : m ∈ aliases := (Finset.mem_erase.mp hm).2
    exact cmp89Eq248ComplexDisplayedGreenEndpointAliasTerm_eq_stabilizedTerm
      hunit hcentral (hfine m hmem) hreduced
  have hstabilized : stabilized ≠ 0 := by
    have hEq := cmp89Eq249CentralFine_mul_reduced_eq_stabilized
      d L j mass a z hcentral
    change cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0
    rw [← hEq]
    exact mul_ne_zero hcentral hreduced
  rw [cmp89Eq248ComplexDisplayedGreenEndpointIntegrand,
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand,
    cmp89Eq248ComplexStabilizedGreenEndpointNumerator]
  change (∑ m ∈ aliases, displayed m) =
    (bare zeroAlias + centralFine * ∑ m ∈ aliases.erase zeroAlias,
      bare m / fine m) / stabilized
  rw [← Finset.sum_erase_add _ _ hzero, hnoncentral, hcentralTerm]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  field_simp [hstabilized]
  ring

/-- The stabilized Green endpoint inherits the physical period on the
original non-singular domain; shifted non-singularity is derived internally. -/
theorem cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalPeriodShift_of_nonzero
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
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d L j mass a z
        (cmp89Eq251LatticeDisplacement endpointU) := by
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
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z)
        (cmp89Eq251LatticeDisplacement endpointU) :=
          (cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_eq_stabilized
            hunitShift hreducedShift hfineShift).symm
    _ = cmp89Eq248ComplexDisplayedGreenEndpointIntegrand d L j mass a z
        (cmp89Eq251LatticeDisplacement endpointU) :=
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_physicalPeriodShift
        mass a nu z endpointU
    _ = cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d L j mass a z
        (cmp89Eq251LatticeDisplacement endpointU) :=
      cmp89Eq248ComplexDisplayedGreenEndpointIntegrand_eq_stabilized
        hunit hreduced hfine

end

end YangMills.RG

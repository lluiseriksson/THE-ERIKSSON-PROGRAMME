/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointHolomorphy
import YangMills.RG.BalabanCMP89Eq251DisplayedIntegrandPeriodicity

/-!
# PRE-VALIDATION: physical periodicity of each stabilized CMP89 endpoint

The source in this module is present, but its `.olean` has not yet been
materialized and its result has not yet been verified by the Lean compiler.

Each endpoint displacement is integer lattice data.  This module constructs
the displayed endpoint alias sum, proves its exact physical `2*pi` period by
the centered-alias permutation, and only then transfers that period to the
stabilized endpoint on the literal non-singular domain.

No global periodicity of the stabilized endpoint is postulated.  The
Brillouin-face domain, endpoint seam, contour displacement, `B0`, owner
dictionary and window-15 attainment remain separate.
-/

namespace YangMills.RG

noncomputable section

/-- One endpoint numerator as a function of already-aliased momentum, with
both physical displacements represented by integer lattice data. -/
def cmp89Eq251ComplexBareEndpointMomentumFactor
    (d N : ℕ) (alpha : ℝ) (q : Fin d → ℂ) (mu : Fin d)
    (holderU endpointU : Fin d → ℤ) : ℂ :=
  (Complex.exp (Complex.I * cmp89Eq251EntirePhase q
        (cmp89Eq251LatticeDisplacement endpointU)) /
      ((cmp89Eq251EuclideanNorm
          (cmp89Eq251LatticeDisplacement holderU) ^ alpha : ℝ) : ℂ)) *
    cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹) (-q mu) *
    cmp89Eq245EntireAverageAmplitude d N q

/-- The endpoint momentum factor has the exact pointwise reciprocal-alias
period. -/
theorem cmp89Eq251ComplexBareEndpointMomentumFactor_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (alpha : ℝ)
    (nu : Fin d) (q : Fin d → ℂ) (mu : Fin d)
    (holderU endpointU : Fin d → ℤ) :
    cmp89Eq251ComplexBareEndpointMomentumFactor d N alpha
        (cmp89Eq251CoordinateAliasPeriodShift N nu q) mu holderU endpointU =
      cmp89Eq251ComplexBareEndpointMomentumFactor d N alpha q mu
        holderU endpointU := by
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
  unfold cmp89Eq251ComplexBareEndpointMomentumFactor
  rw [exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift
      N nu q endpointU,
    hdiff,
    cmp89Eq245EntireAverageAmplitude_coordinateAliasPeriodShift hN]

/-- One displayed endpoint branch before the removable central
cancellations. -/
def cmp89Eq251ComplexDisplayedEndpointAliasTerm
    (d L j : ℕ) (mass a alpha : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holderDisplacement endpointDisplacement : Fin d → ℝ) : ℂ :=
  cmp89Eq251ComplexBareEndpointNumerator d L j alpha z m mu
      holderDisplacement endpointDisplacement *
      cmp89Eq249EntireUnitLaplacianSymbol d mass z /
    (cmp89Eq249ComplexFullAliasDenominator d L j mass a z *
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
        (cmp89Eq248EntireAliasMomentum z m))

/-- The displayed endpoint integrand is the literal finite centered-alias
sum of its endpoint branches. -/
def cmp89Eq251ComplexDisplayedEndpointIntegrand
    (d L j : ℕ) (mass a alpha : ℝ) (z : Fin d → ℂ) (mu : Fin d)
    (holderDisplacement endpointDisplacement : Fin d → ℝ) : ℂ :=
  ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
    cmp89Eq251ComplexDisplayedEndpointAliasTerm d L j mass a alpha z m mu
      holderDisplacement endpointDisplacement

/-- One displayed endpoint branch parameterized by its already-aliased
momentum and common unit/full denominators. -/
def cmp89Eq251ComplexDisplayedEndpointMomentumTerm
    (d N : ℕ) (mass alpha : ℝ) (unit full : ℂ)
    (q : Fin d → ℂ) (mu : Fin d) (holderU endpointU : Fin d → ℤ) : ℂ :=
  cmp89Eq251ComplexBareEndpointMomentumFactor d N alpha q mu
      holderU endpointU * unit /
    (full * cmp89Eq245EntireScaledLaplacianSymbol d ((N : ℝ)⁻¹) mass q)

/-- With the common denominators fixed, one displayed endpoint momentum term
has the exact pointwise alias period. -/
theorem cmp89Eq251ComplexDisplayedEndpointMomentumTerm_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (mass alpha : ℝ) (unit full : ℂ)
    (nu : Fin d) (q : Fin d → ℂ) (mu : Fin d)
    (holderU endpointU : Fin d → ℤ) :
    cmp89Eq251ComplexDisplayedEndpointMomentumTerm d N mass alpha unit full
        (cmp89Eq251CoordinateAliasPeriodShift N nu q) mu holderU endpointU =
      cmp89Eq251ComplexDisplayedEndpointMomentumTerm d N mass alpha unit full
        q mu holderU endpointU := by
  rw [cmp89Eq251ComplexDisplayedEndpointMomentumTerm,
    cmp89Eq251ComplexDisplayedEndpointMomentumTerm,
    cmp89Eq251ComplexBareEndpointMomentumFactor_coordinateAliasPeriodShift
      hN,
    cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
      hN]

/-- Exact dictionary from the displayed endpoint alias branch to the named
endpoint momentum term. -/
theorem cmp89Eq251ComplexDisplayedEndpointAliasTerm_eq_momentumTerm
    (d L j : ℕ) (mass a alpha : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holderU endpointU : Fin d → ℤ) :
    cmp89Eq251ComplexDisplayedEndpointAliasTerm d L j mass a alpha z m mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq251ComplexDisplayedEndpointMomentumTerm d (L ^ j) mass alpha
        (cmp89Eq249EntireUnitLaplacianSymbol d mass z)
        (cmp89Eq249ComplexFullAliasDenominator d L j mass a z)
        (cmp89Eq248EntireAliasMomentum z m) mu holderU endpointU := by
  simp [cmp89Eq251ComplexDisplayedEndpointAliasTerm,
    cmp89Eq251ComplexBareEndpointNumerator,
    cmp89Eq251ComplexDisplayedEndpointMomentumTerm,
    cmp89Eq251ComplexBareEndpointMomentumFactor]

/-- The literal displayed endpoint finite alias sum is invariant under one
physical `2*pi` coordinate shift. -/
theorem cmp89Eq251ComplexDisplayedEndpointIntegrand_physicalPeriodShift
    {d L j : ℕ} [NeZero L] (mass a alpha : ℝ)
    (nu : Fin d) (z : Fin d → ℂ) (mu : Fin d)
    (holderU endpointU : Fin d → ℤ) :
    cmp89Eq251ComplexDisplayedEndpointIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq251ComplexDisplayedEndpointIntegrand d L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  let unit := cmp89Eq249EntireUnitLaplacianSymbol d mass z
  let full := cmp89Eq249ComplexFullAliasDenominator d L j mass a z
  let F := fun q : Fin d → ℂ =>
    cmp89Eq251ComplexDisplayedEndpointMomentumTerm d (L ^ j) mass alpha
      unit full q mu holderU endpointU
  have hsum := cmp89Eq248AliasFactor_physicalShift_finsetSum_eq
    hN nu z F
      (fun q =>
        cmp89Eq251ComplexDisplayedEndpointMomentumTerm_coordinateAliasPeriodShift
          hN mass alpha unit full nu q mu holderU endpointU)
  rw [cmp89Eq251ComplexDisplayedEndpointIntegrand,
    cmp89Eq251ComplexDisplayedEndpointIntegrand]
  calc
    (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq251ComplexDisplayedEndpointAliasTerm d L j mass a alpha
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement endpointU)) =
      ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq251ComplexDisplayedEndpointAliasTerm_eq_momentumTerm,
          cmp89Eq249EntireUnitLaplacianSymbol_physicalPeriodShift,
          cmp89Eq249ComplexFullAliasDenominator_physicalPeriodShift]
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum z m) := hsum
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq251ComplexDisplayedEndpointAliasTerm d L j mass a alpha
          z m mu (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement endpointU) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq251ComplexDisplayedEndpointAliasTerm_eq_momentumTerm]

/-- Termwise cancellation for an endpoint alias on the non-singular domain
of the displayed rational expression. -/
theorem cmp89Eq251ComplexDisplayedEndpointAliasTerm_eq_stabilizedTerm
    {d L j : ℕ} [NeZero L] {mass a alpha : ℝ} {z : Fin d → ℂ}
    {m : Fin d → ℤ} {mu : Fin d}
    {holderDisplacement endpointDisplacement : Fin d → ℝ}
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hcentral : cmp89Eq249CentralEntireFineSymbol d L j mass z ≠ 0)
    (hfinite : cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0) :
    cmp89Eq251ComplexDisplayedEndpointAliasTerm d L j mass a alpha z m mu
        holderDisplacement endpointDisplacement =
      cmp89Eq249CentralEntireFineSymbol d L j mass z *
          (cmp89Eq251ComplexBareEndpointNumerator d L j alpha z m mu
              holderDisplacement endpointDisplacement /
            cmp89Eq245EntireScaledLaplacianSymbol
              d (((L : ℝ) ^ j)⁻¹) mass
                (cmp89Eq248EntireAliasMomentum z m)) /
        cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z := by
  have hstabilized := cmp89Eq249CentralFine_mul_reduced_eq_stabilized
    d L j mass a z hcentral
  rw [cmp89Eq251ComplexDisplayedEndpointAliasTerm,
    cmp89Eq249ComplexFullAliasDenominator, ← hstabilized]
  field_simp [hunit, hcentral, hfinite, hreduced]

/-- On the zero alias, the endpoint central fine-symbol ratio cancels. -/
theorem cmp89Eq251ComplexDisplayedEndpointCentralTerm_eq_stabilized
    {d L j : ℕ} [NeZero L] {mass a alpha : ℝ} {z : Fin d → ℂ}
    {mu : Fin d} {holderDisplacement endpointDisplacement : Fin d → ℝ}
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hcentral : cmp89Eq249CentralEntireFineSymbol d L j mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0) :
    cmp89Eq251ComplexDisplayedEndpointAliasTerm d L j mass a alpha z
        (cmp89Eq249ZeroAlias d) mu holderDisplacement endpointDisplacement =
      cmp89Eq251ComplexBareEndpointNumerator d L j alpha z
          (cmp89Eq249ZeroAlias d) mu holderDisplacement
          endpointDisplacement /
        cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z := by
  have hfinite :
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) ≠ 0 := by
    simpa [cmp89Eq249CentralEntireFineSymbol] using hcentral
  rw [cmp89Eq251ComplexDisplayedEndpointAliasTerm_eq_stabilizedTerm
    hunit hcentral hfinite hreduced]
  have hFineEq :
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias d)) =
        cmp89Eq249CentralEntireFineSymbol d L j mass z := by
    rw [cmp89Eq248EntireAliasMomentum_zero]
    rfl
  rw [hFineEq]
  field_simp [hcentral]

/-- The displayed endpoint sum and its stabilized extension agree exactly
where every denominator of the displayed formula is defined. -/
theorem cmp89Eq251ComplexDisplayedEndpointIntegrand_eq_stabilized
    {d L j : ℕ} [NeZero L] {mass a alpha : ℝ} {z : Fin d → ℂ}
    {mu : Fin d} {holderDisplacement endpointDisplacement : Fin d → ℝ}
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0)
    (hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    cmp89Eq251ComplexDisplayedEndpointIntegrand d L j mass a alpha z mu
        holderDisplacement endpointDisplacement =
      cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a alpha z mu
        holderDisplacement endpointDisplacement := by
  let aliases := cmp89Eq245CenteredAliasVectors d (L ^ j)
  let zeroAlias := cmp89Eq249ZeroAlias d
  let bare := fun m =>
    cmp89Eq251ComplexBareEndpointNumerator d L j alpha z m mu
      holderDisplacement endpointDisplacement
  let fine := fun m =>
    cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
      (cmp89Eq248EntireAliasMomentum z m)
  let displayed := fun m =>
    cmp89Eq251ComplexDisplayedEndpointAliasTerm d L j mass a alpha z m mu
      holderDisplacement endpointDisplacement
  let centralFine := cmp89Eq249CentralEntireFineSymbol d L j mass z
  let stabilized := cmp89Eq249CentralStabilizedAliasDenominator
    d L j mass a z
  have hzero : zeroAlias ∈ aliases := cmp89Eq249ZeroAlias_mem d L j
  have hcentral : centralFine ≠ 0 := by
    have h := hfine zeroAlias hzero
    simpa [centralFine, fine, zeroAlias,
      cmp89Eq249CentralEntireFineSymbol] using h
  have hcentralTerm : displayed zeroAlias = bare zeroAlias / stabilized := by
    exact cmp89Eq251ComplexDisplayedEndpointCentralTerm_eq_stabilized
      hunit hcentral hreduced
  have hnoncentral :
      (∑ m ∈ aliases.erase zeroAlias, displayed m) =
        ∑ m ∈ aliases.erase zeroAlias,
          centralFine * (bare m / fine m) / stabilized := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmem : m ∈ aliases := (Finset.mem_erase.mp hm).2
    exact cmp89Eq251ComplexDisplayedEndpointAliasTerm_eq_stabilizedTerm
      hunit hcentral (hfine m hmem) hreduced
  have hstabilized : stabilized ≠ 0 := by
    have hEq := cmp89Eq249CentralFine_mul_reduced_eq_stabilized
      d L j mass a z hcentral
    change cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0
    rw [← hEq]
    exact mul_ne_zero hcentral hreduced
  rw [cmp89Eq251ComplexDisplayedEndpointIntegrand,
    cmp89Eq251ComplexStabilizedEndpointIntegrand,
    cmp89Eq251ComplexStabilizedEndpointNumerator]
  change (∑ m ∈ aliases, displayed m) =
    (bare zeroAlias + centralFine * ∑ m ∈ aliases.erase zeroAlias,
      bare m / fine m) / stabilized
  rw [← Finset.sum_erase_add _ _ hzero, hnoncentral, hcentralTerm]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  field_simp [hstabilized]
  ring

/-- The stabilized endpoint inherits the physical period on the original
non-singular domain; all shifted non-singularity is derived internally. -/
theorem cmp89Eq251ComplexStabilizedEndpointIntegrand_physicalPeriodShift_of_nonzero
    {d L j : ℕ} [NeZero L] {mass a alpha : ℝ}
    {z : Fin d → ℂ} (nu mu : Fin d) (holderU endpointU : Fin d → ℤ)
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0)
    (hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
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
    cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq251ComplexDisplayedEndpointIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) :=
          (cmp89Eq251ComplexDisplayedEndpointIntegrand_eq_stabilized
            hunitShift hreducedShift hfineShift).symm
    _ = cmp89Eq251ComplexDisplayedEndpointIntegrand d L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) :=
      cmp89Eq251ComplexDisplayedEndpointIntegrand_physicalPeriodShift
        mass a alpha nu z mu holderU endpointU
    _ = cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) :=
      cmp89Eq251ComplexDisplayedEndpointIntegrand_eq_stabilized
        hunit hreduced hfine

end

end YangMills.RG

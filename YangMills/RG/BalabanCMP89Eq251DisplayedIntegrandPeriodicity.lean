/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq248ComplexAliasDenominatorPeriodicity
import YangMills.RG.BalabanCMP89Eq249StabilizedComplexIntegrand
import YangMills.RG.BalabanCMP89Eq251LatticePhasePeriodicity

/-!
# Physical periodicity of the displayed and stabilized CMP89 integrands

Compiler verification: exact source checkpoint
`747e7c6d892ed7c6bbabb0488ca3bfd87c101af0`, cold GitHub Actions run
`31285123749` (8,452 jobs; focal and eight-declaration axiom audit exit zero;
restore and save of `.lake/build` both skipped).

The endpoint displacements in CMP89 are integer lattice data.  This module
therefore derives the `2*pi*N` period of the literal bare momentum numerator
from the already sealed lattice-phase, fine-difference and averaging periods.
The finite displayed alias sum is then transported under a physical `2*pi`
shift by the exact centered-fibre permutation.

The stabilized extension is not asserted periodic everywhere.  Its period is
proved only by identifying it with the displayed rational expression at both
endpoints.  Unit, reduced and every fine denominator are assumed nonzero at
the original endpoint; the corresponding shifted facts are derived
internally from the sealed period and permutation theorems.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal bare numerator as a function of one already-aliased momentum,
with both endpoint displacements carried by integer lattice data. -/
def cmp89Eq251ComplexBareMomentumFactor
    (d N : ℕ) (alpha : ℝ) (q : Fin d → ℂ) (mu : Fin d)
    (holderU transportU : Fin d → ℤ) : ℂ :=
  ((Complex.exp (Complex.I * cmp89Eq251EntirePhase q
          (cmp89Eq251LatticeDisplacement holderU)) - 1) /
      ((cmp89Eq251EuclideanNorm
          (cmp89Eq251LatticeDisplacement holderU) ^ alpha : ℝ) : ℂ)) *
    Complex.exp (Complex.I * cmp89Eq251EntirePhase q
      (cmp89Eq251LatticeDisplacement transportU)) *
    cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹) (-q mu) *
    cmp89Eq245EntireAverageAmplitude d N q

/-- The bare momentum numerator has the exact pointwise alias period. -/
theorem cmp89Eq251ComplexBareMomentumFactor_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (alpha : ℝ)
    (nu : Fin d) (q : Fin d → ℂ) (mu : Fin d)
    (holderU transportU : Fin d → ℤ) :
    cmp89Eq251ComplexBareMomentumFactor d N alpha
        (cmp89Eq251CoordinateAliasPeriodShift N nu q) mu
        holderU transportU =
      cmp89Eq251ComplexBareMomentumFactor d N alpha q mu
        holderU transportU := by
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
  unfold cmp89Eq251ComplexBareMomentumFactor
  rw [exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift
      N nu q holderU,
    exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift
      N nu q transportU,
    hdiff,
    cmp89Eq245EntireAverageAmplitude_coordinateAliasPeriodShift hN]

/-- One displayed branch, parameterized by the common unit and full
denominators and by an already-aliased momentum. -/
def cmp89Eq251ComplexDisplayedMomentumTerm
    (d N : ℕ) (mass alpha : ℝ) (unit full : ℂ)
    (q : Fin d → ℂ) (mu : Fin d)
    (holderU transportU : Fin d → ℤ) : ℂ :=
  cmp89Eq251ComplexBareMomentumFactor d N alpha q mu holderU transportU *
      unit /
    (full *
      cmp89Eq245EntireScaledLaplacianSymbol d ((N : ℝ)⁻¹) mass q)

/-- With the common denominators fixed, one displayed momentum term has the
exact pointwise alias period. -/
theorem cmp89Eq251ComplexDisplayedMomentumTerm_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (mass alpha : ℝ) (unit full : ℂ)
    (nu : Fin d) (q : Fin d → ℂ) (mu : Fin d)
    (holderU transportU : Fin d → ℤ) :
    cmp89Eq251ComplexDisplayedMomentumTerm d N mass alpha unit full
        (cmp89Eq251CoordinateAliasPeriodShift N nu q) mu
        holderU transportU =
      cmp89Eq251ComplexDisplayedMomentumTerm d N mass alpha unit full
        q mu holderU transportU := by
  rw [cmp89Eq251ComplexDisplayedMomentumTerm,
    cmp89Eq251ComplexDisplayedMomentumTerm,
    cmp89Eq251ComplexBareMomentumFactor_coordinateAliasPeriodShift
      hN,
    cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
      hN]

/-- Exact dictionary from the consumer's displayed alias term to the named
momentum term; only the cast `((L^j : ℕ) : ℝ) = (L : ℝ)^j` is transported. -/
theorem cmp89Eq251ComplexDisplayedAliasTerm_eq_momentumTerm
    (d L j : ℕ) (mass a alpha : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holderU transportU : Fin d → ℤ) :
    cmp89Eq251ComplexDisplayedAliasTerm d L j mass a alpha z m mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) =
      cmp89Eq251ComplexDisplayedMomentumTerm d (L ^ j) mass alpha
        (cmp89Eq249EntireUnitLaplacianSymbol d mass z)
        (cmp89Eq249ComplexFullAliasDenominator d L j mass a z)
        (cmp89Eq248EntireAliasMomentum z m) mu holderU transportU := by
  simp [cmp89Eq251ComplexDisplayedAliasTerm,
    cmp89Eq251ComplexBareAliasNumerator,
    cmp89Eq251ComplexDisplayedMomentumTerm,
    cmp89Eq251ComplexBareMomentumFactor]

/-- The literal displayed finite alias sum is invariant under a physical
`2*pi` coordinate shift. -/
theorem cmp89Eq251ComplexDisplayedIntegrand_physicalPeriodShift
    {d L j : ℕ} [NeZero L] (mass a alpha : ℝ)
    (nu : Fin d) (z : Fin d → ℂ) (mu : Fin d)
    (holderU transportU : Fin d → ℤ) :
    cmp89Eq251ComplexDisplayedIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) =
      cmp89Eq251ComplexDisplayedIntegrand d L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  let unit := cmp89Eq249EntireUnitLaplacianSymbol d mass z
  let full := cmp89Eq249ComplexFullAliasDenominator d L j mass a z
  let F := fun q : Fin d → ℂ =>
    cmp89Eq251ComplexDisplayedMomentumTerm d (L ^ j) mass alpha
      unit full q mu holderU transportU
  have hsum := cmp89Eq248AliasFactor_physicalShift_finsetSum_eq
    hN nu z F
      (fun q =>
        cmp89Eq251ComplexDisplayedMomentumTerm_coordinateAliasPeriodShift
          hN mass alpha unit full nu q mu holderU transportU)
  rw [cmp89Eq251ComplexDisplayedIntegrand,
    cmp89Eq251ComplexDisplayedIntegrand]
  calc
    (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq251ComplexDisplayedAliasTerm d L j mass a alpha
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement transportU)) =
      ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq251ComplexDisplayedAliasTerm_eq_momentumTerm,
          cmp89Eq249EntireUnitLaplacianSymbol_physicalPeriodShift,
          cmp89Eq249ComplexFullAliasDenominator_physicalPeriodShift]
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum z m) := hsum
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq251ComplexDisplayedAliasTerm d L j mass a alpha z m mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement transportU) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq251ComplexDisplayedAliasTerm_eq_momentumTerm]

/-- Fine-denominator nonvanishing on the centered alias fibre transports
across the physical period by the exact alias permutation. -/
theorem cmp89Eq245EntireScaledLaplacianSymbol_nonzero_physicalPeriodShift
    {d L j : ℕ} [NeZero L] {mass : ℝ}
    (nu : Fin d) (z : Fin d → ℂ)
    (hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    ∀ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum
            (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m) ≠ 0 := by
  intro m hm
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  let ms : {m : Fin d → ℤ //
      m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j)} := ⟨m, hm⟩
  let F := fun q : Fin d → ℂ =>
    cmp89Eq245EntireScaledLaplacianSymbol d
      (((L ^ j : ℕ) : ℝ)⁻¹) mass q
  have htransport := cmp89Eq248AliasFactor_physicalShift_eq_cycle
    hN nu z F
      (fun q =>
        cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
          hN mass nu q) ms
  have hcycle := hfine
    (cmp89Eq245CenteredAliasVectorCycle d (L ^ j) hN nu ms).1
    (cmp89Eq245CenteredAliasVectorCycle d (L ^ j) hN nu ms).2
  have hEq :
      cmp89Eq245EntireScaledLaplacianSymbol
          d (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum
              (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m) =
        cmp89Eq245EntireScaledLaplacianSymbol
          d (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum z
              (cmp89Eq245CenteredAliasVectorCycle
                d (L ^ j) hN nu ms).1) := by
    simpa [F, ms] using htransport
  rw [hEq]
  exact hcycle

/-- The stabilized extension inherits the physical period on the original
non-singular domain; shifted non-singularity is derived, not assumed. -/
theorem cmp89Eq251ComplexStabilizedIntegrand_physicalPeriodShift_of_nonzero
    {d L j : ℕ} [NeZero L] {mass a alpha : ℝ}
    {z : Fin d → ℂ} (nu mu : Fin d) (holderU transportU : Fin d → ℤ)
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0)
    (hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) =
      cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) := by
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
    cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) =
      cmp89Eq251ComplexDisplayedIntegrand d L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) :=
          (cmp89Eq251ComplexDisplayedIntegrand_eq_stabilized
            hunitShift hreducedShift hfineShift).symm
    _ = cmp89Eq251ComplexDisplayedIntegrand d L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) :=
      cmp89Eq251ComplexDisplayedIntegrand_physicalPeriodShift
        mass a alpha nu z mu holderU transportU
    _ = cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) :=
      cmp89Eq251ComplexDisplayedIntegrand_eq_stabilized
        hunit hreduced hfine

end

end YangMills.RG

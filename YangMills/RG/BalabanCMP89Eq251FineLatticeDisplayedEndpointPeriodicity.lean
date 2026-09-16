/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251FineLatticePhasePeriodicity
import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointPeriodicity

/-!
# Cold-sealed fine-lattice displayed endpoint periodicity

Compiler-verified at exact source checkpoint
`39598f7a567d268f27f57fed681800e7efce0815` by cold GitHub Actions run
`31336314604`. Restoration and saving of `.lake/build` were skipped. The focal
and audit exited zero, and all six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

CMP89 (2.49) places an integer fine-site displacement `u` at physical
spacing `(L^j)^(-1)`.  The existing displayed-endpoint periodicity theorem
uses a unit-lattice displacement and therefore cannot be installed here.
At the literal left-derivative specialization `alpha = 0`, this module keeps
the fine displacement in the endpoint phase and derives the full displayed
alias-sum period from the centered-fibre permutation.

This is displayed rational periodicity only.  Transfer to the stabilized
endpoint, boundary seam, four-coordinate contour shift, normalized
integration, physical `B0`, window-15 attainment and terminal fields remain
open.
-/

namespace YangMills.RG

noncomputable section

/-- The bare endpoint momentum factor at `alpha = 0`, with an integer
fine-site displacement interpreted at physical spacing `1/N`. -/
def cmp89Eq251ComplexFineLatticeBareEndpointMomentumFactor
    (d N : ℕ) (q : Fin d → ℂ) (mu : Fin d)
    (endpointU : Fin d → ℤ) : ℂ :=
  Complex.exp (Complex.I * cmp89Eq251EntirePhase q
      (cmp89Eq249PhysicalFineLatticeDisplacement ((N : ℝ)⁻¹) endpointU)) *
    cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹) (-q mu) *
    cmp89Eq245EntireAverageAmplitude d N q

/-- Every literal factor of the bare fine-lattice endpoint numerator has the
exact centered-alias wrap period. -/
theorem cmp89Eq251ComplexFineLatticeBareEndpointMomentumFactor_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (nu : Fin d) (q : Fin d → ℂ) (mu : Fin d)
    (endpointU : Fin d → ℤ) :
    cmp89Eq251ComplexFineLatticeBareEndpointMomentumFactor d N
        (cmp89Eq251CoordinateAliasPeriodShift N nu q) mu endpointU =
      cmp89Eq251ComplexFineLatticeBareEndpointMomentumFactor d N q mu
        endpointU := by
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
  unfold cmp89Eq251ComplexFineLatticeBareEndpointMomentumFactor
  rw [exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift_physicalFine,
    hdiff, cmp89Eq245EntireAverageAmplitude_coordinateAliasPeriodShift hN]

/-- One displayed endpoint momentum term with common denominators fixed and
the endpoint phase evaluated on the physical fine lattice. -/
def cmp89Eq251ComplexFineLatticeDisplayedEndpointMomentumTerm
    (d N : ℕ) (mass : ℝ) (unit full : ℂ)
    (q : Fin d → ℂ) (mu : Fin d) (endpointU : Fin d → ℤ) : ℂ :=
  cmp89Eq251ComplexFineLatticeBareEndpointMomentumFactor d N q mu endpointU *
      unit /
    (full * cmp89Eq245EntireScaledLaplacianSymbol d ((N : ℝ)⁻¹) mass q)

/-- With the common denominators fixed, the displayed fine-lattice momentum
term has the exact centered-alias wrap period. -/
theorem cmp89Eq251ComplexFineLatticeDisplayedEndpointMomentumTerm_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (mass : ℝ) (unit full : ℂ)
    (nu : Fin d) (q : Fin d → ℂ) (mu : Fin d)
    (endpointU : Fin d → ℤ) :
    cmp89Eq251ComplexFineLatticeDisplayedEndpointMomentumTerm d N mass
        unit full (cmp89Eq251CoordinateAliasPeriodShift N nu q) mu endpointU =
      cmp89Eq251ComplexFineLatticeDisplayedEndpointMomentumTerm d N mass
        unit full q mu endpointU := by
  rw [cmp89Eq251ComplexFineLatticeDisplayedEndpointMomentumTerm,
    cmp89Eq251ComplexFineLatticeDisplayedEndpointMomentumTerm,
    cmp89Eq251ComplexFineLatticeBareEndpointMomentumFactor_coordinateAliasPeriodShift
      hN,
    cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
      hN]

/-- Exact dictionary from the literal displayed alias branch at `alpha = 0`
to the fine-lattice endpoint momentum term.  The holder displacement is
irrelevant only because this specialization has exponent zero. -/
theorem cmp89Eq251ComplexDisplayedEndpointAliasTerm_zero_eq_fineLatticeMomentumTerm
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holderDisplacement : Fin d → ℝ)
    (endpointU : Fin d → ℤ) :
    cmp89Eq251ComplexDisplayedEndpointAliasTerm d L j mass a 0 z m mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq251ComplexFineLatticeDisplayedEndpointMomentumTerm d (L ^ j)
        mass (cmp89Eq249EntireUnitLaplacianSymbol d mass z)
        (cmp89Eq249ComplexFullAliasDenominator d L j mass a z)
        (cmp89Eq248EntireAliasMomentum z m) mu endpointU := by
  simp [cmp89Eq251ComplexDisplayedEndpointAliasTerm,
    cmp89Eq251ComplexBareEndpointNumerator,
    cmp89Eq251ComplexFineLatticeDisplayedEndpointMomentumTerm,
    cmp89Eq251ComplexFineLatticeBareEndpointMomentumFactor]

/-- The literal displayed endpoint sum at `alpha = 0` is invariant under one
physical `2*pi` coordinate shift when its endpoint lies on
`(L^j)^(-1) Z^d`. -/
theorem cmp89Eq251ComplexDisplayedEndpointIntegrand_zero_physicalFinePeriodShift
    {d L j : ℕ} [NeZero L] (mass a : ℝ)
    (nu : Fin d) (z : Fin d → ℂ) (mu : Fin d)
    (holderDisplacement : Fin d → ℝ) (endpointU : Fin d → ℤ) :
    cmp89Eq251ComplexDisplayedEndpointIntegrand d L j mass a 0
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq251ComplexDisplayedEndpointIntegrand d L j mass a 0 z mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  let unit := cmp89Eq249EntireUnitLaplacianSymbol d mass z
  let full := cmp89Eq249ComplexFullAliasDenominator d L j mass a z
  let F := fun q : Fin d → ℂ =>
    cmp89Eq251ComplexFineLatticeDisplayedEndpointMomentumTerm d (L ^ j)
      mass unit full q mu endpointU
  have hsum := cmp89Eq248AliasFactor_physicalShift_finsetSum_eq
    hN nu z F
      (fun q =>
        cmp89Eq251ComplexFineLatticeDisplayedEndpointMomentumTerm_coordinateAliasPeriodShift
          hN mass unit full nu q mu endpointU)
  rw [cmp89Eq251ComplexDisplayedEndpointIntegrand,
    cmp89Eq251ComplexDisplayedEndpointIntegrand]
  calc
    (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq251ComplexDisplayedEndpointAliasTerm d L j mass a 0
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m mu
          holderDisplacement
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)) =
      ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift nu z) m) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq251ComplexDisplayedEndpointAliasTerm_zero_eq_fineLatticeMomentumTerm,
          cmp89Eq249EntireUnitLaplacianSymbol_physicalPeriodShift,
          cmp89Eq249ComplexFullAliasDenominator_physicalPeriodShift]
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        F (cmp89Eq248EntireAliasMomentum z m) := hsum
    _ = ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq251ComplexDisplayedEndpointAliasTerm d L j mass a 0 z m mu
          holderDisplacement
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [cmp89Eq251ComplexDisplayedEndpointAliasTerm_zero_eq_fineLatticeMomentumTerm]

end

end YangMills.RG

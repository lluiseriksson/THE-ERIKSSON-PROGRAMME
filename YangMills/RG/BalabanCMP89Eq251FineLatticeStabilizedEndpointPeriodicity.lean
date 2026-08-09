/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251FineLatticeDisplayedEndpointPeriodicity

/-!
# PRE-VALIDATION: fine-lattice stabilized endpoint periodicity

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

The stabilized endpoint is not globally identified with the displayed
rational expression.  This module transfers the sealed displayed period at
`alpha = 0` only on the literal non-singular domain.  Nonvanishing at the
shifted endpoint is derived from the existing symbol periods and centered
alias permutation; it is not accepted as a second hypothesis.

The full-polydisc nonvanishing producer, boundary seam, four-coordinate
contour shift, normalized integration, physical `B0`, window-15 attainment
and terminal fields remain open.
-/

namespace YangMills.RG

noncomputable section

/-- On its displayed non-singular domain, the stabilized endpoint at
`alpha = 0` inherits the physical period for a fine-lattice displacement
`u/(L^j)`.  No global stabilized periodicity is asserted. -/
theorem cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_physicalFinePeriodShift_of_nonzero
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {z : Fin d → ℂ}
    (nu mu : Fin d) (holderDisplacement : Fin d → ℝ)
    (endpointU : Fin d → ℤ)
    (hunit : cmp89Eq249EntireUnitLaplacianSymbol d mass z ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator
        d L j mass a z ≠ 0)
    (hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0) :
    cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a 0
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a 0 z mu
        holderDisplacement
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
    cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a 0
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq251ComplexDisplayedEndpointIntegrand d L j mass a 0
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) :=
          (cmp89Eq251ComplexDisplayedEndpointIntegrand_eq_stabilized
            hunitShift hreducedShift hfineShift).symm
    _ = cmp89Eq251ComplexDisplayedEndpointIntegrand d L j mass a 0 z mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) :=
      cmp89Eq251ComplexDisplayedEndpointIntegrand_zero_physicalFinePeriodShift
        mass a nu z mu holderDisplacement endpointU
    _ = cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a 0 z mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) :=
      cmp89Eq251ComplexDisplayedEndpointIntegrand_eq_stabilized
        hunit hreduced hfine

end

end YangMills.RG

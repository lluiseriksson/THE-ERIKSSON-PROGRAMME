/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireScaledLaplacianPeriodicity
import YangMills.RG.BalabanCMP89Eq248AliasMomentumCycle
import YangMills.RG.BalabanCMP89Eq248ComplexAliasDenominator

/-!
# Physical periodicity of the complex CMP89 alias denominator

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and this result has not yet been verified by the compiler.

This module composes the separately sealed `2*pi*N` periods of the entire
averaging pair and fine Laplacian.  Their literal quotient is transported
through the centered finite-alias permutation under a physical `2*pi`
momentum shift.  The unit-lattice Laplacian is handled separately at its
different period `2*pi`; the two results give periodicity of the complete
multiplied denominator in CMP89 (2.49).

No nonvanishing assumption is needed for equality of the quotients, because
division is the total field operation in `ℂ`.  This does not prove
nonvanishing, periodicity of the displayed numerator/phase, or periodicity of
the stabilized integrand.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Literal holomorphic average/fine-Laplacian quotient at inverse integer
spacing `1/N`, before evaluation at one reciprocal alias. -/
def cmp89Eq248ComplexAliasQuotient
    (d N : ℕ) (mass : ℝ) (q : Fin d → ℂ) : ℂ :=
  cmp89Eq245EntireAveragePair d N q /
    cmp89Eq245EntireScaledLaplacianSymbol d ((N : ℝ)⁻¹) mass q

/-- The literal alias quotient has the exact pointwise period `2*pi*N`. -/
theorem cmp89Eq248ComplexAliasQuotient_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (mass : ℝ) (mu : Fin d) (q : Fin d → ℂ) :
    cmp89Eq248ComplexAliasQuotient d N mass
        (cmp89Eq251CoordinateAliasPeriodShift N mu q) =
      cmp89Eq248ComplexAliasQuotient d N mass q := by
  rw [cmp89Eq248ComplexAliasQuotient,
    cmp89Eq248ComplexAliasQuotient,
    cmp89Eq245EntireAveragePair_coordinateAliasPeriodShift hN,
    cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
      hN]

/-- The consumer's alias summand is definitionally the named quotient after
the sole cast dictionary `((L^j : ℕ) : ℝ) = (L : ℝ)^j`. -/
theorem cmp89Eq248ComplexAliasDenominatorSummand_eq_quotient
    (d L j : ℕ) (mass : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ) :
    cmp89Eq248ComplexAliasDenominatorSummand d L j mass z m =
      cmp89Eq248ComplexAliasQuotient d (L ^ j) mass
        (cmp89Eq248EntireAliasMomentum z m) := by
  simp [cmp89Eq248ComplexAliasDenominatorSummand,
    cmp89Eq248ComplexAliasQuotient]

/-- The complete finite sum of literal complex alias summands is invariant
under a physical `2*pi` shift by exact reindexing of the centered fibre. -/
theorem cmp89Eq248ComplexAliasDenominatorSum_physicalPeriodShift
    {d L j : ℕ} [NeZero L] (mass : ℝ) (mu : Fin d) (z : Fin d → ℂ) :
    (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq248ComplexAliasDenominatorSummand d L j mass
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m) =
      ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
        cmp89Eq248ComplexAliasDenominatorSummand d L j mass z m := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hsum := cmp89Eq248AliasFactor_physicalShift_finsetSum_eq
    hN mu z (cmp89Eq248ComplexAliasQuotient d (L ^ j) mass)
    (fun q =>
      cmp89Eq248ComplexAliasQuotient_coordinateAliasPeriodShift
        hN mass mu q)
  simpa only [cmp89Eq248ComplexAliasDenominatorSummand_eq_quotient] using hsum

/-- The reduced denominator in CMP89 (2.47) inherits the physical `2*pi`
period from its exactly reindexed alias sum. -/
theorem cmp89Eq247ComplexReducedAliasDenominator_physicalPeriodShift
    {d L j : ℕ} [NeZero L] (mass a : ℝ) (mu : Fin d) (z : Fin d → ℂ) :
    cmp89Eq247ComplexReducedAliasDenominator d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) =
      cmp89Eq247ComplexReducedAliasDenominator d L j mass a z := by
  unfold cmp89Eq247ComplexReducedAliasDenominator
  rw [cmp89Eq248ComplexAliasDenominatorSum_physicalPeriodShift]

/-- The entire unit-lattice Laplacian has the distinct physical coordinate
period `2*pi`. -/
theorem cmp89Eq249EntireUnitLaplacianSymbol_physicalPeriodShift
    {d : ℕ} (mass : ℝ) (mu : Fin d) (z : Fin d → ℂ) :
    cmp89Eq249EntireUnitLaplacianSymbol d mass
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) =
      cmp89Eq249EntireUnitLaplacianSymbol d mass z := by
  simpa [cmp89Eq249EntireUnitLaplacianSymbol,
    cmp89Eq248PhysicalCoordinatePeriodShift,
    cmp89Eq251CoordinateAliasPeriodShift] using
      (cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
        (N := 1) (by norm_num) mass mu z)

/-- The complete multiplied complex denominator in CMP89 (2.49) is periodic
under the physical `2*pi` coordinate shift. -/
theorem cmp89Eq249ComplexFullAliasDenominator_physicalPeriodShift
    {d L j : ℕ} [NeZero L] (mass a : ℝ) (mu : Fin d) (z : Fin d → ℂ) :
    cmp89Eq249ComplexFullAliasDenominator d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) =
      cmp89Eq249ComplexFullAliasDenominator d L j mass a z := by
  unfold cmp89Eq249ComplexFullAliasDenominator
  rw [cmp89Eq247ComplexReducedAliasDenominator_physicalPeriodShift,
    cmp89Eq249EntireUnitLaplacianSymbol_physicalPeriodShift]

end

end YangMills.RG

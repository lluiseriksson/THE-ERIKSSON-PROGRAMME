/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceStabilizedAliasQuotientBridge
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
import YangMills.RG.BalabanCMP99SourceFlatWeightedAdjointFourierOrientation

/-!
# Cross-fibre physical transport of the literal alias quotient

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations have not yet been compiler verified.

Periodic Fourier negation moves the physical fine fibre over `ell` to the
fibre over `FourierNeg ell`.  This module transports the literal rational
row solution to the literal column solution on every nonzero coarse fibre.
The signed affine carry is retained as an equality of the two already sealed
physical dictionaries; it is not replaced by fixed-fibre reflection.

The zero coarse fibre is deliberately excluded from the quotient theorem:
its central fine symbol vanishes at zero mass, so cancellation through the
literal quotient is unavailable there.  Its stabilized contribution must be
handled by the separately sealed simple-reflection theorem before the later
complete finite-sum reindexing.  This file does not perform that sum, identify
a Brillouin integral, construct regional `B0`, attain window 15, discharge a
terminal field or inhabit `TermSource`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The physical coarse base momentum at the periodic negative residue is
the negative original base momentum plus coordinatewise integer `2*pi`
periods. -/
theorem cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_fourierNeg
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') :
    ∃ w : Fin d → ℤ,
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
          (cmp99FinBoxFourierNeg ell) =
        fun mu =>
          -cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell mu +
            (w mu : ℂ) * (2 * Real.pi : ℂ) := by
  refine ⟨fun mu => if (ell mu).val = 0 then 0 else -1, ?_⟩
  funext mu
  by_cases hmu : (ell mu).val = 0
  · simp [cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum,
      cmp99FinBoxFourierNeg_apply_val, hmu]
  · have hN : 0 < N' := Nat.pos_of_ne_zero (NeZero.ne N')
    have hmuPos : 0 < (ell mu).val := Nat.pos_of_ne_zero hmu
    have hsub : N' - (ell mu).val < N' := Nat.sub_lt hN hmuPos
    have hNC : (N' : ℂ) ≠ 0 := by
      exact_mod_cast (NeZero.ne N')
    simp only [cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum,
      cmp99FinBoxFourierNeg_apply_val]
    rw [Nat.mod_eq_of_lt hsub]
    simp only [hmu, if_false, Int.cast_neg, Int.cast_one]
    push_cast
    field_simp [hNC]
    ring

/-- The reduced CMP89 denominator is invariant when the physical coarse
fibre is moved by periodic Fourier negation. -/
theorem cmp89Eq247ComplexReducedAliasDenominator_coarseFourierNeg
    {d M N' : ℕ} [NeZero M] [NeZero N'] (mass a : ℝ)
    (ell : FinBox d N') :
    cmp89Eq247ComplexReducedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
          (cmp99FinBoxFourierNeg ell)) =
      cmp89Eq247ComplexReducedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) := by
  rcases
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_fourierNeg ell with
    ⟨w, hw⟩
  rw [hw, cmp89Eq247ComplexReducedAliasDenominator_add_intPeriods,
    cmp89Eq247ComplexReducedAliasDenominator_neg]

/-- The literal symmetric periodic stencil symbol is invariant under
transported Fourier negation. -/
theorem cmp99FlatPeriodicLaplacianSymbol_fourierNeg
    {d N : ℕ} [NeZero N] (k : FinBox d N) :
    cmp99FlatPeriodicLaplacianSymbol (cmp99FinBoxFourierNeg k) =
      cmp99FlatPeriodicLaplacianSymbol k := by
  unfold cmp99FlatPeriodicLaplacianSymbol
  apply Finset.sum_congr rfl
  intro mu _
  have hcoord :
      (((cmp99FinBoxFourierNeg k mu).val : ℕ) : ZMod N) =
        -(((k mu).val : ℕ) : ZMod N) := by
    have h := congrFun (cmp99FinBoxZModEquiv_fourierNeg k) mu
    simpa only [cmp99FinBoxZModEquiv_apply, Pi.neg_apply] using h
  rw [hcoord]
  simp only [neg_neg]
  ring

/-- The physical fine diagonal itself is even under cross-fibre Fourier
negation. -/
theorem cmp99SourceFlatQprimePhysicalFineSymbol_fourierNeg
    {d M N' : ℕ} [NeZero M] [NeZero N'] (mass : ℝ)
    (k : FinBox d (M * N')) :
    cmp99SourceFlatQprimePhysicalFineSymbol mass
        (cmp99FinBoxFourierNeg k) =
      cmp99SourceFlatQprimePhysicalFineSymbol mass k := by
  rw [cmp99SourceFlatQprimePhysicalFineSymbol_eq_rescaledPeriodic,
    cmp99SourceFlatQprimePhysicalFineSymbol_eq_rescaledPeriodic]
  unfold cmp99SourceFlatQprimeRescaledPeriodicFineSymbol
  rw [cmp99FlatPeriodicLaplacianSymbol_fourierNeg]

/-- Applying the affine signed-alias carry to the input physical dictionary
is definitionally the output physical dictionary after cross-fibre Fourier
negation. -/
theorem cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv_apply_dictionary
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv d M N' ell
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell k) =
      cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N'
        (cmp99FinBoxFourierNeg ell)
        (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
          d M N' ell k) := by
  simp [cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv]

/-- On a nonzero physical coarse fibre the reduced denominator, not merely
the stabilized product, is nonzero. -/
theorem cmp89Eq247ComplexReducedAliasDenominator_massZero_ne_zero_physical
    {d M N' : ℕ} [NeZero M] [NeZero N'] {a : ℝ} (ha : 0 < a)
    {ell : FinBox d N'} (hell : ell ≠ 0) :
    cmp89Eq247ComplexReducedAliasDenominator d M 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0 := by
  let central := cmp89Eq249CentralAliasIndex d M 1
  let z := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  have hcentral : cmp89Eq249CentralEntireFineSymbol d M 1 0 z ≠ 0 := by
    have h :=
      cmp89Eq246EntireAliasFineSymbol_massZero_ne_zero_physical
        (d := d) (M := M) (N' := N') hell central
    simpa [central, z, cmp89Eq246EntireAliasFineSymbol,
      cmp89Eq249CentralEntireFineSymbol,
      cmp89Eq248EntireAliasMomentum_zero] using h
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 0 a z ≠ 0 := by
    simpa only [z] using
      (cmp89Eq249CentralStabilizedAliasDenominator_massZero_ne_zero_physical
        (d := d) (M := M) (N' := N') ha ell)
  intro hreduced
  apply hstabilized
  rw [← cmp89Eq249CentralFine_mul_reduced_eq_stabilized
    d M 1 0 a z hcentral, hreduced, mul_zero]

/-- On every nonzero coarse fibre, the literal row quotient is transported
to the literal column quotient on the periodic-negative fibre. -/
theorem cmp89Eq247EntireAliasTransposeSolution_coarseFourierNeg_eq_column
    {d M N' : ℕ} [NeZero M] [NeZero N'] (a : ℝ)
    {ell : FinBox d N'}
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp89Eq247EntireAliasTransposeSolution d M 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell k) =
      cmp89Eq247EntireAliasColumnSolution d M 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
          (cmp99FinBoxFourierNeg ell))
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N'
          (cmp99FinBoxFourierNeg ell)
          (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
            d M N' ell k)) := by
  let kneg :=
    cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv d M N' ell k
  have hnumerator :
      cmp89Eq246EntireAliasAverageRow d M 1
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
            d M N' ell k) =
        cmp89Eq246EntireAliasAverageColumn d M 1
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            (cmp99FinBoxFourierNeg ell))
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N'
            (cmp99FinBoxFourierNeg ell) kneg) := by
    rw [← cmp99SourceFlatQprimeNegAmplitude_eq_entireAliasRow ell k,
      ← cmp99SourceFlatQprimeAmplitude_eq_entireAliasColumn
        (cmp99FinBoxFourierNeg ell) kneg]
    exact
      (cmp89Eq245EntireAverageAmplitude_amplitudeMomentum_fourierNeg_eq_neg
        k.1).symm
  have hfine :
      cmp89Eq246EntireAliasFineSymbol d M 1 0
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
            d M N' ell k) =
        cmp89Eq246EntireAliasFineSymbol d M 1 0
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            (cmp99FinBoxFourierNeg ell))
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N'
            (cmp99FinBoxFourierNeg ell) kneg) := by
    rw [← cmp99SourceFlatQprimePhysicalFineSymbol_eq_entireAliasFineSymbol
        ell 0 k,
      ← cmp99SourceFlatQprimePhysicalFineSymbol_eq_entireAliasFineSymbol
        (cmp99FinBoxFourierNeg ell) 0 kneg]
    exact (cmp99SourceFlatQprimePhysicalFineSymbol_fourierNeg 0 k.1).symm
  have hreduced :=
    (cmp89Eq247ComplexReducedAliasDenominator_coarseFourierNeg
      (M := M) (mass := 0) (a := a) ell).symm
  unfold cmp89Eq247EntireAliasTransposeSolution
    cmp89Eq247EntireAliasColumnSolution
  rw [hnumerator, hfine, hreduced]

/-- The same transport for the actual stabilized physical row solution.
All quotient non-singularity is derived internally from `ell ≠ 0` and
`a > 0`; no preselected family of quotient solutions is accepted. -/
theorem cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution_coarseFourierNeg_eq_column
    {d M N' : ℕ} [NeZero M] [NeZero N'] {a : ℝ} (ha : 0 < a)
    {ell : FinBox d N'} (hell : ell ≠ 0)
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
        ell 0 a k =
      cmp89Eq249StabilizedAliasColumnSolution d M 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
          (cmp99FinBoxFourierNeg ell))
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N'
          (cmp99FinBoxFourierNeg ell)
          (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
            d M N' ell k)) := by
  have hellNeg : cmp99FinBoxFourierNeg ell ≠ 0 := by
    intro hneg
    apply hell
    rw [← cmp99FinBoxFourierNeg_fourierNeg ell, hneg]
    simp [cmp99FinBoxFourierNeg]
  have hfineIn :=
    cmp89Eq246EntireAliasFineSymbol_massZero_ne_zero_physical
      (d := d) (M := M) (N' := N') hell
  have hfineOut :=
    cmp89Eq246EntireAliasFineSymbol_massZero_ne_zero_physical
      (d := d) (M := M) (N' := N') hellNeg
  have hreducedIn :=
    cmp89Eq247ComplexReducedAliasDenominator_massZero_ne_zero_physical
      (d := d) (M := M) (N' := N') ha hell
  have hreducedOut :=
    cmp89Eq247ComplexReducedAliasDenominator_massZero_ne_zero_physical
      (d := d) (M := M) (N' := N') ha hellNeg
  have hrow :=
    cmp89Eq249StabilizedAliasTransposeSolution_eq_unstabilized
      d M 1 0 a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
      hfineIn hreducedIn
  have hcolumn :=
    cmp89Eq249StabilizedAliasColumnSolution_eq_unstabilized
      d M 1 0 a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
        (cmp99FinBoxFourierNeg ell))
      hfineOut hreducedOut
  unfold cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
  rw [congrFun hrow
      (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell k),
    congrFun hcolumn
      (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N'
        (cmp99FinBoxFourierNeg ell)
        (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
          d M N' ell k))]
  exact cmp89Eq247EntireAliasTransposeSolution_coarseFourierNeg_eq_column
    a k

end

end YangMills.RG

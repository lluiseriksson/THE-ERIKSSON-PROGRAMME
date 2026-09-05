/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249StabilizedAliasTransposeSolution
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalAliasPrecisionMatrix

/-!
# Physical central-stabilized transposed alias solution

The signed physical reciprocal-fibre dictionary transports the sealed CMP89
central-stabilized solution to the literal flat `Q'` precision matrix.  The
central physical mode is constructed as the inverse image of the printed zero
alias; it is not supplied by an enumeration or selected independently.

The resulting physical matrix equation requires nonvanishing of the physical
fine symbol only away from that central mode.  At the central mode it divides
only by the stabilized denominator, so the removable zero is crossed without
postulating that the central fine symbol is nonzero.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- The physical fine mode corresponding exactly to the printed zero alias. -/
def cmp99SourceFlatQprimePhysicalCentralAliasIndex
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N') :
    CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell :=
  (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
    d M N' ell).symm (cmp89Eq249CentralAliasIndex d M 1)

@[simp]
theorem cmp99SourceFlatQprimePhysicalCentralAliasIndex_reindex
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N') :
    cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell
        (cmp99SourceFlatQprimePhysicalCentralAliasIndex
          (d := d) (M := M) (N' := N') ell) =
      cmp89Eq249CentralAliasIndex d M 1 := by
  simp [cmp99SourceFlatQprimePhysicalCentralAliasIndex]

/-- Pullback of the sealed central-stabilized alias solution to one literal
physical fixed-coarse reciprocal fibre. -/
def cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ) :
    CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell → ℂ :=
  fun k =>
    cmp89Eq249StabilizedAliasTransposeSolution d M 1 mass a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
      (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
        d M N' ell k)

@[simp]
theorem cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution_central
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ) :
    cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
        (d := d) (M := M) (N' := N') ell mass a
        (cmp99SourceFlatQprimePhysicalCentralAliasIndex
          (d := d) (M := M) (N' := N') ell) =
      cmp89Eq246EntireAliasAverageRow d M 1
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp89Eq249CentralAliasIndex d M 1) /
        cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) := by
  simp [cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution,
    cmp89Eq249StabilizedAliasTransposeSolution_central]

/-- The pulled-back stabilized vector solves the transpose of the literal
physical alias precision matrix.  Only noncentral physical fine symbols and
the stabilized denominator are assumed nonzero. -/
theorem cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_transpose_mulVec_stabilizedSolution
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ)
    (hfine : ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
      k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
          (d := d) (M := M) (N' := N') ell →
        cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0) :
    (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
        (d := d) (M := M) (N' := N') ell mass a).transpose.mulVec
        (cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
          (d := d) (M := M) (N' := N') ell mass a) =
      fun k => cmp89Eq245EntireAverageAmplitude d M
        (-cmp99SourceFlatQprimeAmplitudeMomentum k.1) := by
  classical
  let e := cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
    d M N' ell
  let z := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  let central := cmp89Eq249CentralAliasIndex d M 1
  have hfineAlias : ∀ m : CMP89Eq246AliasIndex d M 1,
      m ≠ central →
        cmp89Eq246EntireAliasFineSymbol d M 1 mass z m ≠ 0 := by
    intro m hm
    have hphysicalNe :
        e.symm m ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
          (d := d) (M := M) (N' := N') ell := by
      intro h
      apply hm
      have heq := congrArg e h
      simpa only [e, central,
        cmp99SourceFlatQprimePhysicalCentralAliasIndex,
        Equiv.apply_symm_apply] using heq
    have hphysical := hfine (e.symm m) hphysicalNe
    rw [cmp99SourceFlatQprimePhysicalFineSymbol_eq_entireAliasFineSymbol
      (d := d) (M := M) (N' := N') ell mass (e.symm m)] at hphysical
    simpa only [z, e, Equiv.apply_symm_apply] using hphysical
  have hgeneric :=
    cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec_stabilizedSolution
      d M 1 mass a z hfineAlias hstabilized
  funext k
  change (∑ n,
      cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
          (d := d) (M := M) (N' := N') ell mass a n k *
        cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
          (d := d) (M := M) (N' := N') ell mass a n) = _
  calc
    (∑ n,
        cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
            (d := d) (M := M) (N' := N') ell mass a n k *
          cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
            (d := d) (M := M) (N' := N') ell mass a n) =
        ∑ n,
          cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a z (e n) (e k) *
            cmp89Eq249StabilizedAliasTransposeSolution
              d M 1 mass a z (e n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_entry_eq_cmp89
        (d := d) (M := M) (N' := N')]
      rfl
    _ = ∑ m,
        cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a z m (e k) *
          cmp89Eq249StabilizedAliasTransposeSolution
            d M 1 mass a z m := by
      exact Equiv.sum_comp e (fun m =>
        cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a z m (e k) *
          cmp89Eq249StabilizedAliasTransposeSolution d M 1 mass a z m)
    _ = cmp89Eq246EntireAliasAverageRow d M 1 z (e k) := by
      exact congrFun hgeneric (e k)
    _ = cmp89Eq245EntireAverageAmplitude d M
        (-cmp99SourceFlatQprimeAmplitudeMomentum k.1) := by
      exact (cmp99SourceFlatQprimeNegAmplitude_eq_entireAliasRow
        (d := d) (M := M) (N' := N') ell k).symm

end

end YangMills.RG

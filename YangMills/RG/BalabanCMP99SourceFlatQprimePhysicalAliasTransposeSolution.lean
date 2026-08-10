/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq247EntireAliasTransposeSolution
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalAliasPrecisionMatrix

/-!
# Physical specialization of the transposed CMP89 (2.47) alias solution

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and the result has not yet been verified by the Lean compiler.

The signed physical alias dictionary identifies each fixed coarse fibre with
the depth-one carrier printed in CMP89.  This module pulls the transposed
solution back through that equivalence and proves that it solves the literal
physical diagonal-plus-rank-one system against the opposite-momentum source.

The theorem remains on the nonsingular domain of the printed rational
expression.  It does not stabilize the central removable zero, construct an
inverse continuous linear map, or produce the physical uniform `B0` bound.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- Pullback of the literal CMP89 (2.47) transposed solution to one fixed
physical coarse-momentum fibre. -/
def cmp99SourceFlatQprimePhysicalAliasTransposeSolution
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ) :
    CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell → ℂ :=
  fun k =>
    cmp89Eq247EntireAliasTransposeSolution d M 1 mass a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
      (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
        d M N' ell k)

/-- On the nonsingular domain of the printed quotients, the internally
constructed physical vector solves the transpose of the literal fixed-fibre
precision matrix against the physical opposite-momentum amplitude. -/
theorem cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_transpose_mulVec_solution
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ)
    (hfine : ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
      cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator d M 1 mass a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0) :
    (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
        (d := d) (M := M) (N' := N') ell mass a).transpose.mulVec
        (cmp99SourceFlatQprimePhysicalAliasTransposeSolution
          (d := d) (M := M) (N' := N') ell mass a) =
      fun k => cmp89Eq245EntireAverageAmplitude d M
        (-cmp99SourceFlatQprimeAmplitudeMomentum k.1) := by
  classical
  let e := cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
    d M N' ell
  let z := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  have hfineAlias : ∀ m : CMP89Eq246AliasIndex d M 1,
      cmp89Eq246EntireAliasFineSymbol d M 1 mass z m ≠ 0 := by
    intro m
    have hphysical := hfine (e.symm m)
    rw [cmp99SourceFlatQprimePhysicalFineSymbol_eq_entireAliasFineSymbol
      (d := d) (M := M) (N' := N') ell mass (e.symm m)] at hphysical
    simpa only [z, e, Equiv.apply_symm_apply] using hphysical
  have hgeneric :=
    cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec_solution
      d M 1 mass a z hfineAlias hreduced
  funext k
  change (∑ n,
      cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
          (d := d) (M := M) (N' := N') ell mass a n k *
        cmp99SourceFlatQprimePhysicalAliasTransposeSolution
          (d := d) (M := M) (N' := N') ell mass a n) = _
  calc
    (∑ n,
        cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
            (d := d) (M := M) (N' := N') ell mass a n k *
          cmp99SourceFlatQprimePhysicalAliasTransposeSolution
            (d := d) (M := M) (N' := N') ell mass a n) =
        ∑ n,
          cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a z (e n) (e k) *
            cmp89Eq247EntireAliasTransposeSolution d M 1 mass a z (e n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_entry_eq_cmp89
        (d := d) (M := M) (N' := N')]
      rfl
    _ = ∑ m,
        cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a z m (e k) *
          cmp89Eq247EntireAliasTransposeSolution d M 1 mass a z m := by
      exact Equiv.sum_comp e (fun m =>
        cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a z m (e k) *
          cmp89Eq247EntireAliasTransposeSolution d M 1 mass a z m)
    _ = cmp89Eq246EntireAliasAverageRow d M 1 z (e k) := by
      exact congrFun hgeneric (e k)
    _ = cmp89Eq245EntireAverageAmplitude d M
        (-cmp99SourceFlatQprimeAmplitudeMomentum k.1) := by
      exact (cmp99SourceFlatQprimeNegAmplitude_eq_entireAliasRow
        (d := d) (M := M) (N' := N') ell k).symm

end

end YangMills.RG

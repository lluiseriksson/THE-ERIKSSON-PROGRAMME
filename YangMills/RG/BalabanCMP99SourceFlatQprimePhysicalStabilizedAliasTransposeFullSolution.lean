/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246StabilizedAliasTransposeFullSolution
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalAliasPrecisionMatrix
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution

/-!
# PRE-VALIDATION: physical arbitrary-source transposed Eq. (2.46) solution

This draft pulls the internally constructed arbitrary-source solution of the
transposed CMP89 alias matrix through the sealed signed fixed-fibre dictionary.
The source is reindexed explicitly and the literal physical matrix equation is
proved by reindexing the finite sum; no self-adjointness or inverse equality is
assumed.

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler. It remains outside the project
import graph until its own compiler and axiom gates pass.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- Pullback of the complete arbitrary-source transposed alias solution to one
literal physical fixed-coarse reciprocal fibre. -/
def cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ)
    (source : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell → ℂ) :
    CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell → ℂ :=
  let e := cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell
  let z := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  let aliasSource := fun m : CMP89Eq246AliasIndex d M 1 => source (e.symm m)
  fun k =>
    cmp89Eq246StabilizedAliasTransposeFullSolution
      d M 1 mass a z aliasSource (e k)

/-- The pulled-back vector solves the transpose of the literal physical alias
precision matrix for an arbitrary physical source. The central column gate is
derived internally from the named central pair, so no new scalar window is
introduced. -/
theorem cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_transpose_mulVec_fullSolution
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ)
    (source : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell → ℂ)
    (hfine : ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
      k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
          (d := d) (M := M) (N' := N') ell →
        cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0)
    (hpair :
      cmp89Eq249CentralEntireAveragePair d M 1
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0) :
    (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
        (d := d) (M := M) (N' := N') ell mass a).transpose.mulVec
        (cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution
          (d := d) (M := M) (N' := N') ell mass a source) =
      source := by
  classical
  let e := cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell
  let z := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  let central := cmp89Eq249CentralAliasIndex d M 1
  let aliasSource := fun m : CMP89Eq246AliasIndex d M 1 => source (e.symm m)
  let solution :=
    cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution
      (d := d) (M := M) (N' := N') ell mass a source
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
  have hcolumn :
      cmp89Eq246EntireAliasAverageColumn d M 1 z central ≠ 0 := by
    exact cmp89Eq246CentralAverageColumn_ne_zero_of_pair_ne_zero
      d M 1 z hpair
  have hgeneric :=
    cmp89Eq246EntireAliasPrecisionMatrix_transpose_mulVec_stabilizedFullSolution
      d M 1 mass a z aliasSource hfineAlias hstabilized hcolumn
  funext k
  change (∑ n,
      cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
          (d := d) (M := M) (N' := N') ell mass a n k *
        solution n) = source k
  calc
    (∑ n,
        cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
            (d := d) (M := M) (N' := N') ell mass a n k * solution n) =
        ∑ n,
          cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a z (e n) (e k) *
            cmp89Eq246StabilizedAliasTransposeFullSolution
              d M 1 mass a z aliasSource (e n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_entry_eq_cmp89
        (d := d) (M := M) (N' := N')]
      rfl
    _ = ∑ m,
        cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a z m (e k) *
          cmp89Eq246StabilizedAliasTransposeFullSolution
            d M 1 mass a z aliasSource m := by
      exact Equiv.sum_comp e (fun m =>
        cmp89Eq246EntireAliasPrecisionMatrix d M 1 mass a z m (e k) *
          cmp89Eq246StabilizedAliasTransposeFullSolution
            d M 1 mass a z aliasSource m)
    _ = aliasSource (e k) := by
      exact congrFun hgeneric (e k)
    _ = source k := by simp [aliasSource, e]

/-- Coordinatewise lift of the scalar fixed-fibre construction to the
literal complexified Lie fibre. Every Lie coordinate consumes the same
physical precision matrix and no norm conversion is introduced. -/
def cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeFullVectorSolution
    {d M N' Nc : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ)
    (source : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc) :
    CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc :=
  fun k => WithLp.toLp 2 fun A =>
    cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution
      ell mass a (fun n => source n A) k

/-- The coordinatewise vector solution satisfies the literal transposed
fixed-fibre equation. The conclusion is kept as the exact sum consumed by
the physical DFT action, rather than hidden behind a new matrix API. -/
theorem cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_transpose_sum_smul_fullVectorSolution
    {d M N' Nc : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N')
    (mass a : ℝ)
    (source : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc)
    (hfine : ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
      k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
          (d := d) (M := M) (N' := N') ell →
        cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0)
    (hpair :
      cmp89Eq249CentralEntireAveragePair d M 1
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0)
    (output : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    (∑ input,
        (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix
          (d := d) (M := M) (N' := N') ell mass a).transpose output input •
          cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeFullVectorSolution
            ell mass a source input) =
      source output := by
  ext A
  have hscalar := congrFun
    (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_transpose_mulVec_fullSolution
      ell mass a (fun k => source k A) hfine hstabilized hpair) output
  simpa only [Matrix.mulVec, dotProduct,
    cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeFullVectorSolution,
    WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul] using hscalar

end

end YangMills.RG

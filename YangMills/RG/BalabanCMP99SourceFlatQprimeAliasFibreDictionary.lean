/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245CenteredAliasVectorCycle
import YangMills.RG.BalabanCMP89Eq246EntireAliasPrecisionMatrix
import YangMills.RG.BalabanCMP99SourceFlatQprimeCoarseAlias

/-!
# PRE-VALIDATION: flat fine-momentum fibre to the printed CMP89 alias fibre

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

At fixed coarse momentum `ell`, a fine momentum in `FinBox d (M * N')` has a
unique quotient coordinate in `Fin M`.  CMP89 (2.45), however, indexes the
same reciprocal fibre by the centered half-open interval beginning at
`-floor(M / 2)`.  This module constructs the two canonical equivalences and
composes them.  In particular, the even endpoint convention is fixed by the
printed interval; no enumeration, congruence representative or alias equality
is accepted as data.

The final coordinate theorem retains both pieces of Euclidean division:
the reconstructed fine coordinate is `ell + N' * quotient`, while the CMP89
alias coordinate is `-floor(M / 2) + quotient`.  This is the dictionary needed
before forming the weighted-adjoint rank-one matrix on the alias fibre.

No weighted adjoint, `Q'^* Q'`, precision, inverse or regional Green operator
is constructed here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- Canonical equivalence from the nonnegative quotient coordinate `Fin M` to
the centered half-open reciprocal-alias interval printed in CMP89 (2.45). -/
def cmp99SourceFlatQprimeCenteredAliasEquiv (M : ℕ) [NeZero M] :
    Fin M ≃ {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers M} where
  toFun q :=
    ⟨cmp89Eq245CenteredAliasLower M + (q.1 : ℤ), by
      rw [cmp89Eq245CenteredAliasIntegers_eq_Ico, Finset.mem_Ico]
      constructor <;> omega⟩
  invFun m :=
    ⟨Int.toNat (m.1 - cmp89Eq245CenteredAliasLower M), by
      have hm : cmp89Eq245CenteredAliasLower M ≤ m.1 ∧
          m.1 < cmp89Eq245CenteredAliasLower M + (M : ℤ) := by
        simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
          Finset.mem_Ico] using m.property
      omega⟩
  left_inv q := by
    apply Fin.ext
    simp only [add_sub_cancel_left, Int.toNat_natCast]
  right_inv m := by
    apply Subtype.ext
    have hm : cmp89Eq245CenteredAliasLower M ≤ m.1 ∧
        m.1 < cmp89Eq245CenteredAliasLower M + (M : ℤ) := by
      simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
        Finset.mem_Ico] using m.property
    have hnonneg : 0 ≤ m.1 - cmp89Eq245CenteredAliasLower M := by omega
    simp only
    rw [Int.toNat_of_nonneg hnonneg]
    omega

@[simp]
theorem cmp99SourceFlatQprimeCenteredAliasEquiv_apply_val
    (M : ℕ) [NeZero M] (q : Fin M) :
    (cmp99SourceFlatQprimeCenteredAliasEquiv M q).1 =
      cmp89Eq245CenteredAliasLower M + (q.1 : ℤ) := rfl

/-- At fixed coarse momentum, Euclidean quotient and reconstruction give an
actual equivalence between its fine-momentum fibre and `FinBox d M`. -/
def cmp99SourceFlatQprimeFixedCoarseFibreEquiv
    (d M N' : ℕ) [NeZero M] [NeZero N']
    (ell : FinBox d N') :
    {k : FinBox d (M * N') // cmp99SourceFlatQprimeCoarseAlias k = ell} ≃
      FinBox d M where
  toFun k mu := (k.1 mu).divNat
  invFun q :=
    ⟨fun mu => finProdFinEquiv (q mu, ell mu), by
      funext mu
      apply Fin.ext
      change (ell mu).val % N' = (ell mu).val
      exact Nat.mod_eq_of_lt (ell mu).isLt
    ⟩
  left_inv k := by
    apply Subtype.ext
    funext mu
    have hmod : (k.1 mu).modNat = ell mu := by
      apply Fin.ext
      change (k.1 mu).val % N' = (ell mu).val
      exact congrArg Fin.val (congrFun k.property mu)
    change finProdFinEquiv ((k.1 mu).divNat, ell mu) = k.1 mu
    rw [← hmod]
    exact Equiv.apply_symm_apply finProdFinEquiv (k.1 mu)
  right_inv q := by
    funext mu
    change (finProdFinEquiv (q mu, ell mu)).divNat = q mu
    exact congrArg Prod.fst
      (Equiv.symm_apply_apply finProdFinEquiv (q mu, ell mu))

@[simp]
theorem cmp99SourceFlatQprimeFixedCoarseFibreEquiv_apply_val
    (d M N' : ℕ) [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : {k : FinBox d (M * N') //
      cmp99SourceFlatQprimeCoarseAlias k = ell}) (mu : Fin d) :
    (cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N' ell k mu).val =
      (k.1 mu).divNat.val := rfl

/-- Reconstructing from the nonnegative quotient retains the literal
Euclidean decomposition `ell + N' * quotient`. -/
@[simp]
theorem cmp99SourceFlatQprimeFixedCoarseFibreEquiv_symm_apply_val
    (d M N' : ℕ) [NeZero M] [NeZero N']
    (ell : FinBox d N') (q : FinBox d M) (mu : Fin d) :
    (((cmp99SourceFlatQprimeFixedCoarseFibreEquiv
        d M N' ell).symm q).1 mu).val =
      (ell mu).val + N' * (q mu).val := rfl

/-- The source-faithful dictionary between fine momenta with a fixed coarse
alias and the centered CMP89 alias index at one block-averaging step. -/
def cmp99SourceFlatQprimeFixedCoarseAliasIndexEquiv
    (d M N' : ℕ) [NeZero M] [NeZero N']
    (ell : FinBox d N') :
    {k : FinBox d (M * N') // cmp99SourceFlatQprimeCoarseAlias k = ell} ≃
      CMP89Eq246AliasIndex d M 1 := by
  let e :
      {k : FinBox d (M * N') // cmp99SourceFlatQprimeCoarseAlias k = ell} ≃
        {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d M} :=
    (cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N' ell).trans
      ((Equiv.piCongrRight fun _ : Fin d =>
          cmp99SourceFlatQprimeCenteredAliasEquiv M).trans
        (cmp89Eq245CenteredAliasVectorPiEquiv d M).symm)
  simpa only [CMP89Eq246AliasIndex, pow_one] using e

/-- The inverse dictionary lands in the requested coarse-alias fibre by
construction, rather than by an assumed congruence. -/
theorem cmp99SourceFlatQprimeFixedCoarseAliasIndexEquiv_symm_coarseAlias
    (d M N' : ℕ) [NeZero M] [NeZero N']
    (ell : FinBox d N') (m : CMP89Eq246AliasIndex d M 1) :
    cmp99SourceFlatQprimeCoarseAlias
        ((cmp99SourceFlatQprimeFixedCoarseAliasIndexEquiv
          d M N' ell).symm m).1 = ell :=
  ((cmp99SourceFlatQprimeFixedCoarseAliasIndexEquiv
    d M N' ell).symm m).property

end

end YangMills.RG

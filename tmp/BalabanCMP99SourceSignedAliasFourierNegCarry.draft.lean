import YangMills.RG.BalabanCMP99SourceCoarseFibreFourierNeg
import YangMills.RG.BalabanCMP99SourceFlatQprimeSignedAliasMomentumDictionary

namespace YangMills.RG

noncomputable section

/- Draft only.  This conjugate constructs the exact alias permutation induced
by physical fine-momentum negation at coarse residue `ell`.  It is not yet an
acceptance proof for the closed-form `-q` / `-q-1` quotient law. -/
def cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv
    (d M N' : ℕ) [NeZero M] [NeZero N']
    (ell : FinBox d N') :
    Equiv.Perm (CMP89Eq246AliasIndex d M 1) :=
  (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
      d M N' ell).symm.trans
    ((cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
        d M N' ell).trans
      (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
        d M N' (cmp99FinBoxFourierNeg ell)))

/- The exact commuting square with the two signed physical-fibre
dictionaries.  This states construction, not the affine carry formula. -/
@[simp]
theorem cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv_apply
    (d M N' : ℕ) [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : {k : FinBox d (M * N') //
      cmp99SourceFlatQprimeCoarseAlias k = ell}) :
    cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv d M N' ell
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell k) =
      cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
        d M N' (cmp99FinBoxFourierNeg ell)
        (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
          d M N' ell k) := by
  simp [cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv]

/- Complete alias sums may be reindexed by the *coarse-dependent* physical
carry permutation. -/
theorem cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv_sum
    {A : Type*} [AddCommMonoid A]
    (d M N' : ℕ) [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (f : CMP89Eq246AliasIndex d M 1 → A) :
    ∑ m, f (cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv
      d M N' ell m) = ∑ m, f m := by
  exact Equiv.sum_comp
    (cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv d M N' ell) f

end

end YangMills.RG

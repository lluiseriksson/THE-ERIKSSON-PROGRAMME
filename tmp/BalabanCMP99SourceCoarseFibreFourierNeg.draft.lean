import YangMills.RG.BalabanCMP99SourceCenteredAliasReflection
import YangMills.RG.BalabanCMP99SourceFlatWeightedAdjointScalarColumn

namespace YangMills.RG

noncomputable section

/-- Draft gate: periodic Fourier negation is an involution on the literal
`FinBox` carrier. -/
theorem cmp99FinBoxFourierNeg_fourierNeg
    {d N : ℕ} [NeZero N] (k : FinBox d N) :
    cmp99FinBoxFourierNeg (cmp99FinBoxFourierNeg k) = k := by
  apply (cmp99FinBoxZModEquiv d N).injective
  simp only [cmp99FinBoxZModEquiv_fourierNeg, neg_neg]

/-- Draft gate: coarse reciprocal projection commutes with the transported
periodic Fourier negation.  This is the bridge that moves, rather than fixes,
the physical coarse fibre. -/
theorem cmp99SourceFlatQprimeCoarseAlias_fourierNeg
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (k : FinBox d (M * N')) :
    cmp99SourceFlatQprimeCoarseAlias (cmp99FinBoxFourierNeg k) =
      cmp99FinBoxFourierNeg (cmp99SourceFlatQprimeCoarseAlias k) := by
  apply (cmp99FinBoxZModEquiv d N').injective
  rw [cmp99FinBoxZModEquiv_fourierNeg]
  funext mu
  change
    ((((cmp99FinBoxFourierNeg k) mu).val % N' : ℕ) : ZMod N') =
      -((((k mu).val % N' : ℕ) : ZMod N'))
  rw [ZMod.natCast_mod, ZMod.natCast_mod]
  have h := congrFun (cmp99FinBoxZModEquiv_fourierNeg k) mu
  simpa only [cmp99FinBoxZModEquiv_apply] using h

/-- Draft gate: physical momentum negation is an equivalence from the fine
fibre over `ell` to the distinct fibre over its periodic negative. -/
def cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
    (d M N' : ℕ) [NeZero M] [NeZero N']
    (ell : FinBox d N') :
    {k : FinBox d (M * N') // cmp99SourceFlatQprimeCoarseAlias k = ell} ≃
      {k : FinBox d (M * N') //
        cmp99SourceFlatQprimeCoarseAlias k = cmp99FinBoxFourierNeg ell} where
  toFun k := ⟨cmp99FinBoxFourierNeg k.1, by
    rw [cmp99SourceFlatQprimeCoarseAlias_fourierNeg, k.property]⟩
  invFun k := ⟨cmp99FinBoxFourierNeg k.1, by
    rw [cmp99SourceFlatQprimeCoarseAlias_fourierNeg, k.property,
      cmp99FinBoxFourierNeg_fourierNeg]⟩
  left_inv k := by
    apply Subtype.ext
    exact cmp99FinBoxFourierNeg_fourierNeg k.1
  right_inv k := by
    apply Subtype.ext
    exact cmp99FinBoxFourierNeg_fourierNeg k.1

end

end YangMills.RG

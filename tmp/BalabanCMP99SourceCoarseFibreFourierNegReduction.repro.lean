import YangMills.RG.BalabanCMP99SourceFlatQprimeCoarseAlias
import YangMills.RG.BalabanCMP99SourceFlatWeightedAdjointScalarColumn

namespace YangMills.RG

open YangMills

noncomputable section

-- Minimal elaboration gate for the modulus-reduction step.  The production
-- theorem keeps the same statement; this file only tests the canonical
-- `ZMod (M * N') -> ZMod N'` transport before another full focal.
example
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
  have hdiv : N' ∣ M * N' := dvd_mul_left N' M
  have hcast := congrArg (ZMod.castHom hdiv (ZMod N')) h
  simpa only [cmp99FinBoxZModEquiv_apply, map_neg, map_natCast] using hcast

end

end YangMills.RG

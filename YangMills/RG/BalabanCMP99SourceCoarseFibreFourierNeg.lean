/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimeCoarseAlias
import YangMills.RG.BalabanCMP99SourceFlatWeightedAdjointScalarColumn

/-!
# Periodic Fourier negation between coarse momentum fibres

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations have not yet been compiler verified.

Physical momentum negation does not preserve a fixed coarse reciprocal
fibre.  This module proves the exact replacement: periodic Fourier negation
maps the fine fibre over `ell` equivalently onto the fibre over
`cmp99FinBoxFourierNeg ell`.

Honest scope: this is the cross-fibre carrier bridge only.  It does not claim
that the signed centered-alias dictionaries intertwine with residue
reflection.  Euclidean division produces a coarse-residue-dependent unit
borrow/carry in the quotient coordinate whenever the corresponding coarse
residue is nonzero.  That affine carry, endpoint phase, finite-to-continuous
periodization, regional `B0` and window 15 remain open.
-/

namespace YangMills.RG

noncomputable section

/-- Periodic Fourier negation is an involution on the literal `FinBox`
carrier. -/
theorem cmp99FinBoxFourierNeg_fourierNeg
    {d N : ℕ} [NeZero N] (k : FinBox d N) :
    cmp99FinBoxFourierNeg (cmp99FinBoxFourierNeg k) = k := by
  apply (cmp99FinBoxZModEquiv d N).injective
  simp only [cmp99FinBoxZModEquiv_fourierNeg, neg_neg]

/-- Coarse reciprocal projection commutes with transported periodic Fourier
negation.  In particular, negation moves rather than fixes the physical
coarse fibre. -/
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
  have hdiv : N' ∣ M * N' := dvd_mul_left N' M
  have hcast := congrArg (ZMod.castHom hdiv (ZMod N')) h
  simpa only [cmp99FinBoxZModEquiv_apply, map_neg, map_natCast] using hcast

/-- Physical periodic momentum negation is an equivalence from the fine fibre
over `ell` to the generally distinct fibre over its periodic negative. -/
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

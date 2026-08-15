/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCoarseFibreFourierNegQuotientCarry
import YangMills.RG.BalabanCMP99SourceCenteredAliasReflection

/-!
# Signed-alias affine carry under cross-fibre Fourier negation

The cold-sealed Euclidean quotient law is conjugated through the cold-sealed
signed fibre dictionaries.  The output signed alias is the actual centered
residue reflection of the input plus the unit carry selected by the coarse
residue.  This module stops at the exact `ZMod M` carrier law.  It does not
identify an endpoint phase, a finite synthesis with a Brillouin integral, a
regional `B0`, window-15 attainment, a terminal field or a `TermSource`
inhabitant.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- Cross-fibre Fourier negation transported to the literal signed depth-one
CMP89 alias carrier.  The two signed dictionaries are evaluated at their
respective coarse residues; no fixed-fibre reflection is assumed. -/
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

/-- The depth-one alias-index reflection represents coordinatewise residue
negation.  This is a thin consequence of the already sealed centered-vector
reflection and the explicit depth-one carrier bridge. -/
theorem cmp99SourceAliasIndexOneReflection_coordinate_cast_eq_neg
    (d M : ℕ) [NeZero M]
    (m : CMP89Eq246AliasIndex d M 1) (mu : Fin d) :
    (((cmp99SourceAliasIndexOneReflection d M m).1 mu : ℤ) : ZMod M) =
      -((m.1 mu : ℤ) : ZMod M) := by
  calc
    (((cmp99SourceAliasIndexOneReflection d M m).1 mu : ℤ) : ZMod M) =
        (((cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M
          (cmp99SourceAliasIndexOneReflection d M m)).1 mu : ℤ) : ZMod M) :=
      rfl
    _ = (((cmp99SourceCenteredAliasVectorReflection d M
          (cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M m)).1 mu : ℤ) :
          ZMod M) := by
      rw [cmp99SourceFlatQprimeAliasIndexOneVectorEquiv_reflection]
    _ = -((((cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M m).1 mu : ℤ) :
          ZMod M)) :=
      cmp99SourceCenteredAliasVectorReflection_coordinate_cast_eq_neg
        d M (cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M m) mu
    _ = -((m.1 mu : ℤ) : ZMod M) := rfl

/-- Exact affine residue law after cross-fibre Fourier negation.  The unit
carry is zero precisely at coarse residue zero and one otherwise. -/
theorem cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv_coordinate_cast
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N') (m : CMP89Eq246AliasIndex d M 1) (mu : Fin d) :
    ((((cmp99SourceFlatQprimeSignedAliasFourierNegCarryEquiv
        d M N' ell) m).1 mu : ℤ) : ZMod M) =
      (((cmp99SourceAliasIndexOneReflection d M m).1 mu : ℤ) : ZMod M) +
        (if (ell mu).val = 0 then 0 else 1 : ZMod M) := by
  let eIn :=
    cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell
  let k := eIn.symm m
  let k' :=
    cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv d M N' ell k
  let eOut :=
    cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N'
      (cmp99FinBoxFourierNeg ell)
  let q := cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N' ell k
  let q' := cmp99SourceFlatQprimeFixedCoarseFibreEquiv d M N'
    (cmp99FinBoxFourierNeg ell) k'
  have hout : (((eOut k').1 mu : ℤ) : ZMod M) =
      -((q' mu).val : ZMod M) := by
    rw [cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv_apply]
    exact cmp99SourceFlatQprimeSignedCenteredAliasEquiv_cast_eq_neg M (q' mu)
  have hcarry : ((q' mu).val : ZMod M) =
      -((q mu).val : ZMod M) -
        (if (ell mu).val = 0 then 0 else 1 : ZMod M) := by
    simpa only [q, q', k, k'] using
      (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv_quotient_cast
        ell k mu)
  have hin : ((m.1 mu : ℤ) : ZMod M) = -((q mu).val : ZMod M) := by
    have hk : eIn k = m := eIn.apply_symm_apply m
    rw [← hk, cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv_apply]
    exact cmp99SourceFlatQprimeSignedCenteredAliasEquiv_cast_eq_neg M (q mu)
  change (((eOut k').1 mu : ℤ) : ZMod M) =
    (((cmp99SourceAliasIndexOneReflection d M m).1 mu : ℤ) : ZMod M) +
      (if (ell mu).val = 0 then 0 else 1 : ZMod M)
  rw [hout, hcarry,
    cmp99SourceAliasIndexOneReflection_coordinate_cast_eq_neg, hin]
  ring

end

end YangMills.RG

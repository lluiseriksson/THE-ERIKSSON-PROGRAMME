/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCenteredAliasReflection

/-!
# Involutivity of the printed half-open alias reflection

The printed centered alias interval is not closed under literal integer
negation.  Its already sealed reflection is residue negation conjugated by
explicit equivalences.  This module records that applying that actual
reflection twice is the identity, first on one coordinate, then on centered
vectors, and finally on the depth-one Eq. (2.46) alias carrier.

No pointwise integer-negation closure, physical-momentum identification,
finite-grid aliasing, regional estimate, terminal field, or `TermSource`
inhabitant is assumed or asserted.
-/

namespace YangMills.RG

noncomputable section

/-- Residue reflection on the printed one-dimensional half-open carrier is
an involution. -/
@[simp]
theorem cmp99SourceCenteredAliasReflection_apply_apply
    (M : ℕ) [NeZero M]
    (m : {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers M}) :
    cmp99SourceCenteredAliasReflection M
        (cmp99SourceCenteredAliasReflection M m) = m := by
  apply (cmp99SourceCenteredAliasResidueEquiv M).injective
  simp [cmp99SourceCenteredAliasReflection, cmp99SourceZModNegEquiv]

/-- Coordinatewise residue reflection on the printed centered vector carrier
is an involution. -/
@[simp]
theorem cmp99SourceCenteredAliasVectorReflection_apply_apply
    (d M : ℕ) [NeZero M]
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d M}) :
    cmp99SourceCenteredAliasVectorReflection d M
        (cmp99SourceCenteredAliasVectorReflection d M m) = m := by
  apply (cmp89Eq245CenteredAliasVectorPiEquiv d M).injective
  funext mu
  change cmp99SourceCenteredAliasReflection M
      (cmp99SourceCenteredAliasReflection M
        ((cmp89Eq245CenteredAliasVectorPiEquiv d M m) mu)) =
    (cmp89Eq245CenteredAliasVectorPiEquiv d M m) mu
  exact cmp99SourceCenteredAliasReflection_apply_apply M _

/-- The transported reflection on the literal depth-one Eq. (2.46) alias
carrier is an involution. -/
@[simp]
theorem cmp99SourceAliasIndexOneReflection_apply_apply
    (d M : ℕ) [NeZero M] (m : CMP89Eq246AliasIndex d M 1) :
    cmp99SourceAliasIndexOneReflection d M
        (cmp99SourceAliasIndexOneReflection d M m) = m := by
  apply (cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M).injective
  change cmp99SourceCenteredAliasVectorReflection d M
      (cmp99SourceCenteredAliasVectorReflection d M
        (cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M m)) =
    cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M m
  exact cmp99SourceCenteredAliasVectorReflection_apply_apply d M _

end

end YangMills.RG

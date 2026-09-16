/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimeSignedAliasMomentumDictionary
import YangMills.RG.BalabanCMP89Eq245CenteredAliasVectorCycle

/-!
# Residue reflection on the printed centered alias carrier

Compiler-verified at exact source checkpoint
`3bf925319be2b09c6d77706be64913e9817eb3b4` by cold GitHub Actions run
`31885511354`.  Restoration and saving of `.lake/build` were skipped.  The
focal completed 8,531 jobs, the audit exited zero, and all five audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The half-open centered alias interval is not closed under literal integer
negation at its even lower endpoint.  This module instead identifies every
printed centered integer with its actual `ZMod M` residue, conjugates residue
negation through that equivalence, and lifts the resulting permutation to the
printed vector and depth-one alias carriers.  Complete finite sums may then be
reindexed without assuming pointwise periodicity.

Honest scope: this is alias-carrier algebra only.  It does not claim that
reflection stays inside a fixed physical coarse fibre.  Physical momentum
negation transports the fibre over `ell` to the fibre over
`cmp99FinBoxFourierNeg ell`; that cross-fibre dictionary, endpoint phase,
finite-to-continuous periodization, regional `B0` and window 15 remain open.
-/

namespace YangMills.RG

noncomputable section

/-- Negation as an explicit permutation of the quotient residue. -/
def cmp99SourceZModNegEquiv (M : ℕ) : Equiv.Perm (ZMod M) where
  toFun q := -q
  invFun q := -q
  left_inv q := by simp
  right_inv q := by simp

/-- The printed centered alias subtype, viewed by the residue represented by
its integer.  The final negation compensates for the sealed signed dictionary,
whose output represents the negative of its `Fin M` input. -/
def cmp99SourceCenteredAliasResidueEquiv (M : ℕ) [NeZero M] :
    {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers M} ≃ ZMod M :=
  (cmp99SourceFlatQprimeSignedCenteredAliasEquiv M).symm.trans
    ((ZMod.finEquiv M).toEquiv.trans (cmp99SourceZModNegEquiv M))

/-- The residue equivalence returns the literal cast of the centered integer;
it is not merely an enumeration of the carrier. -/
theorem cmp99SourceCenteredAliasResidueEquiv_apply
    (M : ℕ) [NeZero M]
    (m : {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers M}) :
    cmp99SourceCenteredAliasResidueEquiv M m = (m.1 : ZMod M) := by
  let q : Fin M :=
    (cmp99SourceFlatQprimeSignedCenteredAliasEquiv M).symm m
  have hback :
      cmp99SourceFlatQprimeSignedCenteredAliasEquiv M q = m := by
    exact Equiv.apply_symm_apply
      (cmp99SourceFlatQprimeSignedCenteredAliasEquiv M) m
  have hsigned :=
    cmp99SourceFlatQprimeSignedCenteredAliasEquiv_cast_eq_neg M q
  rw [hback] at hsigned
  have hfin : ((q.1 : ℕ) : ZMod M) = ZMod.finEquiv M q := by
    cases M with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n =>
        rw [show q.1 = (ZMod.finEquiv (n + 1) q).val by rfl]
        exact ZMod.natCast_zmod_val _
  change -(ZMod.finEquiv M q) = (m.1 : ZMod M)
  rw [← hfin]
  exact hsigned.symm

/-- Reflection of the printed half-open centered alias fibre is residue
negation conjugated by the residue-preserving equivalence. -/
def cmp99SourceCenteredAliasReflection (M : ℕ) [NeZero M] :
    Equiv.Perm {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers M} :=
  (cmp99SourceCenteredAliasResidueEquiv M).trans
    ((cmp99SourceZModNegEquiv M).trans
      (cmp99SourceCenteredAliasResidueEquiv M).symm)

/-- Reflection negates the represented residue, including the exceptional
lower endpoint of an even half-open fibre. -/
theorem cmp99SourceCenteredAliasReflection_cast_eq_neg
    (M : ℕ) [NeZero M]
    (m : {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers M}) :
    (((cmp99SourceCenteredAliasReflection M m).1 : ℤ) : ZMod M) =
      -((m.1 : ℤ) : ZMod M) := by
  have hin := cmp99SourceCenteredAliasResidueEquiv_apply M m
  change
    (((cmp99SourceCenteredAliasResidueEquiv M).symm
      (-(cmp99SourceCenteredAliasResidueEquiv M m))).1 : ZMod M) =
      -((m.1 : ℤ) : ZMod M)
  calc
    (((cmp99SourceCenteredAliasResidueEquiv M).symm
        (-(cmp99SourceCenteredAliasResidueEquiv M m))).1 : ZMod M) =
        cmp99SourceCenteredAliasResidueEquiv M
          ((cmp99SourceCenteredAliasResidueEquiv M).symm
            (-(cmp99SourceCenteredAliasResidueEquiv M m))) :=
      (cmp99SourceCenteredAliasResidueEquiv_apply M _).symm
    _ = -(cmp99SourceCenteredAliasResidueEquiv M m) := by
      exact Equiv.apply_symm_apply
        (cmp99SourceCenteredAliasResidueEquiv M)
        (-(cmp99SourceCenteredAliasResidueEquiv M m))
    _ = -((m.1 : ℤ) : ZMod M) := by rw [hin]

/-- Coordinatewise residue reflection on the full printed alias vector fibre.
The sealed product equivalence carries all membership proofs; no closure under
literal integer negation is assumed. -/
def cmp99SourceCenteredAliasVectorReflection (d M : ℕ) [NeZero M] :
    Equiv.Perm
      {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d M} :=
  (cmp89Eq245CenteredAliasVectorPiEquiv d M).trans
    ((Equiv.piCongrRight fun _ : Fin d =>
      cmp99SourceCenteredAliasReflection M).trans
      (cmp89Eq245CenteredAliasVectorPiEquiv d M).symm)

/-- Every reflected coordinate represents the negative quotient residue of
the corresponding input coordinate. -/
theorem cmp99SourceCenteredAliasVectorReflection_coordinate_cast_eq_neg
    (d M : ℕ) [NeZero M]
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d M})
    (mu : Fin d) :
    (((cmp99SourceCenteredAliasVectorReflection d M m).1 mu : ℤ) : ZMod M) =
      -((m.1 mu : ℤ) : ZMod M) := by
  change
    (((cmp99SourceCenteredAliasReflection M
      ((cmp89Eq245CenteredAliasVectorPiEquiv d M m) mu)).1 : ℤ) : ZMod M) =
      -((m.1 mu : ℤ) : ZMod M)
  simpa [cmp89Eq245CenteredAliasVectorPiEquiv] using
    cmp99SourceCenteredAliasReflection_cast_eq_neg M
      ((cmp89Eq245CenteredAliasVectorPiEquiv d M m) mu)

/-- A complete finite sum may be reindexed by the actual coordinatewise
residue reflection without assuming pointwise periodicity. -/
theorem cmp99SourceCenteredAliasVectorReflection_sum
    {A : Type*} [AddCommMonoid A]
    (d M : ℕ) [NeZero M]
    (f : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d M} → A) :
    ∑ m, f (cmp99SourceCenteredAliasVectorReflection d M m) = ∑ m, f m := by
  exact Equiv.sum_comp (cmp99SourceCenteredAliasVectorReflection d M) f

/-- The coordinatewise reflection transported through the sealed explicit
depth-one bridge, rather than treating `M ^ 1` and `M` as a hidden
definitional dictionary. -/
def cmp99SourceAliasIndexOneReflection (d M : ℕ) [NeZero M] :
    Equiv.Perm (CMP89Eq246AliasIndex d M 1) :=
  (cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M).trans
    ((cmp99SourceCenteredAliasVectorReflection d M).trans
      (cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M).symm)

/-- The explicit depth-one bridge intertwines its transported reflection with
the literal centered-vector reflection. -/
theorem cmp99SourceFlatQprimeAliasIndexOneVectorEquiv_reflection
    (d M : ℕ) [NeZero M] (m : CMP89Eq246AliasIndex d M 1) :
    cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M
        (cmp99SourceAliasIndexOneReflection d M m) =
      cmp99SourceCenteredAliasVectorReflection d M
        (cmp99SourceFlatQprimeAliasIndexOneVectorEquiv d M m) := by
  simp [cmp99SourceAliasIndexOneReflection]

end

end YangMills.RG

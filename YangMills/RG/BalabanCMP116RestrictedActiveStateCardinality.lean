/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedVisitedDeterminantBound

/-!
# Exact cardinality of the restricted active determinant state

The finite-state determinant removes the ambient lattice dimension, but its
transfer component still remembers every subset of the contour carrier.
This file records that cost exactly.  The active-target predicate depends
only on the current transfer node, so the active target subtype is equivalent
to an active node paired with the complete visited-state powerset.

This is an obstruction theorem for the present determinant realization, not
a final polymer-volume estimate: its `2 ^ carrier.card` factor must be removed
by a smaller realization or bypassed by a trace/walk determinant estimate.
-/

namespace YangMills.RG

noncomputable section

universe u v w

/-- Active restricted transfer targets are exactly active nodes paired with
an arbitrary visited subset of the contour carrier. -/
def cmp116RestrictedTransferTargetActiveEquiv
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta) :
    {target : CMP116RestrictedTransferState Label Domain carrier //
      cmp116RestrictedTransferTargetActive
        carrier domainActive target} ≃
      {node : CMP116VisitedTransferNode Label Domain //
        (domainActive node.domain ∩ carrier).Nonempty} ×
        CMP116RestrictedVisitedState carrier where
  toFun target :=
    (⟨target.1.1, target.2⟩, target.1.2)
  invFun pair :=
    ⟨(pair.1.1, pair.2), pair.1.2⟩
  left_inv target := by
    cases target
    rfl
  right_inv pair := by
    cases pair with
    | mk node visited =>
      cases node
      rfl

/-- Exact powerset multiplicity in the contour-active transfer targets. -/
theorem card_cmp116RestrictedTransferTargetActive
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta) :
    Fintype.card
        {target : CMP116RestrictedTransferState Label Domain carrier //
          cmp116RestrictedTransferTargetActive
            carrier domainActive target} =
      Fintype.card
          {node : CMP116VisitedTransferNode Label Domain //
            (domainActive node.domain ∩ carrier).Nonempty} *
        2 ^ carrier.card := by
  rw [Fintype.card_congr
    (cmp116RestrictedTransferTargetActiveEquiv carrier domainActive)]
  rw [Fintype.card_prod,
    CMP116RestrictedVisitedState.card_eq_two_pow]

/-- The source determinant state contains the powerset multiplicity
literally.  The first summand is the active-head contribution; the second is
the active transfer-node contribution multiplied by `2 ^ carrier.card`.
Both are paired with one physical scalar coordinate. -/
theorem card_cmp116SourceRestrictedActiveDeterminantState
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q))) :
    Fintype.card
        (CMP116SourceRestrictedActiveDeterminantState
          (M := M) (Nc := Nc) anchor carrier) =
      (Fintype.card
          {head : ↥(cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q)) //
            cmp116RestrictedHeadActive carrier
              (cmp116SourcePi4RestrictedDomainActive anchor) head} +
        Fintype.card
          {node : CMP116VisitedTransferNode Unit
              ↥(cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q)) //
            (cmp116SourcePi4RestrictedDomainActive anchor node.domain ∩
              carrier).Nonempty} *
          2 ^ carrier.card) *
        Fintype.card
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) := by
  change Fintype.card
      (Sum
        ({head : ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)) //
          cmp116RestrictedHeadActive carrier
            (cmp116SourcePi4RestrictedDomainActive anchor) head} ×
          CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
        ({target :
            CMP116RestrictedTransferState Unit
              ↥(cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q)) carrier //
          cmp116RestrictedTransferTargetActive
            carrier
            (cmp116SourcePi4RestrictedDomainActive anchor) target} ×
          CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)) = _
  have htarget :=
    card_cmp116RestrictedTransferTargetActive
      (Label := Unit)
      (Domain := ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)))
      carrier (cmp116SourcePi4RestrictedDomainActive anchor)
  simp only [Fintype.card_sum, Fintype.card_prod]
  rw [htarget]
  rw [Nat.add_mul]

end

end YangMills.RG

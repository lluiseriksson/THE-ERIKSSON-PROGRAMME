/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116FiniteStateResolventFactorization

/-!
# Restricted visited-state transfer matrix

This module turns the exact visited-carrier update into a finite transfer
matrix.  A node with label `none` is a possible distinguished head; a node
with label `some alpha` is a continuation factor.  The transition matrix
charges only the contour coordinates newly activated by its target domain.

The key support theorem is entrywise: if a transition adds no new contour
coordinate, its value is identical at an arbitrary restricted coupling and
at full coupling.  Thus the transfer defect is supported on genuinely active
state transitions, the input needed by the finite-state resolvent
factorization.

This file does not yet identify matrix powers with the source walk layers.
-/

namespace YangMills.RG

noncomputable section

universe u v w

/-- One node of the augmented transfer graph.  Only `some` nodes may be
targets of a continuation transition. -/
structure CMP116VisitedTransferNode (Label : Type u) (Domain : Type v) where
  kind : Option Label
  domain : Domain
  deriving DecidableEq, Fintype

/-- Transfer state: current labelled domain together with the finite set of
contour coordinates visited so far. -/
abbrev CMP116RestrictedTransferState
    (Label : Type u) (Domain : Type v)
    {Delta : Type w} [DecidableEq Delta] (carrier : Finset Delta) :=
  CMP116VisitedTransferNode Label Domain ×
    CMP116RestrictedVisitedState carrier

/-- The operator factor stored at one transfer node. -/
def cmp116VisitedTransferNodeFactor
    {Label : Type u} {Domain : Type v} {Index : Type*}
    (R0 : Domain → Matrix Index Index ℂ)
    (R : Label → Domain → Matrix Index Index ℂ)
    (node : CMP116VisitedTransferNode Label Domain) :
    Matrix Index Index ℂ :=
  match node.kind with
  | none => R0 node.domain
  | some label => R label node.domain

/-- Finite augmented transfer matrix.  Its target factor is multiplied after
the factors already accumulated along the path. -/
def cmp116RestrictedVisitedTransferMatrix
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ) :
    Matrix
      (CMP116RestrictedTransferState Label Domain carrier)
      (CMP116RestrictedTransferState Label Domain carrier)
      (Matrix Index Index ℂ) :=
  fun source target =>
    match target.1.kind with
    | none => 0
    | some label =>
        if _hstep :
            (⟨label, target.1.domain⟩ : CMP99WalkStep Label Domain) ∈
              successors source.1.domain then
          if _hstate :
              target.2 =
                CMP116RestrictedVisitedState.update carrier source.2
                  (domainActive target.1.domain) then
            CMP116RestrictedVisitedState.transitionWeight
                carrier sigma source.2 (domainActive target.1.domain) •
              R label target.1.domain
          else 0
        else 0

/-- At full coupling every allowed transition has scalar weight one. -/
theorem cmp116RestrictedVisitedTransferMatrix_one
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (source target :
      CMP116RestrictedTransferState Label Domain carrier) :
    cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R (fun _ => 1) source target =
      match target.1.kind with
      | none => 0
      | some label =>
          if (⟨label, target.1.domain⟩ :
                CMP99WalkStep Label Domain) ∈
              successors source.1.domain ∧
              target.2 =
                CMP116RestrictedVisitedState.update carrier source.2
                  (domainActive target.1.domain) then
            R label target.1.domain
          else 0 := by
  classical
  unfold cmp116RestrictedVisitedTransferMatrix
  split
  · rfl
  · rename_i label
    split <;> split <;>
      simp_all [CMP116RestrictedVisitedState.transitionWeight,
        cmp116ComplexWeakeningMonomial]

/-- If the target domain adds no new contour coordinate, the corresponding
transition entry has zero contour defect. -/
theorem cmp116RestrictedVisitedTransferMatrix_sub_one_eq_zero_of_newlyActive_eq_empty
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (source target :
      CMP116RestrictedTransferState Label Domain carrier)
    (hnew :
      CMP116RestrictedVisitedState.newlyActive carrier source.2
        (domainActive target.1.domain) = ∅) :
    (cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R sigma -
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R (fun _ => 1))
        source target = 0 := by
  classical
  rw [Matrix.sub_apply]
  cases hkind : target.1.kind with
  | none =>
      simp [cmp116RestrictedVisitedTransferMatrix, hkind]
  | some label =>
      simp [cmp116RestrictedVisitedTransferMatrix, hkind,
        CMP116RestrictedVisitedState.transitionWeight,
        hnew, cmp116ComplexWeakeningMonomial]

end

end YangMills.RG

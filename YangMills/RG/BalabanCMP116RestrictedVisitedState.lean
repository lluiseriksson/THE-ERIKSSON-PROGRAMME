/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116VisitedWeakeningFactorization

/-!
# Finite visited states for a restricted CMP116 contour

After the exact visited-carrier factorization, the memory needed by the
weakening weight is a subset of the finite contour carrier.  This module
packages that memory as the subtype of the carrier powerset, defines its
deterministic update and proves the exact transition-weight identity.

The state count is `2 ^ carrier.card`; it is independent of the ambient
periodic volume.  This is the finite state space on which the subsequent
transfer-operator resummation can be built.
-/

open scoped BigOperators

namespace YangMills.RG

universe u

/-- A visited state is literally one subset of the restricted contour
carrier. -/
abbrev CMP116RestrictedVisitedState
    {Delta : Type u} [DecidableEq Delta] (carrier : Finset Delta) :=
  ↥carrier.powerset

namespace CMP116RestrictedVisitedState

variable {Delta : Type u} [DecidableEq Delta]
variable (carrier : Finset Delta)

/-- No contour coordinate has been visited initially. -/
def empty : CMP116RestrictedVisitedState carrier :=
  ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩

/-- Coordinates newly charged by one physical domain. -/
def newlyActive
    (visited : CMP116RestrictedVisitedState carrier)
    (active : Finset Delta) : Finset Delta :=
  (active ∩ carrier) \ visited.1

/-- Deterministic memory update after one physical domain. -/
def update
    (visited : CMP116RestrictedVisitedState carrier)
    (active : Finset Delta) : CMP116RestrictedVisitedState carrier :=
  ⟨visited.1 ∪ (active ∩ carrier), Finset.mem_powerset.mpr <|
    Finset.union_subset
      (Finset.mem_powerset.mp visited.2)
      Finset.inter_subset_right⟩

/-- Scalar transition weight: charge exactly the coordinates first seen at
this step. -/
def transitionWeight
    (sigma : Delta → ℂ)
    (visited : CMP116RestrictedVisitedState carrier)
    (active : Finset Delta) : ℂ :=
  cmp116ComplexWeakeningMonomial
    (newlyActive carrier visited active) sigma

@[simp]
theorem coe_empty :
    (empty carrier : CMP116RestrictedVisitedState carrier).1 = ∅ := rfl

@[simp]
theorem coe_update
    (visited : CMP116RestrictedVisitedState carrier)
    (active : Finset Delta) :
    (update carrier visited active).1 =
      visited.1 ∪ (active ∩ carrier) := rfl

/-- Newly charged coordinates always belong to the restricted carrier. -/
theorem newlyActive_subset
    (visited : CMP116RestrictedVisitedState carrier)
    (active : Finset Delta) :
    newlyActive carrier visited active ⊆ carrier :=
  Finset.sdiff_subset.trans Finset.inter_subset_right

/-- A transition never charges an already visited coordinate. -/
theorem disjoint_newlyActive
    (visited : CMP116RestrictedVisitedState carrier)
    (active : Finset Delta) :
    Disjoint visited.1 (newlyActive carrier visited active) :=
  Finset.disjoint_sdiff

/-- The old monomial times the transition weight is exactly the monomial of
the updated state. -/
theorem monomial_mul_transitionWeight
    (sigma : Delta → ℂ)
    (visited : CMP116RestrictedVisitedState carrier)
    (active : Finset Delta) :
    cmp116ComplexWeakeningMonomial visited.1 sigma *
        transitionWeight carrier sigma visited active =
      cmp116ComplexWeakeningMonomial
        (update carrier visited active).1 sigma := by
  change (∏ d ∈ visited.1, sigma d) *
      (∏ d ∈ (active ∩ carrier) \ visited.1, sigma d) =
    ∏ d ∈ visited.1 ∪ (active ∩ carrier), sigma d
  have hdisjoint :
      Disjoint visited.1 ((active ∩ carrier) \ visited.1) :=
    Finset.disjoint_sdiff
  rw [← Finset.prod_union hdisjoint]
  have hunion :
      visited.1 ∪ ((active ∩ carrier) \ visited.1) =
        visited.1 ∪ (active ∩ carrier) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [hunion]

/-- The visited-state space has exactly the cardinality of a powerset. -/
theorem card_eq_two_pow :
    Fintype.card (CMP116RestrictedVisitedState carrier) =
      2 ^ carrier.card := by
  rw [Fintype.card_coe, Finset.card_powerset]

end CMP116RestrictedVisitedState

end YangMills.RG

import Mathlib

/-!
# Abstract combinatorics of one half of the theta-prism cell

This module deliberately models the two-vertex, three-parallel-edge half-cell,
not a lattice plaquette and not a `GaugeConfig`.  Its cycle rank is computed
from cardinalities.  Deleting one branch leaves two parallel edges and lowers
the rank from two to one.
-/

namespace YangMills.SU2ThetaPrism

/-- The two vertices of either reflected half-cell. -/
inductive HalfVertex
  | source
  | target
  deriving DecidableEq, Fintype, Repr

/-- The three registered parallel branches. -/
abbrev Branch := Fin 3

/-- The branches remaining after deleting branch `2`. -/
abbrev ReducedBranch := {i : Branch // i ≠ 2}

/-- Euler cycle rank for a connected finite graph, expressed only in terms of
edge and vertex cardinalities.  Connectedness is a separate premise at uses
that interpret this number graph-theoretically. -/
def connectedCycleRank (vertexCount edgeCount : ℕ) : ℕ :=
  edgeCount + 1 - vertexCount

theorem halfVertex_card : Fintype.card HalfVertex = 2 := by
  decide

theorem branch_card : Fintype.card Branch = 3 := by
  decide

theorem reducedBranch_card : Fintype.card ReducedBranch = 2 := by
  native_decide

/-- The three-branch half-cell has cycle rank two. -/
theorem threeBranch_cycleRank :
    connectedCycleRank (Fintype.card HalfVertex) (Fintype.card Branch) = 2 := by
  norm_num [connectedCycleRank, halfVertex_card, branch_card]

/-- Deleting the third branch lowers the half-cell cycle rank to one. -/
theorem reduced_cycleRank :
    connectedCycleRank (Fintype.card HalfVertex) (Fintype.card ReducedBranch) = 1 := by
  norm_num [connectedCycleRank, halfVertex_card, reducedBranch_card]

/-- Having three pairwise distinct branch slots is the combinatorial resource
needed by a three-leg theta monomial.  This does not assert sufficiency for any
analytic positivity statement. -/
def HasThreeDistinctBranches (ι : Type*) : Prop :=
  ∃ f : Fin 3 → ι, Function.Injective f

theorem branch_hasThreeDistinct : HasThreeDistinctBranches Branch := by
  exact ⟨id, Function.injective_id⟩

theorem reducedBranch_not_hasThreeDistinct :
    ¬ HasThreeDistinctBranches ReducedBranch := by
  intro h
  rcases h with ⟨f, hf⟩
  have hcard := Fintype.card_le_of_injective f hf
  norm_num [reducedBranch_card] at hcard

/-- The local caveat required before pruning an incidence-one edge. -/
structure PruningLocalHypothesis {Edge : Type*}
    (observableUses weightUses : Edge → Prop) (e : Edge) : Prop where
  occursInWeight : weightUses e
  absentFromObservable : ¬ observableUses e

/-- Pruning exposes its local observable-independence premise at every use.
The conclusion is intentionally only that the selected edge is absent from the
observable; no factorization or OS claim is smuggled into this lemma. -/
theorem pruning_observable_independent {Edge : Type*}
    {observableUses weightUses : Edge → Prop} {e : Edge}
    (h : PruningLocalHypothesis observableUses weightUses e) :
    ¬ observableUses e :=
  h.absentFromObservable

end YangMills.SU2ThetaPrism

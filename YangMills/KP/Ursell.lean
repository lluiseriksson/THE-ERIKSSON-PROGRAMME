/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Cluster

/-!
# KP2a (cont.) — the Ursell / Mayer cluster coefficient

The combinatorial coefficient at the heart of the Mayer cluster expansion of
`log Ξ` (`docs/kp-cluster-expansion-plan.md`, KP2).

For an `n`-tuple of polymers `X : Fin n → Polymer`, the **Ursell coefficient** is
the signed count of *connected spanning subgraphs* of the incompatibility graph:

  `φ(X) = ∑_{G ⊆ incompGraph X, G connected spanning} (−1)^{#edges(G)}`.

A spanning subgraph on the vertex set `Fin n` is identified with a subset `E` of
the incompatibility graph's edge finset; the subgraph is `SimpleGraph.fromEdgeSet E`
(same `n` vertices, edges `E`), and "connected spanning" is its connectedness.

`classical` supplies the decidability needed to enumerate subgraphs (the polymer
system carries no `DecidableRel` on incompatibility), so `ursell` is `noncomputable`.

This file's goal is the **definition** (the milestone is having `φ` well-typed and
oracle-clean).  Its values on small clusters and the expansion identity are the
next sub-steps; the inductive KP convergence bound (KP2b) is the months-long crux.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

variable (P : PolymerSystem)

/-- The **Ursell / Mayer coefficient** of an `n`-tuple of polymers: the signed
count `∑ (−1)^{#edges}` over connected spanning subgraphs of the incompatibility
graph (subsets `E` of its edge finset whose `fromEdgeSet` is connected). -/
noncomputable def ursell {n : ℕ} (X : Fin n → P.Polymer) : ℤ := by
  classical
  exact ∑ E ∈ (incompGraph P X).edgeFinset.powerset.filter
      (fun E : Finset (Sym2 (Fin n)) =>
        (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Connected),
    (-1 : ℤ) ^ E.card

/-- **Base case: a single-polymer cluster has Ursell coefficient `1`.**  Its
incompatibility graph is `⊥` on one vertex (no edges possible), whose only
connected spanning subgraph is the empty one, contributing `(−1)^0 = 1`.  This
validates the definition and is the `n = 1` base of the cluster expansion. -/
theorem ursell_fin_one (X : Fin 1 → P.Polymer) : ursell P X = 1 := by
  classical
  -- The incompatibility graph has no edges (single vertex), computed directly to
  -- avoid the dependent rewrite `incompGraph P X → ⊥` (its `Fintype` instance depends
  -- on `incompGraph P X`).
  have hef : (incompGraph P X).edgeFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet, incompGraph_adj] at he
      exact he.1 (Subsingleton.elim a b)
  have hconn : (SimpleGraph.fromEdgeSet
      (↑(∅ : Finset (Sym2 (Fin 1))) : Set (Sym2 (Fin 1)))).Connected := by
    have he : SimpleGraph.fromEdgeSet
        (↑(∅ : Finset (Sym2 (Fin 1))) : Set (Sym2 (Fin 1))) = ⊥ := by simp
    rw [he]
    refine ⟨fun u v => ?_⟩
    obtain rfl := Subsingleton.elim u v
    exact SimpleGraph.Reachable.refl _
  unfold ursell
  rw [hef, Finset.powerset_empty, Finset.filter_singleton, if_pos hconn,
      Finset.sum_singleton, Finset.card_empty]
  norm_num

/-- **Only clusters contribute.**  If the incompatibility graph of the tuple is not
connected (the tuple is not a cluster), then no spanning subgraph can be connected
either, so the Ursell coefficient vanishes.  This is the structural fact that makes
*clusters* exactly the index set of the Mayer expansion of `log Ξ`. -/
theorem ursell_eq_zero_of_not_isCluster {n : ℕ} (X : Fin n → P.Polymer)
    (h : ¬ IsCluster P X) : ursell P X = 0 := by
  classical
  unfold ursell
  have hempty : (incompGraph P X).edgeFinset.powerset.filter
      (fun E : Finset (Sym2 (Fin n)) =>
        (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Connected) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro E hE hconn
    rw [Finset.mem_powerset] at hE
    apply h
    have hle : SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))) ≤ incompGraph P X := by
      rw [← SimpleGraph.fromEdgeSet_edgeSet (incompGraph P X)]
      apply SimpleGraph.fromEdgeSet_mono
      rw [← SimpleGraph.coe_edgeFinset]
      exact Finset.coe_subset.mpr hE
    exact SimpleGraph.Connected.mono hle hconn
  rw [hempty, Finset.sum_empty]

end YangMills.KP

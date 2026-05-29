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

end YangMills.KP

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Basic

/-!
# KP2a — incompatibility graph and the cluster index

Start of milestone KP2 (`docs/kp-cluster-expansion-plan.md`), the combinatorial
heart of the Kotecký–Preiss cluster expansion.  This file fixes the **index set**
of the expansion: *clusters*.

Given an `n`-tuple of polymers `X : Fin n → Polymer`, its **incompatibility graph**
has vertices `Fin n` and an edge between distinct `i, j` exactly when the polymers
`X i` and `X j` are incompatible.  A tuple is a **cluster** when this graph is
*connected* — i.e. every pair of polymers in the tuple is linked by a chain of
pairwise incompatibilities.  Clusters are precisely the terms that survive in the
Mayer/Ursell expansion of `log Ξ`.

This file provides the definitions and the basic adjacency rewrite.  The Ursell /
Mayer coefficient (a signed sum over connected spanning subgraphs) and the
expansion itself are the next sub-steps (KP2a-cont., KP2b).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

variable (P : PolymerSystem)

/-- The **incompatibility graph** of an `n`-tuple of polymers: vertices `Fin n`,
with an edge between distinct `i j` iff `X i` and `X j` are incompatible.  It is a
genuine `SimpleGraph` (symmetric and loopless) because incompatibility is symmetric
and the edge condition excludes `i = j`. -/
def incompGraph {n : ℕ} (X : Fin n → P.Polymer) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => P.incomp (X i) (X j))

@[simp]
theorem incompGraph_adj {n : ℕ} (X : Fin n → P.Polymer) (i j : Fin n) :
    (incompGraph P X).Adj i j ↔ i ≠ j ∧ P.incomp (X i) (X j) := by
  rw [incompGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, P.incomp_symm _ _ h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

/-- A tuple of polymers forms a **cluster** if its incompatibility graph is
connected: every pair is linked by a chain of pairwise incompatibilities.  This is
the index set of the Mayer/Ursell cluster expansion of `log Ξ` (KP2). -/
def IsCluster {n : ℕ} (X : Fin n → P.Polymer) : Prop :=
  (incompGraph P X).Connected

end YangMills.KP

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.SharpMajorant

/-!
# Sharp KP, step 5 — the shell decomposition (combinatorial half)

`docs/SHARP-KP-PLAN.md`, remaining brick, steps C1–C4.  This file hosts the
combinatorial half of the sharp Kotecký–Preiss bound: pinned cluster sums
are dominated by the depth-recursion majorant `kpMajorant`.

Landed so far:

* **C1** (`exists_adj_reachable_in_deleted`): in a connected graph, every
  vertex other than `v₀` reaches a neighbor of `v₀` inside the
  vertex-deleted subgraph — i.e., every component of `G − v₀` is attached
  to `v₀`.  This is what makes each first-shell subtree's root polymer
  incompatible with the pinned polymer in the shell recursion (C3).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

/-- **C1 — root deletion keeps components attached:** in a connected graph,
any vertex `u ≠ v₀` can reach, *within the subgraph induced on the
complement of `v₀`*, some neighbor `w` of `v₀`.  (Equivalently: every
connected component of `G − v₀` contains a neighbor of `v₀`.) -/
theorem exists_adj_reachable_in_deleted {α : Type*} {G : SimpleGraph α}
    {v₀ : α} :
    ∀ {u b : α} (_ : G.Walk u b) (_ : b = v₀) (hu : u ≠ v₀),
      ∃ (w : α) (hw : w ≠ v₀), G.Adj v₀ w ∧
        (G.induce {x | x ≠ v₀}).Reachable ⟨u, hu⟩ ⟨w, hw⟩ := by
  intro u b p
  induction p with
  | nil => intro hb hu; exact absurd hb hu
  | @cons a c _ h q ih =>
      intro hb hu
      by_cases hc : c = v₀
      · -- `a` is itself a neighbor of `v₀`
        subst hc
        exact ⟨a, hu, h.symm, SimpleGraph.Reachable.refl _⟩
      · -- recurse along the walk, prepending the edge `a–c`
        obtain ⟨w, hw, hadj, hreach⟩ := ih hb hc
        refine ⟨w, hw, hadj, SimpleGraph.Reachable.trans ?_ hreach⟩
        refine SimpleGraph.Adj.reachable ?_
        exact (SimpleGraph.induce_adj).mpr h

/-- C1, packaged from connectivity: any non-root vertex reaches a root
neighbor in the deleted graph. -/
theorem exists_adj_reachable_in_deleted_of_connected {α : Type*}
    {G : SimpleGraph α} (hc : G.Connected) (v₀ : α) {u : α} (hu : u ≠ v₀) :
    ∃ (w : α) (hw : w ≠ v₀), G.Adj v₀ w ∧
      (G.induce {x | x ≠ v₀}).Reachable ⟨u, hu⟩ ⟨w, hw⟩ := by
  obtain ⟨p⟩ := hc.preconnected u v₀
  exact exists_adj_reachable_in_deleted p rfl hu

/-- Graph distances on a finite connected graph are bounded by the vertex
count: geodesics are realized by paths, and paths have fewer edges than
vertices.  (Bounds BFS levels into `Fin (n+1)` for the `treeSumRaw`
indexing.) -/
theorem connected_dist_lt_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (u v : V) :
    G.dist u v < Fintype.card V := by
  classical
  obtain ⟨w, hw⟩ := (hc.preconnected u v).exists_walk_length_eq_dist
  have h1 : G.dist u v ≤ w.bypass.length :=
    SimpleGraph.dist_le _
  have h2 : w.bypass.length < Fintype.card V :=
    (SimpleGraph.Walk.bypass_isPath w).length_lt
  omega

section TreeSum

/-- **Admissibility** of a rooted parent/level structure on `Fin (n+1)`:
the root `0` sits at level `0`, and every non-root vertex's parent lies
strictly below it.  Each admissible pair encodes (at most one) rooted
forest reaching down toward the root; spanning trees of incompatibility
graphs land here via their BFS parent/level data. -/
def IsAdmissible {n D : ℕ} (p : Fin (n + 1) → Fin (n + 1))
    (lev : Fin (n + 1) → Fin (D + 1)) : Prop :=
  lev 0 = 0 ∧ ∀ v, v ≠ 0 → ((lev (p v) : ℕ) < (lev v : ℕ))

instance {n D : ℕ} (p : Fin (n + 1) → Fin (n + 1))
    (lev : Fin (n + 1) → Fin (D + 1)) : Decidable (IsAdmissible p lev) := by
  unfold IsAdmissible
  infer_instance

open Classical in
/-- **The raw depth-`D` rooted tree-sum** pinned at `c` (no factorial
normalization — fixed at assembly): the sum over admissible parent/level
structures and pinned polymer assignments of the tree-compatibility
indicator times the non-root activities.  C2 dominates pinned cluster
weights by `treeSumRaw`; C3 runs the shell recursion on it. -/
noncomputable def treeSumRaw (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (D n : ℕ) : ℝ :=
  ∑ pl ∈ (Finset.univ : Finset ((Fin (n + 1) → Fin (n + 1))
      × (Fin (n + 1) → Fin (D + 1)))).filter
      (fun pl => IsAdmissible pl.1 pl.2),
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X => X 0 = c),
      ∏ v ∈ Finset.univ.filter (fun v : Fin (n + 1) => v ≠ 0),
        (if P.incomp (X (pl.1 v)) (X v) then (1 : ℝ) else 0)
          * ‖P.activity (X v)‖

open Classical in
lemma treeSumRaw_nonneg (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) (D n : ℕ) : 0 ≤ treeSumRaw P c D n := by
  unfold treeSumRaw
  refine Finset.sum_nonneg fun pl _ => Finset.sum_nonneg fun X _ =>
    Finset.prod_nonneg fun v _ => mul_nonneg ?_ (norm_nonneg _)
  split_ifs <;> norm_num

end TreeSum

end YangMills.KP

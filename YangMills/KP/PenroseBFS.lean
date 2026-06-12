/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.PenroseScheme

/-!
# T2 (Penrose scheme, concrete) — the greedy BFS scheme: definitions + foundations

`PenroseScheme.lean` proved: any partition scheme `(π, R)` with interval fibers
gives `|ursell| ≤ #spanningTrees`.  This file begins the **construction of the
concrete scheme** — the classical greedy/BFS Penrose map:

* `bfsLevel E v` — distance from the root `0` in `fromEdgeSet E`;
* `bfsParentSet E v` — the neighbours of `v` one level closer to the root;
* `bfsParent E v` — the **least** such neighbour (greedy choice);
* `penroseTree E` — the edge set `{ s(bfsParent E v, v) : v ≠ 0 }`, the
  candidate `π`;
* `penroseRel`/`penroseEnvelope H T` — the admissible edges, the candidate
  `R`: an edge `{u,v}` of `H` is admissible for `T` iff its endpoints are on
  the same `T`-level, or on adjacent levels with the lower endpoint not
  smaller than the greedy parent.

Proved here (the foundations the fiber verification will consume):

* `exists_bfs_parent` — in a connected graph every nonroot vertex has a
  neighbour one level closer to the root (via a geodesic walk);
* `dist_le_succ_of_adj` — adjacent vertices lie on adjacent-or-equal levels;
* `bfsParent_spec` — the greedy parent is adjacent and one level down;
* `bfsParent_min` — it is minimal among candidate parents;
* `penroseTree_subset` — `π(E) ⊆ E` for connected `E`;
* `bfsLevel_zero_eq` — the root is at level `0`.

Still open (the fiber verification, next campaign): `π(E)` is a spanning tree
(`hmaps`), and the fiber of `π` over each tree `T` is exactly the interval
`[T, penroseEnvelope H T]` (`hfiber`) — the two hypotheses of
`abs_ursell_le_card_spanningTrees_of_scheme`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open SimpleGraph

/-! ### Generic BFS facts -/

/-- **Adjacent vertices lie within one level of each other:** in a connected
graph, `dist w₀ v ≤ dist w₀ u + 1` whenever `u ~ v`. -/
lemma dist_le_succ_of_adj {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    (w₀ : V) {u v : V} (h : G.Adj u v) :
    G.dist w₀ v ≤ G.dist w₀ u + 1 := by
  have htri := hconn.dist_triangle (u := w₀) (v := u) (w := v)
  rwa [SimpleGraph.dist_eq_one_iff_adj.mpr h] at htri

/-- **Parent existence:** in a connected graph, every vertex `v ≠ w₀` has a
neighbour one level closer to the root `w₀` (the penultimate vertex of a
geodesic walk). -/
lemma exists_bfs_parent {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    (w₀ : V) {v : V} (hv : v ≠ w₀) :
    ∃ u : V, G.Adj u v ∧ G.dist w₀ u + 1 = G.dist w₀ v := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist w₀ v
  obtain ⟨q, hq⟩ : ∃ q : G.Walk v w₀, q.length = G.dist w₀ v :=
    ⟨p.reverse, by rw [SimpleGraph.Walk.length_reverse, hp]⟩
  cases q with
  | nil => exact absurd rfl hv
  | @cons _ b _ hadj q' =>
    refine ⟨b, hadj.symm, ?_⟩
    have h1 : G.dist w₀ b ≤ q'.length := by
      have hle := SimpleGraph.dist_le q'.reverse
      rwa [SimpleGraph.Walk.length_reverse] at hle
    have h2 : G.dist w₀ v ≤ G.dist w₀ b + 1 :=
      dist_le_succ_of_adj hconn w₀ hadj.symm
    have h3 : q'.length + 1 = G.dist w₀ v := by
      simpa [SimpleGraph.Walk.length_cons] using hq
    omega

/-! ### The greedy BFS scheme on `Fin (m+1)` -/

variable {m : ℕ}

/-- **BFS level:** distance from the root `0` in the spanning subgraph
`fromEdgeSet E`. -/
noncomputable def bfsLevel (E : Finset (Sym2 (Fin (m + 1)))) (v : Fin (m + 1)) : ℕ :=
  (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).dist 0 v

@[simp] lemma bfsLevel_zero_eq (E : Finset (Sym2 (Fin (m + 1)))) :
    bfsLevel E 0 = 0 :=
  SimpleGraph.dist_self

/-- The **candidate parents** of `v`: neighbours one level closer to the root. -/
noncomputable def bfsParentSet (E : Finset (Sym2 (Fin (m + 1))))
    (v : Fin (m + 1)) : Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter (fun u =>
    (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Adj u v ∧
      bfsLevel E u + 1 = bfsLevel E v)

lemma mem_bfsParentSet {E : Finset (Sym2 (Fin (m + 1)))} {v u : Fin (m + 1)} :
    u ∈ bfsParentSet E v ↔
      (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Adj u v ∧
        bfsLevel E u + 1 = bfsLevel E v := by
  unfold bfsParentSet
  simp

/-- The **greedy (Penrose) parent**: the least candidate parent of `v`
(junk value `v` itself when no candidate exists, e.g. at the root or in a
disconnected subgraph). -/
noncomputable def bfsParent (E : Finset (Sym2 (Fin (m + 1))))
    (v : Fin (m + 1)) : Fin (m + 1) :=
  if h : (bfsParentSet E v).Nonempty then (bfsParentSet E v).min' h else v

/-- For connected `E` and `v ≠ 0`, the greedy parent is a genuine parent:
adjacent to `v` and one level closer to the root. -/
lemma bfsParent_spec {E : Finset (Sym2 (Fin (m + 1)))}
    (hconn : (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected)
    {v : Fin (m + 1)} (hv : v ≠ 0) :
    (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Adj (bfsParent E v) v ∧
      bfsLevel E (bfsParent E v) + 1 = bfsLevel E v := by
  have hne : (bfsParentSet E v).Nonempty := by
    obtain ⟨u, hu1, hu2⟩ := exists_bfs_parent hconn 0 hv
    exact ⟨u, mem_bfsParentSet.mpr ⟨hu1, hu2⟩⟩
  have hmem := Finset.min'_mem _ hne
  rw [mem_bfsParentSet] at hmem
  unfold bfsParent
  rw [dif_pos hne]
  exact hmem

/-- The greedy parent is **minimal** among candidate parents. -/
lemma bfsParent_min {E : Finset (Sym2 (Fin (m + 1)))} {v u : Fin (m + 1)}
    (hu : u ∈ bfsParentSet E v) : bfsParent E v ≤ u := by
  have hne : (bfsParentSet E v).Nonempty := ⟨u, hu⟩
  unfold bfsParent
  rw [dif_pos hne]
  exact Finset.min'_le _ u hu

/-- The **Penrose tree** of a subgraph: every nonroot vertex wires to its
greedy parent.  This is the candidate `π` of the partition scheme. -/
noncomputable def penroseTree (E : Finset (Sym2 (Fin (m + 1)))) :
    Finset (Sym2 (Fin (m + 1))) := by
  classical
  exact (Finset.univ.filter (fun v : Fin (m + 1) => v ≠ 0)).image
    (fun v => s(bfsParent E v, v))

/-- **`π(E) ⊆ E`:** for connected `E`, every Penrose-tree edge is an edge
of `E` (the greedy parent is an `E`-neighbour). -/
lemma penroseTree_subset {E : Finset (Sym2 (Fin (m + 1)))}
    (hconn : (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected) :
    penroseTree E ⊆ E := by
  classical
  intro e he
  unfold penroseTree at he
  rw [Finset.mem_image] at he
  obtain ⟨v, hv, rfl⟩ := he
  rw [Finset.mem_filter] at hv
  have hadj := (bfsParent_spec hconn hv.2).1
  rw [SimpleGraph.fromEdgeSet_adj] at hadj
  exact Finset.mem_coe.mp hadj.1

/-- Every nonroot vertex's parent edge lies in the Penrose tree. -/
lemma parent_edge_mem_penroseTree (E : Finset (Sym2 (Fin (m + 1))))
    {v : Fin (m + 1)} (hv : v ≠ 0) :
    s(bfsParent E v, v) ∈ penroseTree E := by
  classical
  unfold penroseTree
  rw [Finset.mem_image]
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩, rfl⟩

/-- **`π(E)` is connected** (for connected `E`): every vertex reaches the
root by following greedy parents, by induction on the BFS level. -/
lemma penroseTree_connected {E : Finset (Sym2 (Fin (m + 1)))}
    (hconn : (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected) :
    (fromEdgeSet (↑(penroseTree E) : Set (Sym2 (Fin (m + 1))))).Connected := by
  have key : ∀ k (v : Fin (m + 1)), bfsLevel E v = k →
      (fromEdgeSet (↑(penroseTree E) : Set (Sym2 (Fin (m + 1))))).Reachable v 0 := by
    intro k
    induction k with
    | zero =>
      intro v hv
      have h0 : (0 : Fin (m + 1)) = v :=
        (SimpleGraph.Reachable.dist_eq_zero_iff (hconn.preconnected 0 v)).mp hv
      rw [← h0]
    | succ k ih =>
      intro v hv
      have hv0 : v ≠ 0 := by
        intro h
        rw [h, bfsLevel_zero_eq] at hv
        omega
      obtain ⟨hadj, hlev⟩ := bfsParent_spec hconn hv0
      have hadj' : (fromEdgeSet (↑(penroseTree E) :
          Set (Sym2 (Fin (m + 1))))).Adj (bfsParent E v) v := by
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨Finset.mem_coe.mpr (parent_edge_mem_penroseTree E hv0), ?_⟩
        intro heq
        rw [heq] at hlev
        omega
      have hplevel : bfsLevel E (bfsParent E v) = k := by omega
      exact (hadj'.symm.reachable).trans (ih _ hplevel)
  rw [SimpleGraph.connected_iff]
  exact ⟨fun a b => (key _ a rfl).trans (key _ b rfl).symm, ⟨0⟩⟩

/-- **`π(E)` has exactly `m` edges** (one parent edge per nonroot vertex):
the map `v ↦ s(parent v, v)` is injective because the child is the
higher-level endpoint. -/
lemma penroseTree_card {E : Finset (Sym2 (Fin (m + 1)))}
    (hconn : (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected) :
    (penroseTree E).card = m := by
  classical
  have hinj : Set.InjOn (fun v => s(bfsParent E v, v))
      ↑(Finset.univ.filter (fun v : Fin (m + 1) => v ≠ 0)) := by
    intro u hu v hv heq
    rw [Finset.mem_coe, Finset.mem_filter] at hu hv
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · have hu' := (bfsParent_spec hconn hu.2).2
      have hv' := (bfsParent_spec hconn hv.2).2
      rw [h1] at hu'
      rw [← h2] at hv'
      omega
  unfold penroseTree
  rw [Finset.card_image_of_injOn hinj, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- **`π(E)` is a spanning tree** of the vertex set (for connected `E`):
connected with `m` edges on `m + 1` vertices. -/
lemma penroseTree_isTree {E : Finset (Sym2 (Fin (m + 1)))}
    (hconn : (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected) :
    (fromEdgeSet (↑(penroseTree E) : Set (Sym2 (Fin (m + 1))))).IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨penroseTree_connected hconn, ?_⟩
  -- the edge set is the (diagonal-free) coercion of the tree finset
  have hnodiag : ∀ e ∈ penroseTree E, ¬ e.IsDiag := by
    intro e he
    unfold penroseTree at he
    rw [Finset.mem_image] at he
    obtain ⟨v, hv, rfl⟩ := he
    rw [Finset.mem_filter] at hv
    rw [Sym2.mk_isDiag_iff]
    intro heq
    have hlev := (bfsParent_spec hconn hv.2).2
    rw [heq] at hlev
    omega
  have hset : (fromEdgeSet (↑(penroseTree E) :
      Set (Sym2 (Fin (m + 1))))).edgeSet
      = (↑(penroseTree E) : Set (Sym2 (Fin (m + 1)))) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff, Sym2.mem_diagSet]
    exact ⟨fun h => h.1, fun h => ⟨h, hnodiag e (Finset.mem_coe.mp h)⟩⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    penroseTree_card hconn, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Instance-agnostic form of `SimpleGraph.mem_edgeFinset` (cf.
`PenroseScheme.lean`): rewriting unifies the `Fintype` instance with the one
in the goal. -/
private lemma mem_edgeFinset_iff'' {V : Type*} {G : SimpleGraph V}
    {inst : Fintype G.edgeSet} {e : Sym2 V} :
    e ∈ @SimpleGraph.edgeFinset V G inst ↔ e ∈ G.edgeSet :=
  SimpleGraph.mem_edgeFinset

/-- **`hmaps` of the partition scheme, discharged:** for a connected subgraph
`E` supported on the edges of the ambient graph `H`, the Penrose tree
`π(E) = penroseTree E` is a spanning tree of `H`.  This is the first of the
two hypotheses of `abs_ursell_le_card_spanningTrees_of_scheme`; only the
fiber characterization (`hfiber`) remains open. -/
lemma penroseTree_mem_spanningTrees {H : SimpleGraph (Fin (m + 1))}
    [Fintype H.edgeSet] {E : Finset (Sym2 (Fin (m + 1)))}
    (hE : ∀ e ∈ E, e ∈ H.edgeSet)
    (hconn : (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected) :
    penroseTree E ∈ spanningTrees H := by
  classical
  unfold spanningTrees
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun e he => ?_, penroseTree_isTree hconn⟩
  rw [mem_edgeFinset_iff'']
  exact hE e (penroseTree_subset hconn he)

/-- The **Penrose admissibility relation** for a tree `T`: endpoints on the
same `T`-level, or on adjacent levels with the lower endpoint not below the
greedy parent of the upper one.  (Symmetric by construction.) -/
def penroseRel (T : Finset (Sym2 (Fin (m + 1)))) (u v : Fin (m + 1)) : Prop :=
  bfsLevel T u = bfsLevel T v ∨
  (bfsLevel T u + 1 = bfsLevel T v ∧ bfsParent T v ≤ u) ∨
  (bfsLevel T v + 1 = bfsLevel T u ∧ bfsParent T u ≤ v)

lemma penroseRel_symm (T : Finset (Sym2 (Fin (m + 1)))) :
    Symmetric (penroseRel T) := by
  intro u v h
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- The **Penrose envelope** `R(T)`: the admissible edges of the ambient
graph `H`.  The open fiber verification asserts that the `π`-fiber over a
spanning tree `T` is exactly the interval `[T, penroseEnvelope H T]`. -/
noncomputable def penroseEnvelope (H : SimpleGraph (Fin (m + 1)))
    [Fintype H.edgeSet] (T : Finset (Sym2 (Fin (m + 1)))) :
    Finset (Sym2 (Fin (m + 1))) := by
  classical
  exact H.edgeFinset.filter (fun e => e ∈ Sym2.fromRel (penroseRel_symm T))

lemma mem_penroseEnvelope_iff {H : SimpleGraph (Fin (m + 1))}
    [Fintype H.edgeSet] (T : Finset (Sym2 (Fin (m + 1))))
    (u v : Fin (m + 1)) :
    s(u, v) ∈ penroseEnvelope H T ↔
      s(u, v) ∈ H.edgeFinset ∧ penroseRel T u v := by
  unfold penroseEnvelope
  classical
  rw [Finset.mem_filter]
  simp [Sym2.fromRel_prop]

end YangMills.KP

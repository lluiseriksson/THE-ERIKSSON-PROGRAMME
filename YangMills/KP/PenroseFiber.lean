/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.PenroseBFS

/-!
# T2 (Penrose fiber, foundations) — tree geometry for the fiber verification

The single remaining lemma of Target B step (i) is `hfiber`: the `π`-fiber
over a spanning tree `T` is exactly the interval `[T, penroseEnvelope H T]`
(see `docs/HANDOFF-KP.md`).  Its bookkeeping rests on four facts about
distances, walks and trees, proved here:

* `dist_le_dist_of_le` — distances only shrink in a supergraph;
* `level_le_of_walk` — a function changing by ≤ 1 along edges grows at most
  by the length along any walk (the level-preservation engine);
* `isTree_path_length_eq_dist` — **in a tree, every path realizes the
  distance** (via path uniqueness + geodesic bypass);
* `isTree_adj_level` — **adjacent tree vertices lie on consecutive levels**
  (same-level adjacency would produce two distinct paths to one vertex).

With these, the remaining `hfiber` steps are: levels agree on the interval
(`bfsLevel E = bfsLevel T` for `T ⊆ E ⊆ R(T)`), the greedy parent is
preserved, `penroseTree T = T` for spanning trees, and the two directions of
the fiber characterization.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open SimpleGraph

/-- **Distances only shrink in a supergraph:** if `G ≤ G'` and `u, v` are
`G`-reachable, then `G'.dist u v ≤ G.dist u v`. -/
lemma dist_le_dist_of_le {V : Type*} {G G' : SimpleGraph V} (h : G ≤ G')
    {u v : V} (hr : G.Reachable u v) : G'.dist u v ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  calc G'.dist u v ≤ (p.mapLe h).length := SimpleGraph.dist_le _
    _ = p.length := by
        show (SimpleGraph.Walk.map (SimpleGraph.Hom.ofLE h) p).length = p.length
        rw [SimpleGraph.Walk.length_map]
    _ = G.dist u v := hp

/-- **Level growth along a walk:** if `f` increases by at most `1` across
every edge, then `f v ≤ f u + length` along any walk `u → v`. -/
lemma level_le_of_walk {V : Type*} {G : SimpleGraph V} (f : V → ℕ)
    (hedge : ∀ u w : V, G.Adj u w → f w ≤ f u + 1) {u v : V}
    (p : G.Walk u v) : f v ≤ f u + p.length := by
  induction p with
  | nil => simp
  | @cons a b c hadj q ih =>
    have hab := hedge a b hadj
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- **In a tree, every path realizes the distance.**  The geodesic walk's
bypass is a path of length `dist u v`; by uniqueness of paths it *is* the
given path. -/
lemma isTree_path_length_eq_dist {V : Type*} {G : SimpleGraph V}
    (hT : G.IsTree) {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    p.length = G.dist u v := by
  classical
  obtain ⟨q, hq⟩ := hT.isConnected.exists_walk_length_eq_dist u v
  have hqb_path := q.bypass_isPath
  have hqb_len : q.bypass.length = G.dist u v := by
    have h1 := SimpleGraph.Walk.length_bypass_le q
    have h2 := SimpleGraph.dist_le q.bypass
    omega
  obtain ⟨P, -, hPuniq⟩ :=
    (SimpleGraph.isTree_iff_existsUnique_path.mp hT).2 u v
  have h3 : p = P := hPuniq p hp
  have h4 : q.bypass = P := hPuniq q.bypass hqb_path
  rw [h3, ← h4, hqb_len]

/-- **Adjacent tree vertices lie on consecutive levels:** in a tree, an edge
never joins two vertices at the same distance from the root.  (Same-level
adjacency would yield two distinct paths to one endpoint: the root path of
the other endpoint extended across the edge, versus the endpoint's own root
path.) -/
lemma isTree_adj_level {V : Type*} {G : SimpleGraph V} (hT : G.IsTree)
    (w₀ : V) {u v : V} (h : G.Adj u v) :
    G.dist w₀ u + 1 = G.dist w₀ v ∨ G.dist w₀ v + 1 = G.dist w₀ u := by
  classical
  have hconn := hT.isConnected
  have h1 : G.dist w₀ v ≤ G.dist w₀ u + 1 := dist_le_succ_of_adj hconn w₀ h
  have h2 : G.dist w₀ u ≤ G.dist w₀ v + 1 :=
    dist_le_succ_of_adj hconn w₀ h.symm
  rcases Nat.lt_trichotomy (G.dist w₀ u) (G.dist w₀ v) with hlt | heq | hgt
  · left; omega
  · exfalso
    -- same level: build a second path to `v`
    obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist w₀ u
    have hqb_path := q.bypass_isPath
    have hqb_len : q.bypass.length = G.dist w₀ u := by
      have hb1 := SimpleGraph.Walk.length_bypass_le q
      have hb2 := SimpleGraph.dist_le q.bypass
      omega
    by_cases hv : v ∈ q.bypass.support
    · -- `v` on the root path of `u`: the prefix path forces `v = u`
      have hQpath : (q.bypass.takeUntil v hv).IsPath := hqb_path.takeUntil hv
      have hQlen : (q.bypass.takeUntil v hv).length = G.dist w₀ v :=
        isTree_path_length_eq_dist hT _ hQpath
      have hlen : (q.bypass.takeUntil v hv).length
          + (q.bypass.dropUntil v hv).length = q.bypass.length := by
        rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
      have hdrop0 : (q.bypass.dropUntil v hv).length = 0 := by omega
      exact h.ne (SimpleGraph.Walk.eq_of_length_eq_zero hdrop0).symm
    · -- `v` off the root path of `u`: extending across the edge gives a
      -- path to `v` of the wrong length
      have hWpath : (q.bypass.concat h).IsPath := by
        rw [SimpleGraph.Walk.concat_isPath_iff]
        exact ⟨hqb_path, hv⟩
      have hWlen : (q.bypass.concat h).length = G.dist w₀ v :=
        isTree_path_length_eq_dist hT _ hWpath
      rw [SimpleGraph.Walk.length_concat, hqb_len] at hWlen
      omega
  · right; omega

/-- In a tree, a vertex strictly farther from the root than `u` cannot lie
on a path from the root to `u` (prefix paths realize distances). -/
lemma not_mem_support_of_dist_lt {V : Type*} {G : SimpleGraph V}
    (hT : G.IsTree) {w₀ u v : V} (p : G.Walk w₀ u) (hp : p.IsPath)
    (hgt : G.dist w₀ u < G.dist w₀ v) : v ∉ p.support := by
  classical
  intro hv
  have hQ : (p.takeUntil v hv).IsPath := hp.takeUntil hv
  have hQlen : (p.takeUntil v hv).length = G.dist w₀ v :=
    isTree_path_length_eq_dist hT _ hQ
  have hle := SimpleGraph.Walk.length_takeUntil_le p hv
  have hplen : p.length = G.dist w₀ u := isTree_path_length_eq_dist hT p hp
  omega

/-- **Parent uniqueness in a tree:** a vertex has at most one neighbour one
level closer to the root.  (Two such neighbours would give two distinct
root-paths, comparing penultimate vertices.) -/
lemma isTree_parent_unique {V : Type*} {G : SimpleGraph V} (hT : G.IsTree)
    (w₀ : V) {v u₁ u₂ : V}
    (h₁ : G.Adj u₁ v ∧ G.dist w₀ u₁ + 1 = G.dist w₀ v)
    (h₂ : G.Adj u₂ v ∧ G.dist w₀ u₂ + 1 = G.dist w₀ v) : u₁ = u₂ := by
  classical
  obtain ⟨q₁, hq₁⟩ := hT.isConnected.exists_walk_length_eq_dist w₀ u₁
  obtain ⟨q₂, hq₂⟩ := hT.isConnected.exists_walk_length_eq_dist w₀ u₂
  have hp₁ := q₁.bypass_isPath
  have hp₂ := q₂.bypass_isPath
  have hl₁ : q₁.bypass.length = G.dist w₀ u₁ := by
    have hb1 := SimpleGraph.Walk.length_bypass_le q₁
    have hb2 := SimpleGraph.dist_le q₁.bypass
    omega
  have hl₂ : q₂.bypass.length = G.dist w₀ u₂ := by
    have hb1 := SimpleGraph.Walk.length_bypass_le q₂
    have hb2 := SimpleGraph.dist_le q₂.bypass
    omega
  have hv₁ : v ∉ q₁.bypass.support :=
    not_mem_support_of_dist_lt hT q₁.bypass hp₁ (by omega)
  have hv₂ : v ∉ q₂.bypass.support :=
    not_mem_support_of_dist_lt hT q₂.bypass hp₂ (by omega)
  have hP₁ : (q₁.bypass.concat h₁.1).IsPath := by
    rw [SimpleGraph.Walk.concat_isPath_iff]
    exact ⟨hp₁, hv₁⟩
  have hP₂ : (q₂.bypass.concat h₂.1).IsPath := by
    rw [SimpleGraph.Walk.concat_isPath_iff]
    exact ⟨hp₂, hv₂⟩
  obtain ⟨P, -, hPuniq⟩ :=
    (SimpleGraph.isTree_iff_existsUnique_path.mp hT).2 w₀ v
  have he : q₁.bypass.concat h₁.1 = q₂.bypass.concat h₂.1 := by
    rw [hPuniq _ hP₁, hPuniq _ hP₂]
  have hpen := congrArg SimpleGraph.Walk.penultimate he
  rwa [SimpleGraph.Walk.penultimate_concat, SimpleGraph.Walk.penultimate_concat]
    at hpen

/-- **`π` fixes spanning trees:** `penroseTree T = T` for every spanning
tree `T` of the ambient graph — each tree edge is the greedy parent edge of
its lower endpoint, by parent uniqueness.  (This is the diagonal of the
fiber characterization: `T` itself lies in the fiber over `T`.) -/
lemma penroseTree_of_spanningTree {m : ℕ} {H : SimpleGraph (Fin (m + 1))}
    [Fintype H.edgeSet] {T : Finset (Sym2 (Fin (m + 1)))}
    (hT : T ∈ spanningTrees H) : penroseTree T = T := by
  classical
  have htree := isTree_of_mem_spanningTrees H hT
  have hconn := htree.isConnected
  apply Finset.Subset.antisymm (penroseTree_subset hconn)
  intro e he
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro he
  -- the endpoints are distinct
  have hne : a ≠ b := by
    have hmem := spanningTrees_subset H hT he
    rw [SimpleGraph.mem_edgeFinset] at hmem
    intro hab
    exact H.not_isDiag_of_mem_edgeSet hmem (Sym2.mk_isDiag_iff.mpr hab)
  -- adjacency in the tree
  have hadj : (fromEdgeSet (↑T : Set (Sym2 (Fin (m + 1))))).Adj a b := by
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨Finset.mem_coe.mpr he, hne⟩
  rcases isTree_adj_level htree 0 hadj with hlev | hlev
  · -- `b` is the lower endpoint: the edge is `b`'s parent edge
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, SimpleGraph.dist_self] at hlev
      omega
    have hbspec := bfsParent_spec hconn hb0
    have hpar : bfsParent T b = a :=
      isTree_parent_unique htree 0 ⟨hbspec.1, hbspec.2⟩ ⟨hadj, hlev⟩
    have hmem := parent_edge_mem_penroseTree T hb0
    rwa [hpar] at hmem
  · -- `a` is the lower endpoint: the edge is `a`'s parent edge
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, SimpleGraph.dist_self] at hlev
      omega
    have haspec := bfsParent_spec hconn ha0
    have hpar : bfsParent T a = b :=
      isTree_parent_unique htree 0 ⟨haspec.1, haspec.2⟩ ⟨hadj.symm, hlev⟩
    have hmem := parent_edge_mem_penroseTree T ha0
    rw [hpar] at hmem
    rw [Sym2.eq_swap]
    exact hmem

/-- A subgraph containing a connected spanning subgraph is connected. -/
lemma connected_of_subset_connected {m : ℕ}
    {T E : Finset (Sym2 (Fin (m + 1)))} (hTE : T ⊆ E)
    (hconn : (fromEdgeSet (↑T : Set (Sym2 (Fin (m + 1))))).Connected) :
    (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun a b => ?_, ⟨0⟩⟩
  exact SimpleGraph.Reachable.mono
    (SimpleGraph.fromEdgeSet_mono (Finset.coe_subset.mpr hTE))
    (hconn.preconnected a b)

/-- **Level preservation on the interval (hfiber step 1):** for
`T ⊆ E ⊆ penroseEnvelope H T`, the BFS levels of `E` coincide with those of
the spanning tree `T`.  Downward: `T ⊆ E` only shrinks distances.  Upward:
every admissible edge moves the `T`-level by at most one, so any `E`-walk of
length `ℓ` from the root reaches level at most `ℓ`. -/
lemma bfsLevel_eq_of_interval {m : ℕ} {H : SimpleGraph (Fin (m + 1))}
    [Fintype H.edgeSet] {T E : Finset (Sym2 (Fin (m + 1)))}
    (hT : T ∈ spanningTrees H) (hTE : T ⊆ E)
    (hER : E ⊆ penroseEnvelope H T) (v : Fin (m + 1)) :
    bfsLevel E v = bfsLevel T v := by
  classical
  have htree := isTree_of_mem_spanningTrees H hT
  have hTconn := htree.isConnected
  have hEconn := connected_of_subset_connected hTE hTconn
  have hedge : ∀ u w : Fin (m + 1),
      (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Adj u w →
      bfsLevel T w ≤ bfsLevel T u + 1 := by
    intro u w hadj
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    have hmem : s(u, w) ∈ penroseEnvelope H T :=
      hER (Finset.mem_coe.mp hadj.1)
    rw [mem_penroseEnvelope_iff] at hmem
    rcases hmem.2 with h | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  refine Nat.le_antisymm ?_ ?_
  · exact dist_le_dist_of_le
      (SimpleGraph.fromEdgeSet_mono (Finset.coe_subset.mpr hTE))
      (hTconn.preconnected 0 v)
  · obtain ⟨p, hp⟩ := hEconn.exists_walk_length_eq_dist 0 v
    have hw := level_le_of_walk (bfsLevel T) hedge p
    rw [bfsLevel_zero_eq] at hw
    have hEv : bfsLevel E v = p.length := hp.symm
    omega

/-- **The Penrose tree preserves BFS levels (hfiber step 3):**
`bfsLevel (penroseTree E) = bfsLevel E` for connected `E` — parents descend
exactly one level, so the tree path to the root realizes the `E`-distance. -/
lemma bfsLevel_penroseTree_eq {m : ℕ} {E : Finset (Sym2 (Fin (m + 1)))}
    (hconn : (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected)
    (v : Fin (m + 1)) :
    bfsLevel (penroseTree E) v = bfsLevel E v := by
  have hπconn := penroseTree_connected hconn
  refine Nat.le_antisymm ?_ ?_
  · -- descent: `dist_{π E} ≤ bfsLevel E` by induction on the level
    have key : ∀ k (w : Fin (m + 1)), bfsLevel E w = k →
        bfsLevel (penroseTree E) w ≤ k := by
      intro k
      induction k with
      | zero =>
        intro w hw
        have h0 : (0 : Fin (m + 1)) = w :=
          (SimpleGraph.Reachable.dist_eq_zero_iff (hconn.preconnected 0 w)).mp hw
        rw [← h0]
        simp
      | succ k ih =>
        intro w hw
        have hw0 : w ≠ 0 := by
          intro h
          rw [h, bfsLevel_zero_eq] at hw
          omega
        obtain ⟨hadj, hlev⟩ := bfsParent_spec hconn hw0
        have hadj' : (fromEdgeSet (↑(penroseTree E) :
            Set (Sym2 (Fin (m + 1))))).Adj (bfsParent E w) w := by
          rw [SimpleGraph.fromEdgeSet_adj]
          refine ⟨Finset.mem_coe.mpr (parent_edge_mem_penroseTree E hw0), ?_⟩
          intro heq
          rw [heq] at hlev
          omega
        have hple : bfsLevel (penroseTree E) (bfsParent E w) ≤ k :=
          ih _ (by omega)
        have hstep : bfsLevel (penroseTree E) w
            ≤ bfsLevel (penroseTree E) (bfsParent E w) + 1 :=
          dist_le_succ_of_adj hπconn 0 hadj'
        omega
    exact key _ v rfl
  · exact dist_le_dist_of_le
      (SimpleGraph.fromEdgeSet_mono
        (Finset.coe_subset.mpr (penroseTree_subset hconn)))
      (hπconn.preconnected 0 v)

end YangMills.KP

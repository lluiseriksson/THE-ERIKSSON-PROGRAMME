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

/-- **Greedy-parent preservation on the interval (hfiber step 2):** for
`T ⊆ E ⊆ penroseEnvelope H T` and `v ≠ 0`, the greedy parent of `v` in `E`
is its tree parent — admissible extra edges into the lower level sit at or
above the tree parent, so the minimum is unchanged. -/
lemma bfsParent_eq_of_interval {m : ℕ} {H : SimpleGraph (Fin (m + 1))}
    [Fintype H.edgeSet] {T E : Finset (Sym2 (Fin (m + 1)))}
    (hT : T ∈ spanningTrees H) (hTE : T ⊆ E)
    (hER : E ⊆ penroseEnvelope H T) {v : Fin (m + 1)} (hv : v ≠ 0) :
    bfsParent E v = bfsParent T v := by
  classical
  have htree := isTree_of_mem_spanningTrees H hT
  have hTconn := htree.isConnected
  have hEconn := connected_of_subset_connected hTE hTconn
  obtain ⟨hTadj, hTlev⟩ := bfsParent_spec hTconn hv
  obtain ⟨hEadj, hElev⟩ := bfsParent_spec hEconn hv
  -- the tree parent is an E-candidate, so the E-parent is ≤ it
  have hmemE : bfsParent T v ∈ bfsParentSet E v := by
    rw [mem_bfsParentSet]
    constructor
    · rw [SimpleGraph.fromEdgeSet_adj] at hTadj ⊢
      exact ⟨Finset.mem_coe.mpr (hTE (Finset.mem_coe.mp hTadj.1)), hTadj.2⟩
    · rw [bfsLevel_eq_of_interval hT hTE hER,
        bfsLevel_eq_of_interval hT hTE hER]
      exact hTlev
  have hle : bfsParent E v ≤ bfsParent T v := bfsParent_min hmemE
  -- the E-parent's edge is admissible, hence at/above the tree parent
  have hrel : penroseRel T (bfsParent E v) v := by
    have hedge : s(bfsParent E v, v) ∈ E := by
      rw [SimpleGraph.fromEdgeSet_adj] at hEadj
      exact Finset.mem_coe.mp hEadj.1
    have hmem := hER hedge
    rw [mem_penroseEnvelope_iff] at hmem
    exact hmem.2
  have hlevT : bfsLevel T (bfsParent E v) + 1 = bfsLevel T v := by
    rw [← bfsLevel_eq_of_interval hT hTE hER,
      ← bfsLevel_eq_of_interval hT hTE hER]
    exact hElev
  have hge : bfsParent T v ≤ bfsParent E v := by
    rcases hrel with h | ⟨-, h2⟩ | ⟨h1, -⟩
    · omega
    · exact h2
    · omega
  exact le_antisymm hle hge

/-- **The Penrose tree preserves greedy parents:** in the tree `π E`, the
unique parent of `v` is its `E`-greedy parent. -/
lemma bfsParent_penroseTree_eq {m : ℕ} {E : Finset (Sym2 (Fin (m + 1)))}
    (hconn : (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected)
    {v : Fin (m + 1)} (hv : v ≠ 0) :
    bfsParent (penroseTree E) v = bfsParent E v := by
  have hπtree := penroseTree_isTree hconn
  have hπconn := penroseTree_connected hconn
  obtain ⟨hπadj, hπlev⟩ := bfsParent_spec hπconn hv
  obtain ⟨hEadj, hElev⟩ := bfsParent_spec hconn hv
  -- the E-parent is a level-down neighbour of `v` in the tree π E
  have hadj' : (fromEdgeSet (↑(penroseTree E) :
      Set (Sym2 (Fin (m + 1))))).Adj (bfsParent E v) v := by
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨Finset.mem_coe.mpr (parent_edge_mem_penroseTree E hv), ?_⟩
    intro heq
    rw [heq] at hElev
    omega
  have hlev' : bfsLevel (penroseTree E) (bfsParent E v) + 1
      = bfsLevel (penroseTree E) v := by
    rw [bfsLevel_penroseTree_eq hconn, bfsLevel_penroseTree_eq hconn]
    exact hElev
  -- parent uniqueness in the tree π E
  exact isTree_parent_unique hπtree 0 ⟨hπadj, hπlev⟩ ⟨hadj', hlev'⟩

/-- **The Penrose fiber characterization (`hfiber`), closed.**  For a
spanning tree `T` of `H`: a subgraph `E` is a connected `H`-subgraph with
Penrose tree `T` **iff** it lies in the Boolean interval
`[T, penroseEnvelope H T]`.  This is the last hypothesis of the partition
scheme (Penrose 1967). -/
lemma penrose_hfiber {m : ℕ} {H : SimpleGraph (Fin (m + 1))}
    [Fintype H.edgeSet] {T : Finset (Sym2 (Fin (m + 1)))}
    (hT : T ∈ spanningTrees H) (E : Finset (Sym2 (Fin (m + 1)))) :
    ((∀ e ∈ E, e ∈ H.edgeSet) ∧
      (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected ∧
      penroseTree E = T)
    ↔ (T ⊆ E ∧ E ⊆ penroseEnvelope H T) := by
  classical
  constructor
  · rintro ⟨hsub, hconn, hπ⟩
    subst hπ
    refine ⟨penroseTree_subset hconn, ?_⟩
    intro e he
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    have heSet := hsub _ he
    have hne : a ≠ b := by
      intro hab
      exact H.not_isDiag_of_mem_edgeSet heSet (Sym2.mk_isDiag_iff.mpr hab)
    have hadj : (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Adj a b := by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨Finset.mem_coe.mpr he, hne⟩
    rw [mem_penroseEnvelope_iff]
    refine ⟨by rw [SimpleGraph.mem_edgeFinset]; exact heSet, ?_⟩
    have h1 : bfsLevel E b ≤ bfsLevel E a + 1 :=
      dist_le_succ_of_adj hconn 0 hadj
    have h2 : bfsLevel E a ≤ bfsLevel E b + 1 :=
      dist_le_succ_of_adj hconn 0 hadj.symm
    unfold penroseRel
    rcases Nat.lt_trichotomy (bfsLevel E a) (bfsLevel E b) with hlt | heq | hgt
    · -- `b` one level below: later-choice condition via greedy minimality
      have hb0 : b ≠ 0 := by
        intro h
        rw [h, bfsLevel_zero_eq] at hlt
        omega
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · rw [bfsLevel_penroseTree_eq hconn, bfsLevel_penroseTree_eq hconn]
        omega
      · rw [bfsParent_penroseTree_eq hconn hb0]
        refine bfsParent_min ?_
        rw [mem_bfsParentSet]
        exact ⟨hadj, by omega⟩
    · refine Or.inl ?_
      rw [bfsLevel_penroseTree_eq hconn, bfsLevel_penroseTree_eq hconn]
      exact heq
    · have ha0 : a ≠ 0 := by
        intro h
        rw [h, bfsLevel_zero_eq] at hgt
        omega
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [bfsLevel_penroseTree_eq hconn, bfsLevel_penroseTree_eq hconn]
        omega
      · rw [bfsParent_penroseTree_eq hconn ha0]
        refine bfsParent_min ?_
        rw [mem_bfsParentSet]
        exact ⟨hadj.symm, by omega⟩
  · rintro ⟨hTE, hER⟩
    have htree := isTree_of_mem_spanningTrees H hT
    have hTconn := htree.isConnected
    have hEconn := connected_of_subset_connected hTE hTconn
    refine ⟨?_, hEconn, ?_⟩
    · intro e he
      have hmem := hER he
      revert hmem
      refine Sym2.ind (fun a b => ?_) e
      intro hmem
      rw [mem_penroseEnvelope_iff] at hmem
      have h1 := hmem.1
      rwa [SimpleGraph.mem_edgeFinset] at h1
    · have himg : penroseTree E = penroseTree T := by
        unfold penroseTree
        apply Finset.image_congr
        intro v hv
        rw [Finset.mem_coe, Finset.mem_filter] at hv
        show s(bfsParent E v, v) = s(bfsParent T v, v)
        rw [bfsParent_eq_of_interval hT hTE hER hv.2]
      rw [himg, penroseTree_of_spanningTree hT]

/-- **The Penrose tree-graph inequality — UNCONDITIONAL.**
For any polymer tuple `X`, the Ursell/Mayer coefficient is bounded by the
number of spanning trees of the incompatibility graph:
`|φ(X)| ≤ #(spanning trees of incompGraph P X)`.

This is Penrose's theorem (O. Penrose, *Convergence of fugacity expansions
for classical systems*, 1967), here obtained by instantiating the verified
partition-scheme mechanism with the greedy BFS scheme
`(penroseTree, penroseEnvelope)` whose hypotheses `hmaps`/`hfiber` are now
discharged.  Step (i) of Target B is closed; the remaining open content of
the KP convergence bound is spanning-tree *counting* (Cayley/Prüfer) and the
per-tree activity walk (`docs/HANDOFF-KP.md`). -/
theorem abs_ursell_le_card_spanningTrees (P : PolymerSystem) {n : ℕ}
    (X : Fin n → P.Polymer) [Fintype (incompGraph P X).edgeSet] :
    |ursell P X| ≤ ((spanningTrees (incompGraph P X)).card : ℤ) := by
  classical
  cases n with
  | zero =>
    have h0 : ursell P X = 0 := by
      unfold ursell
      rw [Finset.sum_filter]
      apply Finset.sum_eq_zero
      intro E _
      have hnc : ¬ (fromEdgeSet (↑E : Set (Sym2 (Fin 0)))).Connected := by
        intro hconn
        obtain ⟨v⟩ := hconn.nonempty
        exact v.elim0
      rw [if_neg hnc]
    rw [h0, abs_zero]
    positivity
  | succ m =>
    exact abs_ursell_le_card_spanningTrees_of_scheme P X penroseTree
      (penroseEnvelope (incompGraph P X))
      (fun E hsub hconn => penroseTree_mem_spanningTrees hsub hconn)
      (fun T hT E => penrose_hfiber hT E)

open Classical in
/-- The **universal labeled-tree count** on `Fin n`: all diagonal-free edge
sets whose graph is a spanning tree.  Step (iii) of Target B must bound this
at Cayley order (`docs/DEPENDENCY-GRAPH.md`); here it serves as the
system-independent majorant of the Ursell coefficient. -/
noncomputable def treeCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Sym2 (Fin n)))).filter
    (fun T : Finset (Sym2 (Fin n)) =>
      (fromEdgeSet (↑T : Set (Sym2 (Fin n)))).IsTree ∧
      ∀ e ∈ T, ¬ e.IsDiag)).card

/-- The spanning trees of any graph on `Fin n` inject into the universal
tree count. -/
lemma card_spanningTrees_le_treeCount {n : ℕ} (H : SimpleGraph (Fin n))
    [Fintype H.edgeSet] : (spanningTrees H).card ≤ treeCount n := by
  classical
  unfold treeCount
  apply Finset.card_le_card
  intro T hT
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ T, isTree_of_mem_spanningTrees H hT, ?_⟩
  intro e he
  have hmem := spanningTrees_subset H hT he
  rw [SimpleGraph.mem_edgeFinset] at hmem
  exact H.not_isDiag_of_mem_edgeSet hmem

/-- **Uniform Penrose bound:** `|φ(X)| ≤ treeCount n` for every polymer
system and every `n`-tuple — the tree-graph inequality with a majorant
independent of `X`.  This is the form the per-size cluster weight estimate
consumes; step (iii) of Target B is now exactly the pure counting statement
that `treeCount` grows at Cayley order. -/
theorem abs_ursell_le_treeCount (P : PolymerSystem) {n : ℕ}
    (X : Fin n → P.Polymer) [Fintype (incompGraph P X).edgeSet] :
    |ursell P X| ≤ (treeCount n : ℤ) := by
  calc |ursell P X| ≤ ((spanningTrees (incompGraph P X)).card : ℤ) :=
        abs_ursell_le_card_spanningTrees P X
    _ ≤ (treeCount n : ℤ) := by
        exact_mod_cast card_spanningTrees_le_treeCount (incompGraph P X)

/-- **Step (iii) closed — tree counting at the needed order, via the
parent-function injection.**  A spanning tree is recoverable from its greedy
parent function (`penroseTree_of_spanningTree`), so labeled trees on
`Fin (m+1)` inject into functions `Fin (m+1) → Fin (m+1)`:
`treeCount (m+1) ≤ (m+1)^(m+1)`.  Combined with the proved
`succ_pow_le_exp_mul_factorial`, this is exactly the Cayley-order growth the
per-size cluster bound needs — the full Prüfer bijection is unnecessary. -/
theorem treeCount_le_pow (m : ℕ) :
    treeCount (m + 1) ≤ (m + 1) ^ (m + 1) := by
  classical
  unfold treeCount
  have hcard : ((Finset.univ :
      Finset (Fin (m + 1) → Fin (m + 1)))).card = (m + 1) ^ (m + 1) := by
    simp
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun T => bfsParent T)
  · intro T _
    exact Finset.mem_univ _
  · intro T₁ h₁ T₂ h₂ heq
    rw [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    have hmem : ∀ {T : Finset (Sym2 (Fin (m + 1)))},
        (fromEdgeSet (↑T : Set (Sym2 (Fin (m + 1))))).IsTree →
        (∀ e ∈ T, ¬ e.IsDiag) →
        T ∈ spanningTrees (⊤ : SimpleGraph (Fin (m + 1))) := by
      intro T htree hdiag
      unfold spanningTrees
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun e he => ?_, htree⟩
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
        Set.mem_compl_iff, Sym2.mem_diagSet]
      exact hdiag e he
    have e₁ : penroseTree T₁ = T₁ :=
      penroseTree_of_spanningTree (hmem h₁.2.1 h₁.2.2)
    have e₂ : penroseTree T₂ = T₂ :=
      penroseTree_of_spanningTree (hmem h₂.2.1 h₂.2.2)
    have heq' : bfsParent T₁ = bfsParent T₂ := heq
    rw [← e₁, ← e₂]
    unfold penroseTree
    rw [heq']

/-- **The Penrose bound in closed numerical form:** for any polymer system
and any `(m+1)`-tuple, `|φ(X)| ≤ (m+1)^(m+1)`.  Together with
`succ_pow_le_exp_mul_factorial` this supplies the tree-counting input of the
per-size cluster estimate; of Target B's three open steps only the per-tree
activity walk (ii) remains. -/
theorem abs_ursell_le_succ_pow (P : PolymerSystem) {m : ℕ}
    (X : Fin (m + 1) → P.Polymer) [Fintype (incompGraph P X).edgeSet] :
    |ursell P X| ≤ (((m + 1) ^ (m + 1) : ℕ) : ℤ) :=
  le_trans (abs_ursell_le_treeCount P X)
    (by exact_mod_cast treeCount_le_pow m)

end YangMills.KP

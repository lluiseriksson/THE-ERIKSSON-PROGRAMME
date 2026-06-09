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

end YangMills.KP

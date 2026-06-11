/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.LatticePolymerSystem
import YangMills.KP.SharpShell
import YangMills.KP.ClusterTail

/-!
# Cluster geometry, step B3 — connecting clusters are large

Half B of `docs/CLUSTER-CORRELATION-PLAN.md`: the geometric input of
the correlation decay.  A cluster of the connected lattice gas whose
support meets two distant plaquettes must contain many plaquettes:

* `touchGraph` — the global plaquette-touching graph and its distance;
* `touchGraph_dist_lt_card_of_connected` (B3a) — within one connected
  polymer, touching-distance is bounded by the plaquette count;
* `exists_touching_of_not_disjoint` (B3b) — overlapping supports
  produce a touching pair (the crossing step between incompatible
  polymers).

The cluster-level bound (B3c: distance ≤ linear in total size along
incompatibility paths) composes these and feeds the size-tail bound
`connectedLattice_pinned_tail_volumeUniform` (Half A).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open KP

variable {d N : ℕ} [NeZero N]

/-- The **global plaquette-touching graph**. -/
def touchGraph (d N : ℕ) [NeZero N] :
    SimpleGraph (ConcretePlaquette d N) :=
  SimpleGraph.fromRel plaquetteTouches

open Classical in
/-- **B3a: within-polymer distances are bounded by the size** —
a connected polymer realizes touching-paths between its members. -/
lemma touchGraph_dist_lt_card_of_connected
    {c : Finset (ConcretePlaquette d N)} (hc : IsConnectedPolymer c)
    {p q : ConcretePlaquette d N} (hp : p ∈ c) (hq : q ∈ c) :
    (touchGraph d N).dist p q < c.card := by
  classical
  have hadj : ∀ {x y : ↥c},
      (SimpleGraph.fromRel
        (fun p q : ↥c => plaquetteTouches p.1 q.1)).Adj x y →
      (touchGraph d N).Adj x.1 y.1 := by
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    show (SimpleGraph.fromRel plaquetteTouches).Adj x.1 y.1
    rw [SimpleGraph.fromRel_adj]
    exact ⟨fun h => hxy.1 (Subtype.ext h), hxy.2⟩
  have hdist : (SimpleGraph.fromRel
      (fun p q : ↥c => plaquetteTouches p.1 q.1)).dist
        ⟨p, hp⟩ ⟨q, hq⟩ < Fintype.card ↥c :=
    connected_dist_lt_card hc _ _
  obtain ⟨w, hw⟩ :=
    (hc.preconnected ⟨p, hp⟩ ⟨q, hq⟩).exists_walk_length_eq_dist
  have h1 : (touchGraph d N).dist p q
      ≤ (w.map ⟨Subtype.val, hadj⟩).length :=
    SimpleGraph.dist_le _
  rw [SimpleGraph.Walk.length_map, hw] at h1
  calc (touchGraph d N).dist p q
      ≤ (SimpleGraph.fromRel
          (fun p q : ↥c => plaquetteTouches p.1 q.1)).dist
            ⟨p, hp⟩ ⟨q, hq⟩ := h1
    _ < Fintype.card ↥c := hdist
    _ = c.card := Fintype.card_coe c

open Classical in
/-- **B3b: the crossing** — overlapping edge supports produce a
touching pair of plaquettes. -/
lemma exists_touching_of_not_disjoint
    {c c' : Finset (ConcretePlaquette d N)}
    (h : ¬ Disjoint (c.biUnion plaquetteSupport)
      (c'.biUnion plaquetteSupport)) :
    ∃ p ∈ c, ∃ q ∈ c', plaquetteTouches p q := by
  obtain ⟨e, he, he'⟩ := Finset.not_disjoint_iff.mp h
  obtain ⟨p, hp, hep⟩ := Finset.mem_biUnion.mp he
  obtain ⟨q, hq, heq⟩ := Finset.mem_biUnion.mp he'
  exact ⟨p, hp, q, hq,
    fun hd => (Finset.disjoint_left.mp hd hep) heq⟩

open Classical in
/-- B3a, walk form: connected polymers realize touching-walks of
length below their size. -/
lemma exists_touchWalk_of_connected
    {c : Finset (ConcretePlaquette d N)} (hc : IsConnectedPolymer c)
    {p q : ConcretePlaquette d N} (hp : p ∈ c) (hq : q ∈ c) :
    ∃ W : (touchGraph d N).Walk p q, W.length < c.card := by
  classical
  have hadj : ∀ {x y : ↥c},
      (SimpleGraph.fromRel
        (fun p q : ↥c => plaquetteTouches p.1 q.1)).Adj x y →
      (touchGraph d N).Adj x.1 y.1 := by
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    show (SimpleGraph.fromRel plaquetteTouches).Adj x.1 y.1
    rw [SimpleGraph.fromRel_adj]
    exact ⟨fun h => hxy.1 (Subtype.ext h), hxy.2⟩
  obtain ⟨w, hw⟩ :=
    (hc.preconnected ⟨p, hp⟩ ⟨q, hq⟩).exists_walk_length_eq_dist
  refine ⟨w.map ⟨Subtype.val, hadj⟩, ?_⟩
  rw [SimpleGraph.Walk.length_map, hw]
  calc (SimpleGraph.fromRel
      (fun p q : ↥c => plaquetteTouches p.1 q.1)).dist
        ⟨p, hp⟩ ⟨q, hq⟩
      < Fintype.card ↥c := connected_dist_lt_card hc _ _
    _ = c.card := Fintype.card_coe c

set_option maxHeartbeats 1600000 in
open Classical in
/-- **B3c, the walk construction:** along an incompatibility path
through a cluster of the connected gas, touching-walks thread the
polymers — with total length bounded by the visited sizes plus the
number of crossings. -/
lemma exists_walk_through_cluster {G : Type*} [Group G]
    [MeasurableSpace G] [NeZero d]
    (μ : MeasureTheory.Measure G) (pe : G → ℝ) (β : ℝ) {n : ℕ}
    {X : Fin n → (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer} :
    ∀ {i j : Fin n}
      (w : (KP.incompGraph (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β) X).Walk i j),
      w.IsPath →
      ∀ p ∈ (X i).1, ∀ q ∈ (X j).1,
      ∃ W : (touchGraph d N).Walk p q,
        W.length ≤ (∑ i' ∈ w.support.toFinset, (X i').1.card)
          + w.length := by
  intro i j w
  induction w with
  | @nil u =>
      intro _ p hp q hq
      obtain ⟨W, hW⟩ :=
        exists_touchWalk_of_connected (X u).2.2 hp hq
      refine ⟨W, ?_⟩
      rw [SimpleGraph.Walk.support_nil, SimpleGraph.Walk.length_nil]
      simp only [List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq, Finset.sum_singleton]
      omega
  | @cons u v j' h w' ih =>
      intro hpath p hp q hq
      rw [SimpleGraph.Walk.cons_isPath_iff] at hpath
      obtain ⟨hw'path, hinotin⟩ := hpath
      have hinc : (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).incomp (X u) (X v) :=
        ((KP.incompGraph_adj _ X u v).mp h).2
      obtain ⟨p', hp', q', hq', htouch⟩ :=
        exists_touching_of_not_disjoint hinc
      obtain ⟨W₁, hW₁⟩ :=
        exists_touchWalk_of_connected (X u).2.2 hp hp'
      have hop : ∃ W₂ : (touchGraph d N).Walk p' q',
          W₂.length ≤ 1 := by
        by_cases hpq : p' = q'
        · subst hpq
          exact ⟨SimpleGraph.Walk.nil, Nat.zero_le 1⟩
        · have hadj2 : (touchGraph d N).Adj p' q' := by
            show (SimpleGraph.fromRel plaquetteTouches).Adj p' q'
            rw [SimpleGraph.fromRel_adj]
            exact ⟨hpq, Or.inl htouch⟩
          refine ⟨SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil,
            ?_⟩
          rw [SimpleGraph.Walk.length_cons,
            SimpleGraph.Walk.length_nil]
      obtain ⟨W₂, hW₂⟩ := hop
      obtain ⟨W₃, hW₃⟩ := ih hw'path q' hq' q hq
      refine ⟨(W₁.append W₂).append W₃, ?_⟩
      rw [SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.support_cons]
      rw [List.toFinset_cons,
        Finset.sum_insert (fun hmem =>
          hinotin (List.mem_toFinset.mp hmem))]
      omega

open Classical in
/-- **B3c (the connecting bound):** plaquettes joined through a cluster
of the connected lattice gas are within touching-distance twice the
total plaquette count of the cluster. -/
theorem cluster_dist_le {G : Type*} [Group G]
    [MeasurableSpace G] [NeZero d]
    (μ : MeasureTheory.Measure G) (pe : G → ℝ) (β : ℝ) {n : ℕ}
    {X : Fin n → (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer}
    (hX : KP.IsCluster (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β) X)
    {i₀ j₀ : Fin n} {p q : ConcretePlaquette d N}
    (hp : p ∈ (X i₀).1) (hq : q ∈ (X j₀).1) :
    (touchGraph d N).dist p q ≤ 2 * ∑ i, (X i).1.card := by
  classical
  obtain ⟨w⟩ := hX.preconnected i₀ j₀
  obtain ⟨W, hW⟩ := exists_walk_through_cluster μ pe β
    w.bypass (SimpleGraph.Walk.bypass_isPath w) p hp q hq
  refine le_trans (SimpleGraph.dist_le W) (le_trans hW ?_)
  have h1 : ∑ i' ∈ w.bypass.support.toFinset, (X i').1.card
      ≤ ∑ i', (X i').1.card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h2 : w.bypass.length < n := by
    have := (SimpleGraph.Walk.bypass_isPath w).length_lt
    rwa [Fintype.card_fin] at this
  have h3 : n ≤ ∑ i', (X i').1.card := by
    calc n = ∑ _i' : Fin n, 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_univ, Fintype.card_fin]
      _ ≤ ∑ i', (X i').1.card :=
          Finset.sum_le_sum fun i' _ =>
            Finset.card_pos.mpr (X i').2.1
  omega

set_option maxHeartbeats 800000 in
open Classical in
/-- **The connecting-sum domination:** pinned cluster sums restricted
to clusters touching a distant plaquette are dominated by the
size-restricted pinned weights — B3's geometry feeds Half A's tail. -/
lemma connecting_pinned_le_GE {G : Type*} [Group G]
    [MeasurableSpace G] [NeZero d]
    (μ : MeasureTheory.Measure G) (pe : G → ℝ) (β : ℝ)
    {p q : ConcretePlaquette d N}
    (c : (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer)
    (hp : p ∈ c.1) (n : ℕ) :
    (((n + 1).factorial : ℝ))⁻¹ *
      ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
        (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).Polymer)).filter
        (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
        |((KP.ursell (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β) X : ℤ) : ℝ)| *
          ∏ i, ‖(connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).activity (X i)‖
    ≤ KP.pinnedClusterWeightGE (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β)
        (fun c' => c'.1.card) c ((touchGraph d N).dist p q / 2) n := by
  classical
  unfold KP.pinnedClusterWeightGE
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- restrict to genuine clusters (non-clusters contribute zero)
  rw [show ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) →
      (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β).Polymer)).filter
      (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1),
      |((KP.ursell (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β) X : ℤ) : ℝ)| *
        ∏ i, ‖(connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).activity (X i)‖
    = ∑ X ∈ ((Finset.univ : Finset (Fin (n + 1) →
        (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).Polymer)).filter
        (fun X => X 0 = c ∧ ∃ j, q ∈ (X j).1)).filter
        (fun X => KP.IsCluster (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β) X),
        |((KP.ursell (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β) X : ℤ) : ℝ)| *
          ∏ i, ‖(connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).activity (X i)‖
    from (Finset.sum_filter_of_ne fun X _ hne => by
      by_contra hnc
      exact hne (by
        rw [KP.ursell_eq_zero_of_not_isCluster _ X hnc]
        simp)).symm]
  -- the cluster filter lands in the size-restricted filter
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun X _ _ =>
    mul_nonneg (abs_nonneg _)
      (Finset.prod_nonneg fun i _ => norm_nonneg _)
  intro X hX
  rw [Finset.mem_filter, Finset.mem_filter] at hX
  obtain ⟨⟨-, hX0, j, hqj⟩, hclus⟩ := hX
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hX0, ?_⟩
  have hp0 : p ∈ (X 0).1 := by rw [hX0]; exact hp
  have hdist := cluster_dist_le μ pe β hclus hp0 hqj
  have hsz : ∑ i, (fun c' : (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer => c'.1.card) (X i)
      = ∑ i, (X i).1.card := rfl
  omega

end YangMills

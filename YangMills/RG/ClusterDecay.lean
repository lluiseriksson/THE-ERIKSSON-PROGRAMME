/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.HolePolymerSystem
import YangMills.RG.ModifiedMetric
import YangMills.RG.LocalKP
import YangMills.KP.Cluster
import YangMills.KP.Ursell
import YangMills.KP.MayerInversion
import YangMills.KP.Restriction

attribute [local instance] Classical.propDecidable

open Finset
open YangMills.KP


namespace YangMills.RG

/-- The union of all polymers in a cluster. -/
def clusterUnion {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer) : Finset (Cube d L) :=
  univ.biUnion (fun i => (X i).val)

/-- A finite union of sets that each respect the hole family still respects the
hole family.  A hole is either contained in one summand, hence in the union, or
disjoint from every summand, hence disjoint from the union. -/
lemma polymerWithHoles_biUnion {d L : ℕ} {α : Type*} [DecidableEq α]
    (H : HoleFamily d L) (S : Finset α) (F : α → Finset (Cube d L))
    (hF : ∀ a ∈ S, polymerWithHoles H (F a)) :
    polymerWithHoles H (S.biUnion F) := by
  intro H₀ hH₀
  by_cases hsome : ∃ a ∈ S, H₀ ⊆ F a
  · left
    obtain ⟨a, ha, hsub⟩ := hsome
    intro x hx
    rw [mem_biUnion]
    exact ⟨a, ha, hsub hx⟩
  · right
    rw [disjoint_iff_ne]
    intro x hx y hy hxy
    subst y
    rw [mem_biUnion] at hy
    obtain ⟨a, ha, hyF⟩ := hy
    have hpoly := hF a ha H₀ hH₀
    rcases hpoly with hsub | hdisj
    · exact hsome ⟨a, ha, hsub⟩
    · rw [disjoint_iff_ne] at hdisj
      exact hdisj x hx x hyF rfl

/-- The raw union of a tuple of hole polymers is itself hole-respecting. -/
lemma clusterUnion_polymerWithHoles {d L : ℕ} [NeZero L] (H : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ) {n : ℕ}
    (X : Fin n → (holePolymerSystem H z).Polymer) :
    polymerWithHoles H (clusterUnion H z X) := by
  dsimp [clusterUnion]
  exact polymerWithHoles_biUnion H univ (fun i => (X i).val)
    (fun i _ => (X i).property.right.right)

/-- A nonempty tuple of hole polymers has a nonempty raw union. -/
lemma clusterUnion_nonempty {d L : ℕ} [NeZero L] (H : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ) {n : ℕ}
    (X : Fin (n + 1) → (holePolymerSystem H z).Polymer) :
    (clusterUnion H z X).Nonempty := by
  obtain ⟨x, hx⟩ := (X 0).property.left
  refine ⟨x, ?_⟩
  dsimp [clusterUnion]
  rw [mem_biUnion]
  exact ⟨0, mem_univ 0, hx⟩

/-- The modified metric of a cluster, defined as the modified metric of its union.

This is the source-shaped cluster object `d_M(Y, mod Ωᶜ)`: the cluster is first
collected into one polymer-like union `Y`, then the modified metric is evaluated
on that union.  Do not infer from `X i ⊆ clusterUnion H z X` that
`discreteModifiedMetric H (X i).val ≤ clusterModifiedMetric H z X` for arbitrary
clusters: the modified metric is a constrained Steiner minimum, and enlarging
the ambient set can introduce shortcuts.  The comparison below is proved only
for the degenerate `Fin 1` case, where the union is definitionally the polymer
itself. -/
noncomputable def clusterModifiedMetric {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer) : ℕ :=
  discreteModifiedMetric H (clusterUnion H z X)

lemma skeleton_biUnion {d L : ℕ} {α : Type*} [DecidableEq α] (H : HoleFamily d L) (S : Finset α) (F : α → Finset (Cube d L)) :
    skeleton H (S.biUnion F) = S.biUnion (fun a => skeleton H (F a)) := by
  unfold skeleton
  ext x
  simp only [mem_filter, mem_biUnion]
  constructor
  · rintro ⟨⟨a, ha, hx⟩, hnot⟩
    exact ⟨a, ha, hx, hnot⟩
  · rintro ⟨a, ha, hx, hnot⟩
    exact ⟨⟨a, ha, hx⟩, hnot⟩

lemma clusterUnion_skeleton {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer) :
    skeleton H (clusterUnion H z X) = univ.biUnion (fun i => skeleton H (X i).val) := by
  dsimp [clusterUnion]
  exact skeleton_biUnion H univ (fun i => (X i).val)

lemma clusterUnion_fin_one {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X : Fin 1 → (holePolymerSystem H z).Polymer) :
    clusterUnion H z X = (X 0).val := by
  dsimp [clusterUnion]
  ext x
  simp only [mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hx⟩
    have : i = 0 := Subsingleton.elim i 0
    rw [this] at hx
    exact hx
  · intro hx
    exact ⟨0, hx⟩

lemma clusterModifiedMetric_fin_one {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X : Fin 1 → (holePolymerSystem H z).Polymer) :
    clusterModifiedMetric H z X = discreteModifiedMetric H (X 0).val := by
  dsimp [clusterModifiedMetric]
  rw [clusterUnion_fin_one]

/-- The decay weight function of a cluster under the modified metric. -/
noncomputable def clusterDecayWeight {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (q : ℝ) {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer) : ℝ :=
  q ^ (clusterModifiedMetric H z X + 1)

lemma clusterDecayWeight_fin_one {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (q : ℝ) (X : Fin 1 → (holePolymerSystem H z).Polymer) :
    clusterDecayWeight H z q X = q ^ (discreteModifiedMetric H (X 0).val + 1) := by
  dsimp [clusterDecayWeight]
  rw [clusterModifiedMetric_fin_one]

lemma walkConnected_union {V : Type*} [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    (hA : walkConnected G A) (hB : walkConnected G B)
    (hab : ¬ Disjoint A B ∨ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b) :
    walkConnected G (A ∪ B) := by
  intro x hx y hy
  rw [mem_union] at hx hy
  rcases hx with hxA | hxB
  · rcases hy with hyA | hyB
    · obtain ⟨w, hw⟩ := hA x hxA y hyA
      refine ⟨w, fun v hv => mem_union.mpr (Or.inl (hw v hv))⟩
    · rcases hab with h_int | ⟨a, haA, b, hbB, hadj⟩
      · rw [disjoint_iff_ne] at h_int
        push_neg at h_int
        obtain ⟨z, hzA, b, hbB, rfl⟩ := h_int
        obtain ⟨w1, hw1⟩ := hA x hxA z hzA
        obtain ⟨w2, hw2⟩ := hB z hbB y hyB
        refine ⟨w1.append w2, ?_⟩
        intro v hv
        rw [SimpleGraph.Walk.mem_support_append_iff] at hv
        rw [mem_union]
        rcases hv with hv1 | hv2
        · left; exact hw1 v hv1
        · right; exact hw2 v hv2
      · obtain ⟨w1, hw1⟩ := hA x hxA a haA
        obtain ⟨w2, hw2⟩ := hB b hbB y hyB
        let w_edge := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
        refine ⟨w1.append w_edge |>.append w2, ?_⟩
        intro v hv
        rw [SimpleGraph.Walk.mem_support_append_iff] at hv
        rcases hv with hv12 | hv2
        · rw [SimpleGraph.Walk.mem_support_append_iff] at hv12
          rcases hv12 with hv1 | hve
          · rw [mem_union]; left; exact hw1 v hv1
          · dsimp [w_edge] at hve
            simp at hve
            rcases hve with rfl | rfl
            · rw [mem_union]; left; exact haA
            · rw [mem_union]; right; exact hbB
        · rw [mem_union]; right; exact hw2 v hv2
  · rcases hy with hyA | hyB
    · rcases hab with h_int | ⟨a, haA, b, hbB, hadj⟩
      · rw [disjoint_iff_ne] at h_int
        push_neg at h_int
        obtain ⟨z, hzA, b, hbB, rfl⟩ := h_int
        obtain ⟨w1, hw1⟩ := hB x hxB z hbB
        obtain ⟨w2, hw2⟩ := hA z hzA y hyA
        refine ⟨w1.append w2, ?_⟩
        intro v hv
        rw [SimpleGraph.Walk.mem_support_append_iff] at hv
        rw [mem_union]
        rcases hv with hv1 | hv2
        · right; exact hw1 v hv1
        · left; exact hw2 v hv2
      · obtain ⟨w1, hw1⟩ := hB x hxB b hbB
        obtain ⟨w2, hw2⟩ := hA a haA y hyA
        have hadj_symm := G.symm hadj
        let w_edge := SimpleGraph.Walk.cons hadj_symm SimpleGraph.Walk.nil
        refine ⟨w1.append w_edge |>.append w2, ?_⟩
        intro v hv
        rw [SimpleGraph.Walk.mem_support_append_iff] at hv
        rcases hv with hv12 | hv2
        · rw [SimpleGraph.Walk.mem_support_append_iff] at hv12
          rcases hv12 with hv1 | hve
          · rw [mem_union]; right; exact hw1 v hv1
          · dsimp [w_edge] at hve
            simp at hve
            rcases hve with rfl | rfl
            · rw [mem_union]; right; exact hbB
            · rw [mem_union]; left; exact haA
        · rw [mem_union]; left; exact hw2 v hv2
    · obtain ⟨w, hw⟩ := hB x hxB y hyB
      refine ⟨w, fun v hv => mem_union.mpr (Or.inr (hw v hv))⟩

-- Helper 1: closedNeigh of a connected set is connected
lemma cubeConnected_closedNeigh {d L : ℕ} [NeZero L] (S : Finset (Cube d L)) (hS : cubeConnected S) :

    cubeConnected (closedNeigh S) := by
  intro x hx y hy
  have h_to_S : ∀ u ∈ closedNeigh S,
      ∃ u' ∈ S, ∃ w : (cubeAdj d L).Walk u u', (∀ v ∈ w.support, v ∈ closedNeigh S) := by
    intro u hu
    unfold closedNeigh at hu ⊢
    rw [mem_union] at hu
    rcases hu with huS | huN
    · refine ⟨u, huS, SimpleGraph.Walk.nil, ?_⟩
      intro v hv
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      subst hv
      exact mem_union.mpr (Or.inl huS)
    · rw [mem_biUnion] at huN
      obtain ⟨u', hu'S, hun⟩ := huN
      rw [SimpleGraph.mem_neighborFinset] at hun
      have hun_symm := (cubeAdj d L).symm hun
      let w := SimpleGraph.Walk.cons hun_symm SimpleGraph.Walk.nil
      refine ⟨u', hu'S, w, ?_⟩
      intro v hv
      simp only [w, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons] at hv
      rcases hv with rfl | rfl | hv_nil
      · refine mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨u', hu'S, ?_⟩))
        rw [SimpleGraph.mem_neighborFinset]
        exact hun
      · exact mem_union.mpr (Or.inl hu'S)
      · rw [List.mem_nil_iff] at hv_nil
        exact False.elim hv_nil
  obtain ⟨x', hx'S, wx, hwx⟩ := h_to_S x hx
  obtain ⟨y', hy'S, wy, hwy⟩ := h_to_S y hy
  obtain ⟨w_mid, hw_mid⟩ := hS x' hx'S y' hy'S
  let w := wx.append (w_mid.append wy.reverse)
  refine ⟨w, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hv_x | hv_mid_y
  · exact hwx v hv_x
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hv_mid_y
    rcases hv_mid_y with hv_mid | hv_y
    · have h_in := hw_mid v hv_mid
      exact mem_union.mpr (Or.inl h_in)
    · have hv_y_rev : v ∈ wy.support := by
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv_y
        exact hv_y
      exact hwy v hv_y_rev

-- Helper 2: incompatible polymers have intersecting closed neighborhoods
lemma closedNeigh_intersect_of_incomp {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X Y : (holePolymerSystem H z).Polymer) (h : (holePolymerSystem H z).incomp X Y) :
    ¬ Disjoint (closedNeigh X.val) (closedNeigh Y.val) := by
  have hne := incomp_imp_intersect H z X Y h
  intro hd
  rw [disjoint_iff_inter_eq_empty] at hd
  have h_sub : Y.val ∩ closedNeigh X.val ⊆ closedNeigh X.val ∩ closedNeigh Y.val := by
    intro w hw
    rw [mem_inter] at hw ⊢
    refine ⟨hw.2, ?_⟩
    unfold closedNeigh
    exact subset_union_left hw.1
  have h_empty : Y.val ∩ closedNeigh X.val = ∅ := by
    exact subset_empty.mp (hd ▸ h_sub)
  rw [h_empty] at hne
  exact not_nonempty_empty hne

-- Helper 3: General graph union connectivity lemma
lemma walk_union_connected {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {H_type : Type*} [DecidableEq H_type] (H : SimpleGraph H_type)
    (A : V → Finset H_type) (hA : ∀ i, walkConnected H (A i))
    (hadj : ∀ i j, G.Adj i j → ¬ Disjoint (A i) (A j))
    {i j : V} (w : G.Walk i j) (x : H_type) (hx : x ∈ A i) (y : H_type) (hy : y ∈ A j) :
    ∃ w_H : H.Walk x y, ∀ v ∈ w_H.support, ∃ k ∈ w.support, v ∈ A k := by
  induction w generalizing x with
  | nil =>
      obtain ⟨w_H, hw_H⟩ := hA _ x hx y hy
      refine ⟨w_H, ?_⟩
      intro v hv
      refine ⟨_, ?_, hw_H v hv⟩
      simp [SimpleGraph.Walk.support_nil]
  | cons hadj_edge w' ih =>
      have h_not_disj := hadj _ _ hadj_edge
      rw [disjoint_iff_ne] at h_not_disj
      push_neg at h_not_disj
      obtain ⟨z_val, hz_u, z', hz_next, rfl⟩ := h_not_disj
      have h_ih := ih z_val hz_next hy
      obtain ⟨w_tail, hw_tail⟩ := h_ih
      obtain ⟨w_head, hw_head⟩ := hA _ x hx z_val hz_u
      let w_total := w_head.append w_tail
      refine ⟨w_total, ?_⟩
      intro v hv
      rw [SimpleGraph.Walk.mem_support_append_iff] at hv
      rcases hv with hv_head | hv_tail
      · refine ⟨_, ?_, hw_head v hv_head⟩
        simp [SimpleGraph.Walk.support_cons]
      · obtain ⟨k, hk_tail, hv_in⟩ := hw_tail v hv_tail
        refine ⟨k, ?_, hv_in⟩
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ hk_tail

/-- General graph union connectivity lemma when adjacent index-vertices carry
sets that either overlap or touch by one edge. -/
lemma walk_union_connected_touching {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {H_type : Type*} [DecidableEq H_type] (H : SimpleGraph H_type)
    (A : V → Finset H_type) (hA : ∀ i, walkConnected H (A i))
    (hadj : ∀ i j, G.Adj i j →
      ¬ Disjoint (A i) (A j) ∨ ∃ a ∈ A i, ∃ b ∈ A j, H.Adj a b)
    {i j : V} (w : G.Walk i j) (x : H_type) (hx : x ∈ A i)
    (y : H_type) (hy : y ∈ A j) :
    ∃ w_H : H.Walk x y, ∀ v ∈ w_H.support, ∃ k ∈ w.support, v ∈ A k := by
  induction w generalizing x with
  | nil =>
      obtain ⟨w_H, hw_H⟩ := hA _ x hx y hy
      refine ⟨w_H, ?_⟩
      intro v hv
      refine ⟨_, ?_, hw_H v hv⟩
      simp [SimpleGraph.Walk.support_nil]
  | cons hadj_edge w' ih =>
      rcases hadj _ _ hadj_edge with h_int | h_touch
      · rw [disjoint_iff_ne] at h_int
        push_neg at h_int
        obtain ⟨z_val, hz_u, z', hz_next, rfl⟩ := h_int
        have h_tail := ih z_val hz_next hy
        obtain ⟨w_tail, hw_tail⟩ := h_tail
        obtain ⟨w_head, hw_head⟩ := hA _ x hx z_val hz_u
        let w_total := w_head.append w_tail
        refine ⟨w_total, ?_⟩
        intro v hv
        rw [SimpleGraph.Walk.mem_support_append_iff] at hv
        rcases hv with hv_head | hv_tail
        · refine ⟨_, ?_, hw_head v hv_head⟩
          simp [SimpleGraph.Walk.support_cons]
        · obtain ⟨k, hk_tail, hv_in⟩ := hw_tail v hv_tail
          refine ⟨k, ?_, hv_in⟩
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ hk_tail
      · obtain ⟨a, ha_u, b, hb_next, hab⟩ := h_touch
        have h_tail := ih b hb_next hy
        obtain ⟨w_tail, hw_tail⟩ := h_tail
        obtain ⟨w_head, hw_head⟩ := hA _ x hx a ha_u
        let w_edge := SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil
        let w_total := (w_head.append w_edge).append w_tail
        refine ⟨w_total, ?_⟩
        intro v hv
        rw [SimpleGraph.Walk.mem_support_append_iff] at hv
        rcases hv with hv_head_edge | hv_tail
        · rw [SimpleGraph.Walk.mem_support_append_iff] at hv_head_edge
          rcases hv_head_edge with hv_head | hv_edge
          · refine ⟨_, ?_, hw_head v hv_head⟩
            simp [SimpleGraph.Walk.support_cons]
          · dsimp [w_edge] at hv_edge
            simp at hv_edge
            rcases hv_edge with rfl | hv_edge
            · refine ⟨_, ?_, ha_u⟩
              simp [SimpleGraph.Walk.support_cons]
            · rcases hv_edge with rfl
              refine ⟨_, ?_, hb_next⟩
              rw [SimpleGraph.Walk.support_cons]
              exact List.mem_cons_of_mem _ (by simp)
        · obtain ⟨k, hk_tail, hv_in⟩ := hw_tail v hv_tail
          refine ⟨k, ?_, hv_in⟩
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ hk_tail

/-- A genuine cluster's raw polymer union is connected.  This uses the
source-faithful incompatibility relation on hole polymers: polymers in the same
cluster are chained by overlaps or one-step cube adjacency. -/
lemma clusterUnion_connected {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer)
    (hcl : IsCluster (holePolymerSystem H z) X) :
    cubeConnected (clusterUnion H z X) := by
  intro x hx y hy
  dsimp [clusterUnion] at hx hy
  rw [mem_biUnion] at hx hy
  obtain ⟨i, _, hx_i⟩ := hx
  obtain ⟨j, _, hy_j⟩ := hy
  obtain ⟨w⟩ := hcl.1 i j
  have h_walk := walk_union_connected_touching (incompGraph (holePolymerSystem H z) X)
    (cubeAdj d L)
    (fun k => (X k).val)
    (fun k => (X k).property.right.left)
    (fun a b hab => by
      rw [incompGraph_adj] at hab
      exact hab.2)
    w x hx_i y hy_j
  obtain ⟨w_H, hw_H⟩ := h_walk
  refine ⟨w_H, ?_⟩
  intro v hv
  obtain ⟨k, _, hv_in⟩ := hw_H v hv
  dsimp [clusterUnion]
  rw [mem_biUnion]
  exact ⟨k, mem_univ k, hv_in⟩

/-- A nonempty genuine cluster tuple can be collapsed to the single
hole-respecting polymer given by its raw union.  This packages the three
cluster-union facts needed downstream: nonemptiness, connectedness, and the
hole-respecting condition. -/
def clusterUnionPolymer {d L : ℕ} [NeZero L] (H : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ) {n : ℕ}
    (X : Fin (n + 1) → (holePolymerSystem H z).Polymer)
    (hcl : IsCluster (holePolymerSystem H z) X) :
    (holePolymerSystem H z).Polymer :=
  ⟨clusterUnion H z X,
    clusterUnion_nonempty H z X,
    clusterUnion_connected H z X hcl,
    clusterUnion_polymerWithHoles H z X⟩

/-- For a genuine cluster, the cluster modified metric controls the size of the
active skeleton of the cluster union.  This is the source-faithful cluster-level
version of `skeleton_card_le_discreteModifiedMetric_add_one`: the metric is
evaluated on the whole cluster union, not on an arbitrary constituent polymer. -/
lemma clusterUnion_skeleton_card_le_clusterModifiedMetric_add_one {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer)
    (hcl : IsCluster (holePolymerSystem H z) X) :
    (skeleton H (clusterUnion H z X)).card ≤ clusterModifiedMetric H z X + 1 := by
  dsimp [clusterModifiedMetric]
  exact skeleton_card_le_discreteModifiedMetric_add_one H (clusterUnion H z X)
    (clusterUnion_connected H z X hcl)

-- Target 8.3: cluster union of closed neighborhoods is connected
lemma cluster_closedNeigh_union_connected {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer) (hcl : IsCluster (holePolymerSystem H z) X) :
    cubeConnected (univ.biUnion (fun i => closedNeigh (X i).val)) := by
  intro x hx y hy
  rw [mem_biUnion] at hx hy
  obtain ⟨i, _, hx_c⟩ := hx
  obtain ⟨j, _, hy_c⟩ := hy
  obtain ⟨w⟩ := hcl.1 i j
  have h_walk := walk_union_connected (incompGraph (holePolymerSystem H z) X) (cubeAdj d L)
    (fun k => closedNeigh (X k).val)
    (fun k => cubeConnected_closedNeigh (X k).val (X k).property.right.left)
    (fun a b hab => closedNeigh_intersect_of_incomp H z (X a) (X b) (by
      rw [incompGraph_adj] at hab
      exact hab.2))
    w x hx_c y hy_c
  obtain ⟨w_H, hw_H⟩ := h_walk
  refine ⟨w_H, ?_⟩
  intro v hv
  obtain ⟨k, _, hv_in⟩ := hw_H v hv
  rw [mem_biUnion]
  refine ⟨k, mem_univ _, hv_in⟩

-- Helper 4: Term-wise bound for cluster activity remainder sum
lemma clusterRemainderSum_term_le {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (r : Cube d L) (n : ℕ) :
    (((n + 1).factorial : ℝ))⁻¹ *
      ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
        (fun X => IsCluster (holePolymerSystem H z) X ∧ r ∈ clusterUnion H z X),
        |((ursell (holePolymerSystem H z) X : ℤ) : ℝ)| * ∏ i, ‖(holePolymerSystem H z).activity (X i)‖
    ≤ ((n : ℝ) + 1) * ∑ c ∈ Finset.univ.filter (fun c => r ∈ (c : PolymerType H z).val),
        pinnedClusterWeight (holePolymerSystem H z) c n := by
  classical
  let P := holePolymerSystem H z
  set f : (Fin (n + 1) → PolymerType H z) → ℝ :=
    fun X => |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖ with hf
  have hf0 : ∀ X, 0 ≤ f X := fun X =>
    mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hfswap : ∀ (σ : Equiv.Perm (Fin (n + 1))) (X : Fin (n + 1) → PolymerType H z), f (X ∘ σ) = f X := by
    intro σ X
    rw [hf]
    simp only
    rw [ursell_comp_equiv P X σ]
    congr 1
    exact Equiv.prod_comp σ (fun k => ‖P.activity (X k)‖)
  have hidx : ∀ i : Fin (n + 1),
      ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun X => r ∈ (X i).val), f X
      = ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun Y => r ∈ (Y 0).val), f Y := by
    intro i
    refine Finset.sum_nbij' (i := fun X => X ∘ Equiv.swap 0 i) (j := fun Y => Y ∘ Equiv.swap 0 i) ?_ ?_ ?_ ?_ ?_
    · intro X hX
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show r ∈ ((X ∘ Equiv.swap 0 i) 0).val
      have h0 : (X ∘ Equiv.swap 0 i) 0 = X i := by simp [Function.comp, Equiv.swap_apply_left]
      rw [h0]
      exact (Finset.mem_filter.mp hX).2
    · intro Y hY
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show r ∈ ((Y ∘ Equiv.swap 0 i) i).val
      have h0 : (Y ∘ Equiv.swap 0 i) i = Y 0 := by simp [Function.comp, Equiv.swap_apply_right]
      rw [h0]
      exact (Finset.mem_filter.mp hY).2
    · intro X _
      funext k
      simp [Function.comp, Equiv.swap_apply_self]
    · intro Y _
      funext k
      simp [Function.comp, Equiv.swap_apply_self]
    · intro X _
      exact (hfswap _ X).symm
  have hmain : ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun X => IsCluster P X ∧ r ∈ clusterUnion H z X), f X
      ≤ ((n : ℝ) + 1) * ∑ c ∈ Finset.univ.filter (fun c => r ∈ (c : PolymerType H z).val),
          ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun Y => Y 0 = c), f Y := by
    calc ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun X => IsCluster P X ∧ r ∈ clusterUnion H z X), f X
        -- drop IsCluster
        ≤ ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun X => r ∈ clusterUnion H z X), f X := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun X _ _ => hf0 X)
          intro X hX
          rw [mem_filter] at hX ⊢
          exact ⟨hX.1, hX.2.2⟩
      _ ≤ ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun X => r ∈ clusterUnion H z X),
            ∑ i : Fin (n + 1), if r ∈ (X i).val then f X else 0 := by
          refine Finset.sum_le_sum fun X hX => ?_
          obtain ⟨i₀, hi₀⟩ : ∃ i, r ∈ (X i).val := by
            have hm := (Finset.mem_filter.mp hX).2
            dsimp [clusterUnion] at hm
            rw [mem_biUnion] at hm
            rcases hm with ⟨i, _, hi⟩
            exact ⟨i, hi⟩
          have hX0 : f X = if r ∈ (X i₀).val then f X else 0 := by rw [if_pos hi₀]
          refine le_trans (le_of_eq hX0) ?_
          refine Finset.single_le_sum (f := fun i => if r ∈ (X i).val then f X else 0) (fun i _ => ?_) (Finset.mem_univ i₀)
          show (0 : ℝ) ≤ if r ∈ (X i).val then f X else 0
          split_ifs
          · exact hf0 X
          · exact le_rfl
      _ ≤ ∑ X : Fin (n + 1) → PolymerType H z, ∑ i : Fin (n + 1), if r ∈ (X i).val then f X else 0 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun X _ _ => ?_)
          refine Finset.sum_nonneg fun i _ => ?_
          split_ifs
          · exact hf0 X
          · exact le_rfl
      _ = ∑ i : Fin (n + 1), ∑ X : Fin (n + 1) → PolymerType H z, if r ∈ (X i).val then f X else 0 := Finset.sum_comm
      _ = ∑ i : Fin (n + 1), ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun X => r ∈ (X i).val), f X := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (Finset.sum_filter _ _).symm
      _ = ∑ _i : Fin (n + 1), ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun Y => r ∈ (Y 0).val), f Y :=
          Finset.sum_congr rfl fun i _ => hidx i
      _ = ((n : ℝ) + 1) * ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun Y => r ∈ (Y 0).val), f Y := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ = ((n : ℝ) + 1) * ∑ c ∈ Finset.univ.filter (fun c => r ∈ (c : PolymerType H z).val),
            ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun Y => Y 0 = c), f Y := by
          congr 1
          rw [← Finset.sum_fiberwise_of_maps_to (g := fun Y => Y 0) (fun Y hY => ?_) f]
          · refine Finset.sum_congr rfl fun c hc => ?_
            rw [Finset.filter_filter]
            refine Finset.sum_congr ?_ fun _ _ => rfl
            refine Finset.filter_congr fun Y _ => ?_
            constructor
            · exact fun h => h.2
            · intro h
              refine ⟨?_, h⟩
              show r ∈ (Y 0).val
              rw [h]
              exact Finset.mem_filter.mp hc |>.2
          · rw [mem_filter] at hY
            refine Finset.mem_filter.mpr ⟨mem_univ _, hY.2⟩
  calc (((n + 1).factorial : ℝ))⁻¹ * ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun X => IsCluster P X ∧ r ∈ clusterUnion H z X), f X
      ≤ (((n + 1).factorial : ℝ))⁻¹ * (((n : ℝ) + 1) * ∑ c ∈ Finset.univ.filter (fun c => r ∈ (c : PolymerType H z).val),
          ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun Y => Y 0 = c), f Y) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ((n : ℝ) + 1) * ((((n + 1).factorial : ℝ))⁻¹ * ∑ c ∈ Finset.univ.filter (fun c => r ∈ (c : PolymerType H z).val),
          ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun Y => Y 0 = c), f Y) := by ring
    _ = ((n : ℝ) + 1) * ∑ c ∈ Finset.univ.filter (fun c => r ∈ (c : PolymerType H z).val), (((n + 1).factorial : ℝ))⁻¹ *
          ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter (fun Y => Y 0 = c), f Y := by
        rw [Finset.mul_sum]
    _ = ((n : ℝ) + 1) * ∑ c ∈ Finset.univ.filter (fun c => r ∈ (c : PolymerType H z).val),
          pinnedClusterWeight P c n := rfl

noncomputable def clusterRemainderSumTerm {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (r : Cube d L) (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
      (fun X => IsCluster (holePolymerSystem H z) X ∧ r ∈ clusterUnion H z X),
      |((ursell (holePolymerSystem H z) X : ℤ) : ℝ)| * ∏ i, ‖(holePolymerSystem H z).activity (X i)‖

/-- The source-shaped skeleton-pinned cluster remainder term: the cluster is
pinned only when `r` lies in the active skeleton of the cluster union, not
merely anywhere in the raw union. -/
noncomputable def clusterSkeletonRemainderSumTerm {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (r : Cube d L) (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
      (fun X => IsCluster (holePolymerSystem H z) X ∧
        r ∈ skeleton H (clusterUnion H z X)),
      |((ursell (holePolymerSystem H z) X : ℤ) : ℝ)| * ∏ i, ‖(holePolymerSystem H z).activity (X i)‖

theorem clusterRemainderSum_summable {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (r : Cube d L) (t : ℝ) (ht : 0 < t)
    (hkp : KPCriterion ((holePolymerSystem H z).scaleActivity (Real.exp t)) (fun X => (X.val.card : ℝ))) :
    Summable (fun n => clusterRemainderSumTerm H z r n) := by
  have hnn : ∀ n, 0 ≤ clusterRemainderSumTerm H z r n := by
    intro n
    unfold clusterRemainderSumTerm
    positivity
  have h_le : ∀ n, clusterRemainderSumTerm H z r n
      ≤ t⁻¹ * ∑ c ∈ Finset.univ.filter (fun c => r ∈ (c : PolymerType H z).val),
        pinnedClusterWeight ((holePolymerSystem H z).scaleActivity (Real.exp t)) c n := by
    intro n
    have h_term := clusterRemainderSum_term_le H z r n
    refine le_trans h_term ?_
    rw [mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have h1 : t * ((n : ℝ) + 1) ≤ Real.exp (t * ((n : ℝ) + 1)) := by
      have h2 := Real.add_one_le_exp (t * ((n : ℝ) + 1))
      linarith
    have h3 : (Real.exp t : ℝ) ^ (n + 1) = Real.exp (t * ((n : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hfac : ((n : ℝ) + 1) ≤ t⁻¹ * Real.exp t ^ (n + 1) := by
      rw [h3]
      exact (le_inv_mul_iff₀ ht).mpr h1
    calc ((n : ℝ) + 1) * pinnedClusterWeight (holePolymerSystem H z) c n
      _ ≤ (t⁻¹ * Real.exp t ^ (n + 1)) * pinnedClusterWeight (holePolymerSystem H z) c n := by
        refine mul_le_mul_of_nonneg_right hfac (pinnedClusterWeight_nonneg _ _ _)
      _ = t⁻¹ * pinnedClusterWeight ((holePolymerSystem H z).scaleActivity (Real.exp t)) c n := by
        rw [pinnedClusterWeight_scale, abs_of_pos (Real.exp_pos t)]
        ring
  have h_sum : Summable (fun n => t⁻¹ * ∑ c ∈ Finset.univ.filter (fun c => r ∈ (c : PolymerType H z).val),
      pinnedClusterWeight ((holePolymerSystem H z).scaleActivity (Real.exp t)) c n) := by
    refine Summable.mul_left _ ?_
    refine summable_sum fun c _ => ?_
    exact (pinned_cluster_summable_sharp ((holePolymerSystem H z).scaleActivity (Real.exp t)) hkp c).1
  exact Summable.of_nonneg_of_le hnn h_le h_sum

/-- Termwise domination of the skeleton-pinned remainder by the raw-union pinned
remainder. -/
lemma clusterSkeletonRemainderSumTerm_le {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (r : Cube d L) (n : ℕ) :
    clusterSkeletonRemainderSumTerm H z r n ≤ clusterRemainderSumTerm H z r n := by
  unfold clusterSkeletonRemainderSumTerm clusterRemainderSumTerm
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun X _ _ => ?_)
  · intro X hX
    rw [mem_filter] at hX ⊢
    exact ⟨hX.1, hX.2.1, skeleton_subset H (clusterUnion H z X) hX.2.2⟩
  · exact mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)

/-- The skeleton-pinned cluster remainder term is bounded by the same pinned
cluster-weight expression as the larger raw-union-pinned term. -/
lemma clusterSkeletonRemainderSum_term_le_pinned {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (r : Cube d L) (n : ℕ) :
    clusterSkeletonRemainderSumTerm H z r n
      ≤ ((n : ℝ) + 1) * ∑ c ∈ Finset.univ.filter (fun c => r ∈ (c : PolymerType H z).val),
        pinnedClusterWeight (holePolymerSystem H z) c n :=
  (clusterSkeletonRemainderSumTerm_le H z r n).trans
    (clusterRemainderSum_term_le H z r n)

/-- Sharper skeleton-pinned domination: if the root lies in the active skeleton
of the cluster union, then after symmetrization one may pin at a constituent
polymer whose own active skeleton contains the root. -/
lemma clusterSkeletonRemainderSum_term_le_skeletonPinned {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (r : Cube d L) (n : ℕ) :
    clusterSkeletonRemainderSumTerm H z r n
      ≤ ((n : ℝ) + 1) *
        ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
          pinnedClusterWeight (holePolymerSystem H z) c n := by
  classical
  let P := holePolymerSystem H z
  set f : (Fin (n + 1) → PolymerType H z) → ℝ :=
    fun X => |((ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖ with hf
  have hf0 : ∀ X, 0 ≤ f X := fun X =>
    mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hfswap : ∀ (σ : Equiv.Perm (Fin (n + 1))) (X : Fin (n + 1) → PolymerType H z),
      f (X ∘ σ) = f X := by
    intro σ X
    rw [hf]
    simp only
    rw [ursell_comp_equiv P X σ]
    congr 1
    exact Equiv.prod_comp σ (fun k => ‖P.activity (X k)‖)
  have hidx : ∀ i : Fin (n + 1),
      ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
          (fun X => r ∈ skeleton H (X i).val), f X
      = ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
          (fun Y => r ∈ skeleton H (Y 0).val), f Y := by
    intro i
    refine Finset.sum_nbij' (i := fun X => X ∘ Equiv.swap 0 i)
      (j := fun Y => Y ∘ Equiv.swap 0 i) ?_ ?_ ?_ ?_ ?_
    · intro X hX
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show r ∈ skeleton H ((X ∘ Equiv.swap 0 i) 0).val
      have h0 : (X ∘ Equiv.swap 0 i) 0 = X i := by
        simp [Function.comp, Equiv.swap_apply_left]
      rw [h0]
      exact (Finset.mem_filter.mp hX).2
    · intro Y hY
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show r ∈ skeleton H ((Y ∘ Equiv.swap 0 i) i).val
      have h0 : (Y ∘ Equiv.swap 0 i) i = Y 0 := by
        simp [Function.comp, Equiv.swap_apply_right]
      rw [h0]
      exact (Finset.mem_filter.mp hY).2
    · intro X _
      funext k
      simp [Function.comp, Equiv.swap_apply_self]
    · intro Y _
      funext k
      simp [Function.comp, Equiv.swap_apply_self]
    · intro X _
      exact (hfswap _ X).symm
  have hmain : ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
        (fun X => IsCluster P X ∧ r ∈ skeleton H (clusterUnion H z X)), f X
      ≤ ((n : ℝ) + 1) *
        ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
          ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
            (fun Y => Y 0 = c), f Y := by
    calc ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
          (fun X => IsCluster P X ∧ r ∈ skeleton H (clusterUnion H z X)), f X
        ≤ ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
            (fun X => r ∈ skeleton H (clusterUnion H z X)), f X := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun X _ _ => hf0 X)
          intro X hX
          rw [mem_filter] at hX ⊢
          exact ⟨hX.1, hX.2.2⟩
      _ ≤ ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
            (fun X => r ∈ skeleton H (clusterUnion H z X)),
            ∑ i : Fin (n + 1), if r ∈ skeleton H (X i).val then f X else 0 := by
          refine Finset.sum_le_sum fun X hX => ?_
          obtain ⟨i₀, hi₀⟩ : ∃ i, r ∈ skeleton H (X i).val := by
            have hm := (Finset.mem_filter.mp hX).2
            rw [clusterUnion_skeleton H z X] at hm
            rw [mem_biUnion] at hm
            rcases hm with ⟨i, _, hi⟩
            exact ⟨i, hi⟩
          have hX0 : f X = if r ∈ skeleton H (X i₀).val then f X else 0 := by
            rw [if_pos hi₀]
          refine le_trans (le_of_eq hX0) ?_
          refine Finset.single_le_sum
            (f := fun i => if r ∈ skeleton H (X i).val then f X else 0)
            (fun i _ => ?_) (Finset.mem_univ i₀)
          show 0 ≤ if r ∈ skeleton H (X i).val then f X else 0
          split_ifs
          · exact hf0 X
          · exact le_rfl
      _ ≤ ∑ X : Fin (n + 1) → PolymerType H z,
            ∑ i : Fin (n + 1), if r ∈ skeleton H (X i).val then f X else 0 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun X _ _ => ?_)
          refine Finset.sum_nonneg fun i _ => ?_
          split_ifs
          · exact hf0 X
          · exact le_rfl
      _ = ∑ i : Fin (n + 1), ∑ X : Fin (n + 1) → PolymerType H z,
            if r ∈ skeleton H (X i).val then f X else 0 := Finset.sum_comm
      _ = ∑ i : Fin (n + 1),
            ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
              (fun X => r ∈ skeleton H (X i).val), f X := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (Finset.sum_filter _ _).symm
      _ = ∑ _i : Fin (n + 1),
            ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
              (fun Y => r ∈ skeleton H (Y 0).val), f Y :=
          Finset.sum_congr rfl fun i _ => hidx i
      _ = ((n : ℝ) + 1) *
            ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
              (fun Y => r ∈ skeleton H (Y 0).val), f Y := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ = ((n : ℝ) + 1) *
          ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
            ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
              (fun Y => Y 0 = c), f Y := by
          congr 1
          rw [← Finset.sum_fiberwise_of_maps_to (g := fun Y => Y 0) (fun Y hY => ?_) f]
          · refine Finset.sum_congr rfl fun c hc => ?_
            rw [Finset.filter_filter]
            refine Finset.sum_congr ?_ fun _ _ => rfl
            refine Finset.filter_congr fun Y _ => ?_
            constructor
            · exact fun h => h.2
            · intro h
              refine ⟨?_, h⟩
              show r ∈ skeleton H (Y 0).val
              rw [h]
              exact Finset.mem_filter.mp hc |>.2
          · rw [mem_filter] at hY
            refine Finset.mem_filter.mpr ⟨mem_univ _, hY.2⟩
  calc clusterSkeletonRemainderSumTerm H z r n
      = (((n + 1).factorial : ℝ))⁻¹ *
          ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
            (fun X => IsCluster P X ∧ r ∈ skeleton H (clusterUnion H z X)), f X := by
        rfl
    _ ≤ (((n + 1).factorial : ℝ))⁻¹ *
        (((n : ℝ) + 1) *
          ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
            ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
              (fun Y => Y 0 = c), f Y) := by
        exact mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ((n : ℝ) + 1) * ((((n + 1).factorial : ℝ))⁻¹ *
        ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
          ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
            (fun Y => Y 0 = c), f Y) := by ring
    _ = ((n : ℝ) + 1) *
        ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
          (((n + 1).factorial : ℝ))⁻¹ *
            ∑ Y ∈ (Finset.univ : Finset (Fin (n + 1) → PolymerType H z)).filter
              (fun Y => Y 0 = c), f Y := by
        rw [Finset.mul_sum]
    _ = ((n : ℝ) + 1) *
        ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
          pinnedClusterWeight P c n := rfl

/-- The same termwise bound after paying the factor `(n+1)` by an `e^t`
activity tilt.  This is the source-shaped skeleton-pinned analogue of the
off-region tail comparison in the KP restriction layer. -/
lemma clusterSkeletonRemainderSum_term_le_tilt {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (r : Cube d L) (t : ℝ) (ht : 0 < t) (n : ℕ) :
    clusterSkeletonRemainderSumTerm H z r n
      ≤ t⁻¹ * ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
        pinnedClusterWeight ((holePolymerSystem H z).scaleActivity (Real.exp t)) c n := by
  refine le_trans (clusterSkeletonRemainderSum_term_le_skeletonPinned H z r n) ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hfac : ((n : ℝ) + 1) ≤ t⁻¹ * Real.exp t ^ (n + 1) := by
    have h1 : t * ((n : ℝ) + 1) ≤ Real.exp (t * ((n : ℝ) + 1)) := by
      have h2 := Real.add_one_le_exp (t * ((n : ℝ) + 1))
      linarith
    have h3 : (Real.exp t : ℝ) ^ (n + 1)
        = Real.exp (t * ((n : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h3]
    exact (le_inv_mul_iff₀ ht).mpr h1
  calc ((n : ℝ) + 1) * pinnedClusterWeight (holePolymerSystem H z) c n
      ≤ (t⁻¹ * Real.exp t ^ (n + 1)) *
          pinnedClusterWeight (holePolymerSystem H z) c n := by
        refine mul_le_mul_of_nonneg_right hfac
          (pinnedClusterWeight_nonneg (holePolymerSystem H z) c n)
    _ = t⁻¹ * pinnedClusterWeight
          ((holePolymerSystem H z).scaleActivity (Real.exp t)) c n := by
        rw [pinnedClusterWeight_scale, abs_of_pos (Real.exp_pos t)]
        ring

/-- Skeleton-pinned cluster remainders are summable whenever the larger
union-pinned cluster remainders are summable.  The only set-theoretic input is
`skeleton_subset`: active-skeleton pinning is a genuine restriction of raw-union
pinning. -/
theorem clusterSkeletonRemainderSum_summable {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (r : Cube d L) (t : ℝ) (ht : 0 < t)
    (hkp : KPCriterion ((holePolymerSystem H z).scaleActivity (Real.exp t))
      (fun X => (X.val.card : ℝ))) :
    Summable (fun n => clusterSkeletonRemainderSumTerm H z r n) := by
  have hnn : ∀ n, 0 ≤ clusterSkeletonRemainderSumTerm H z r n := by
    intro n
    unfold clusterSkeletonRemainderSumTerm
    positivity
  exact Summable.of_nonneg_of_le hnn (clusterSkeletonRemainderSumTerm_le H z r)
    (clusterRemainderSum_summable H z r t ht hkp)

/-- Quantitative skeleton-pinned cluster remainder bound.  After the `e^t`
tilt pays the order factor, the total skeleton-pinned remainder is bounded by a
finite pinned KP sum over polymers whose active skeleton contains the root.

This is still only a KP/summability substrate: the model-specific
Balaban-Dimock activity-decay estimate is not proved here. -/
theorem clusterSkeletonRemainderSum_tsum_le {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (r : Cube d L) (t : ℝ) (ht : 0 < t)
    (hkp : KPCriterion ((holePolymerSystem H z).scaleActivity (Real.exp t))
      (fun X => (X.val.card : ℝ))) :
    ∑' n, clusterSkeletonRemainderSumTerm H z r n
      ≤ t⁻¹ * ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
        Real.exp t * ‖(holePolymerSystem H z).activity c‖ *
          Real.exp ((c.val.card : ℝ)) := by
  have hle : ∀ n, clusterSkeletonRemainderSumTerm H z r n
      ≤ t⁻¹ * ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
        pinnedClusterWeight ((holePolymerSystem H z).scaleActivity (Real.exp t)) c n := by
    intro n
    exact clusterSkeletonRemainderSum_term_le_tilt H z r t ht n
  have hgsum : Summable (fun n => t⁻¹ * ∑ c ∈ Finset.univ.filter
      (fun c => r ∈ skeleton H (c : PolymerType H z).val),
      pinnedClusterWeight ((holePolymerSystem H z).scaleActivity (Real.exp t)) c n) := by
    refine Summable.mul_left _ ?_
    exact summable_sum fun c _ =>
      (pinned_cluster_summable_sharp _ hkp c).1
  have hskel : Summable (fun n => clusterSkeletonRemainderSumTerm H z r n) :=
    clusterSkeletonRemainderSum_summable H z r t ht hkp
  refine le_trans (hskel.tsum_le_tsum hle hgsum) ?_
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ht.le)
  have hswap := Summable.tsum_finsetSum
    (s := Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val))
    (f := fun c n =>
      pinnedClusterWeight ((holePolymerSystem H z).scaleActivity (Real.exp t)) c n)
    (fun c _ => (pinned_cluster_summable_sharp _ hkp c).1)
  refine le_trans (le_of_eq hswap) ?_
  refine Finset.sum_le_sum fun c _ => ?_
  refine le_trans (pinned_cluster_summable_sharp _ hkp c).2 (le_of_eq ?_)
  show ‖((Real.exp t : ℝ) : ℂ) * (holePolymerSystem H z).activity c‖ *
      Real.exp ((c.val.card : ℝ))
    = Real.exp t * ‖(holePolymerSystem H z).activity c‖ *
      Real.exp ((c.val.card : ℝ))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]

/-- Source-shaped skeleton cluster remainder bound from a modified-metric
activity estimate.

This is the consumer side of the Balaban-Dimock activity-decay input: if the
tilted, cardinality-weighted polymer activity is bounded by
`A * q^(d_M + 1)`, then the full skeleton-rooted cluster remainder is bounded by
the already-proved modified-metric summability constant.  The activity-decay
estimate itself is still an explicit hypothesis, not proved here. -/
theorem clusterSkeletonRemainderSum_tsum_le_metric_bound {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (r : Cube d L) (t q A : ℝ) (ht : 0 < t)
    (hkp : KPCriterion ((holePolymerSystem H z).scaleActivity (Real.exp t))
      (fun X => (X.val.card : ℝ)))
    (hA0 : 0 ≤ A)
    (hact : ∀ c : PolymerType H z,
      Real.exp t * ‖(holePolymerSystem H z).activity c‖ *
          Real.exp ((c.val.card : ℝ))
        ≤ A * q ^ (discreteModifiedMetric H c.val + 1))
    (hdisj : ∀ H₁ ∈ H.holes, ∀ H₂ ∈ H.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) H.holes)
    (hholes_ne : ∀ H₀ ∈ H.holes, H₀.Nonempty)
    (hq0 : 0 ≤ q)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)) < 1) :
    ∑' n, clusterSkeletonRemainderSumTerm H z r n
      ≤ t⁻¹ * (A *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹) := by
  classical
  let K := (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹
  have hbase := clusterSkeletonRemainderSum_tsum_le H z r t ht hkp
  refine hbase.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ht.le)
  have hfinite : ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
        Real.exp t * ‖(holePolymerSystem H z).activity c‖ *
          Real.exp ((c.val.card : ℝ))
      ≤ A * K := by
    have hterm : ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
        Real.exp t * ‖(holePolymerSystem H z).activity c‖ *
          Real.exp ((c.val.card : ℝ))
      ≤ ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
          A * q ^ (discreteModifiedMetric H c.val + 1) := by
      exact Finset.sum_le_sum fun c _ => hact c
    have hfilter_eq :
        ∑ c ∈ Finset.univ.filter (fun c : PolymerType H z => r ∈ skeleton H c.val),
          q ^ (discreteModifiedMetric H c.val + 1)
        =
        ∑ c : {c : PolymerType H z // r ∈ skeleton H c.val},
          q ^ (discreteModifiedMetric H c.val.val + 1) := by
      exact (Finset.sum_subtype
        ((Finset.univ : Finset (PolymerType H z)).filter
          (fun c => r ∈ skeleton H c.val))
        (fun c => by simp)
        (fun c => q ^ (discreteModifiedMetric H c.val + 1)))
    let f1 := fun c : {c : PolymerType H z // r ∈ skeleton H c.val} =>
      (⟨c.val.val, ⟨c.property, c.val.property.right.left, c.val.property.right.right⟩⟩ :
        {X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X})
    have hf1_inj : Function.Injective f1 := by
      intro a b h
      have h_eq : a.val.val = b.val.val := congrArg (fun x => x.val) h
      have h_val_eq : a.val = b.val := Subtype.ext h_eq
      exact Subtype.ext h_val_eq
    have hf1_surj : Function.Surjective f1 := by
      intro b
      refine ⟨⟨⟨b.val, ⟨?_, b.property.right.left, b.property.right.right⟩⟩,
        b.property.left⟩, rfl⟩
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have hr : r ∈ skeleton H b.val := b.property.left
      have hr_sub := skeleton_subset H b.val hr
      rw [he] at hr_sub
      cases hr_sub
    have hsum_eq :
        ∑ c : {c : PolymerType H z // r ∈ skeleton H c.val},
          q ^ (discreteModifiedMetric H c.val.val + 1)
        =
        ∑ X : {X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X},
          q ^ (discreteModifiedMetric H X.val + 1) := by
      refine Fintype.sum_equiv (Equiv.ofBijective f1 ⟨hf1_inj, hf1_surj⟩) _ _ ?_
      intro c
      rfl
    have hmetric :
        ∑ c ∈ Finset.univ.filter (fun c : PolymerType H z => r ∈ skeleton H c.val),
          q ^ (discreteModifiedMetric H c.val + 1)
        ≤ K := by
      rw [hfilter_eq, hsum_eq]
      simpa [K] using
        discreteModifiedMetric_weight_summable H r q hdisj hnoedges hholes_ne hq0 hCq
    calc ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
          Real.exp t * ‖(holePolymerSystem H z).activity c‖ *
            Real.exp ((c.val.card : ℝ))
        ≤ ∑ c ∈ Finset.univ.filter (fun c => r ∈ skeleton H (c : PolymerType H z).val),
            A * q ^ (discreteModifiedMetric H c.val + 1) := hterm
      _ = A * ∑ c ∈ Finset.univ.filter (fun c : PolymerType H z => r ∈ skeleton H c.val),
            q ^ (discreteModifiedMetric H c.val + 1) := by
          rw [Finset.mul_sum]
      _ ≤ A * K := mul_le_mul_of_nonneg_left hmetric hA0
  exact hfinite

/-- One-shot source-shaped skeleton remainder bound from local tilted
summability plus modified-metric activity decay.

Compared with `clusterSkeletonRemainderSum_tsum_le_metric_bound`, this theorem
does not carry the tilted KP criterion as a separate hypothesis: it derives it
from the volume-uniform local summability criterion for the scaled activity. -/
theorem clusterSkeletonRemainderSum_tsum_le_metric_bound_of_local {d L : ℕ}
    [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (r : Cube d L) (t q A : ℝ) (ht : 0 < t)
    (hlocal : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        Real.exp t * ‖(holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹)
    (hA0 : 0 ≤ A)
    (hact : ∀ c : PolymerType H z,
      Real.exp t * ‖(holePolymerSystem H z).activity c‖ *
          Real.exp ((c.val.card : ℝ))
        ≤ A * q ^ (discreteModifiedMetric H c.val + 1))
    (hdisj : ∀ H₁ ∈ H.holes, ∀ H₂ ∈ H.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) H.holes)
    (hholes_ne : ∀ H₀ ∈ H.holes, H₀.Nonempty)
    (hq0 : 0 ≤ q)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)) < 1) :
    ∑' n, clusterSkeletonRemainderSumTerm H z r n
      ≤ t⁻¹ * (A *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹) := by
  have hlocal_scaled : ∀ s : Cube d L,
      ∑ Y ∈ Finset.univ.filter (fun Y : PolymerType H z => s ∈ Y.val),
        ‖((Real.exp t : ℝ) : ℂ) * (holePolymerSystem H z).activity Y‖ *
          Real.exp (Y.val.card : ℝ) ≤ ((3 ^ d + 1 : ℕ) : ℝ)⁻¹ := by
    intro s
    refine (le_of_eq ?_).trans (hlocal s)
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos t)]
  exact clusterSkeletonRemainderSum_tsum_le_metric_bound H z r t q A ht
    (holePolymerSystem_KPCriterion_volumeUniform_scaled H z (Real.exp t)
      hlocal_scaled)
    hA0 hact hdisj hnoedges hholes_ne hq0 hCq

lemma polymer_subset_clusterUnion {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    {n : ℕ} (X : Fin n → (holePolymerSystem H z).Polymer) (i : Fin n) :
    (X i).val ⊆ clusterUnion H z X := by
  dsimp [clusterUnion]
  intro x hx
  rw [mem_biUnion]
  refine ⟨i, mem_univ i, hx⟩

/-- The only currently justified comparison between a constituent polymer metric
and the cluster-union metric is the single-polymer case.  For genuine
multi-polymer clusters, subset inclusion is not enough: the modified metric is
not an abstract monotone function of the ambient set because its Steiner
minimization is constrained to lie inside that ambient set. -/
lemma discreteModifiedMetric_le_clusterModifiedMetric {d L : ℕ} [NeZero L] (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ)
    (X : Fin 1 → (holePolymerSystem H z).Polymer) (i : Fin 1) :
    discreteModifiedMetric H (X i).val ≤ clusterModifiedMetric H z X := by
  dsimp [clusterModifiedMetric]
  rw [clusterUnion_fin_one]
  have : i = 0 := Subsingleton.elim i 0
  rw [this]

end YangMills.RG


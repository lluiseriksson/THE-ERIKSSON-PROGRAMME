/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Ursell
import YangMills.KP.Cluster

/-!
# Mayer–Ursell inversion, step 0 — the indicator identity

Opening bricks of B0a (`docs/CLUSTER-CORRELATION-PLAN.md` §2c): the
alternating sum over ALL spanning subgraphs of the incompatibility graph
is the compatibility indicator,

  `∑_{E ⊆ edges(G_X)} (−1)^{|E|} = 𝟙[X pairwise compatible]`,

via `Finset.sum_powerset_neg_one_pow_card`.  The forthcoming core of
B0a refines this by grouping `E` by its component partition, producing
`∑_π ∏_B ursell` on the left — the partition identity that drives
`Ξ = exp(clusterSum)`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

variable (P : PolymerSystem)

/-- A tuple is **pairwise compatible** when no two coordinates (equal or
not) carry incompatible polymers — the tuple-level admissibility that the
Mayer product detects.  (Repetitions die through `incomp_self`.) -/
def PairwiseCompatible {n : ℕ} (X : Fin n → P.Polymer) : Prop :=
  ∀ i j : Fin n, i ≠ j → ¬ P.incomp (X i) (X j)

open Classical in
/-- The incompatibility graph has no edges iff the tuple is pairwise
compatible. -/
lemma edgeFinset_eq_empty_iff {n : ℕ} (X : Fin n → P.Polymer) :
    (incompGraph P X).edgeFinset = ∅ ↔ PairwiseCompatible P X := by
  constructor
  · intro h i j hne hinc
    have hadj : (incompGraph P X).Adj i j :=
      (incompGraph_adj P X i j).mpr ⟨hne, hinc⟩
    have : s(i, j) ∈ (incompGraph P X).edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr hadj
    rw [h] at this
    exact absurd this (Finset.notMem_empty _)
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    induction e with
    | h i j =>
        have hadj := SimpleGraph.mem_edgeFinset.mp he
        have := (incompGraph_adj P X i j).mp hadj
        exact h i j this.1 this.2

open Classical in
/-- **The indicator identity (B0a, step 0):** the alternating sum over
all spanning subgraphs of the incompatibility graph is the pairwise-
compatibility indicator. -/
theorem sum_neg_one_pow_eq_indicator {n : ℕ} (X : Fin n → P.Polymer) :
    ∑ E ∈ (incompGraph P X).edgeFinset.powerset, (-1 : ℤ) ^ E.card
    = if PairwiseCompatible P X then 1 else 0 := by
  rw [Finset.sum_powerset_neg_one_pow_card]
  by_cases h : PairwiseCompatible P X
  · rw [if_pos ((edgeFinset_eq_empty_iff P X).mpr h), if_pos h]
  · rw [if_neg fun he => h ((edgeFinset_eq_empty_iff P X).mp he),
      if_neg h]

open Classical in
/-- **Ursell coefficients are relabeling-invariant (B0a, step 1):**
precomposing the tuple with a permutation does not change the Ursell
coefficient — the incompatibility graphs are isomorphic, and connected
spanning edge sets transport along `Sym2.map`. -/
theorem ursell_comp_equiv {n : ℕ} (X : Fin n → P.Polymer)
    (σ : Equiv.Perm (Fin n)) :
    ursell P (X ∘ σ) = ursell P X := by
  classical
  have hmapinj : Function.Injective (Sym2.map σ) :=
    Sym2.map.injective σ.injective
  -- adjacency transport between the two incompatibility graphs
  have hedge : ∀ i j : Fin n, (incompGraph P (X ∘ σ)).Adj i j
      ↔ (incompGraph P X).Adj (σ i) (σ j) := by
    intro i j
    rw [incompGraph_adj, incompGraph_adj]
    constructor
    · rintro ⟨hne, hinc⟩
      exact ⟨fun h => hne (σ.injective h), hinc⟩
    · rintro ⟨hne, hinc⟩
      exact ⟨fun h => hne (by rw [h]), hinc⟩
  -- adjacency transport for relabeled spanning edge sets
  have hadj : ∀ (E : Finset (Sym2 (Fin n))) (i j : Fin n),
      (SimpleGraph.fromEdgeSet
        (↑(E.image (Sym2.map σ)) : Set (Sym2 (Fin n)))).Adj (σ i) (σ j)
      ↔ (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Adj i j := by
    intro E i j
    rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨hmem, hne⟩
      refine ⟨?_, fun h => hne (by rw [h])⟩
      rw [Finset.mem_coe, Finset.mem_image] at hmem
      obtain ⟨e', he', heq⟩ := hmem
      have he : e' = s(i, j) := hmapinj (by rw [heq, Sym2.map_mk])
      rwa [he] at he'
    · rintro ⟨hmem, hne⟩
      refine ⟨?_, fun h => hne (σ.injective h)⟩
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨s(i, j), hmem, rfl⟩
  -- connectivity transport
  have hconn : ∀ E : Finset (Sym2 (Fin n)),
      (SimpleGraph.fromEdgeSet
        (↑(E.image (Sym2.map σ)) : Set (Sym2 (Fin n)))).Connected
      ↔ (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Connected := by
    intro E
    have iso : SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))
        ≃g SimpleGraph.fromEdgeSet
          (↑(E.image (Sym2.map σ)) : Set (Sym2 (Fin n))) :=
      { toEquiv := σ
        map_rel_iff' := by intro i j; exact hadj E i j }
    exact iso.connected_iff.symm
  unfold ursell
  refine Finset.sum_nbij' (fun E => E.image (Sym2.map σ))
    (fun E => E.image (Sym2.map σ.symm)) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro E hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE ⊢
    refine ⟨?_, (hconn E).mpr hE.2⟩
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨e', he', rfl⟩ := he
    have hmem := hE.1 he'
    revert hmem
    refine Sym2.ind (fun i j => ?_) e'
    intro hmem
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem
    rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (hedge i j).mp hmem
  · -- backward membership
    intro E hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE ⊢
    constructor
    · intro e he
      rw [Finset.mem_image] at he
      obtain ⟨e', he', rfl⟩ := he
      have hmem := hE.1 he'
      revert hmem
      refine Sym2.ind (fun i j => ?_) e'
      intro hmem
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem
      rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      have := (hedge (σ.symm i) (σ.symm j)).mpr
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact this hmem
    · -- connectivity of the σ.symm-image, from hconn applied backwards
      have hEimg : (E.image (Sym2.map σ.symm)).image (Sym2.map σ) = E := by
        rw [Finset.image_image, ← Sym2.map_comp, Equiv.self_comp_symm,
          Sym2.map_id, Finset.image_id]
      have := (hconn (E.image (Sym2.map σ.symm)))
      rw [hEimg] at this
      exact this.mp hE.2
  · -- left inverse
    intro E _
    dsimp only
    rw [Finset.image_image, ← Sym2.map_comp, Equiv.symm_comp_self,
      Sym2.map_id, Finset.image_id]
  · -- right inverse
    intro E _
    dsimp only
    rw [Finset.image_image, ← Sym2.map_comp, Equiv.self_comp_symm,
      Sym2.map_id, Finset.image_id]
  · -- values
    intro E _
    dsimp only
    rw [Finset.card_image_of_injective E hmapinj]

open Classical in
/-- **Walk pullback along an embedding (B0a, step 2a):** a walk in the
image edge set between image vertices pulls back to reachability in the
source — every edge of the image set joins image vertices, so the walk
never leaves the range. -/
lemma reachable_of_walk_image {m n : ℕ} (f : Fin m ↪ Fin n)
    (E : Finset (Sym2 (Fin m))) :
    ∀ {v w : Fin n}, (SimpleGraph.fromEdgeSet
      (↑(E.image (Sym2.map f)) : Set (Sym2 (Fin n)))).Walk v w →
    ∀ i j : Fin m, f i = v → f j = w →
    (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin m)))).Reachable i j := by
  intro v w p
  induction p with
  | nil =>
      intro i j hi hj
      have hij : i = j := f.injective (hi.trans hj.symm)
      rw [hij]
  | @cons v u w h q ih =>
      intro i j hi hj
      rw [SimpleGraph.fromEdgeSet_adj] at h
      obtain ⟨hmem, hne⟩ := h
      rw [Finset.mem_coe, Finset.mem_image] at hmem
      obtain ⟨e₀, he₀, heq⟩ := hmem
      revert he₀ heq
      refine Sym2.ind (fun a b => ?_) e₀
      intro he₀ heq
      rw [Sym2.map_mk, Sym2.eq_iff] at heq
      rcases heq with ⟨hav, hbu⟩ | ⟨hau, hbv⟩
      · have hia : i = a := f.injective (hi.trans hav.symm)
        have hadj : (SimpleGraph.fromEdgeSet
            (↑E : Set (Sym2 (Fin m)))).Adj a b := by
          rw [SimpleGraph.fromEdgeSet_adj]
          exact ⟨he₀, fun hab => hne (by rw [← hav, ← hbu, hab])⟩
        rw [hia]
        exact hadj.reachable.trans (ih b j hbu hj)
      · have hib : i = b := f.injective (hi.trans hbv.symm)
        have hadj : (SimpleGraph.fromEdgeSet
            (↑E : Set (Sym2 (Fin m)))).Adj b a := by
          rw [SimpleGraph.fromEdgeSet_adj]
          refine ⟨?_, fun hba => hne (by rw [← hbv, ← hau, hba])⟩
          rwa [Sym2.eq_swap]
        rw [hib]
        exact hadj.reachable.trans (ih a j hau hj)

open Classical in
/-- **Reachability transport along an embedding (B0a, step 2b):**
image vertices are reachable through the image edge set iff the sources
are reachable through the source edge set. -/
lemma reachable_image_iff {m n : ℕ} (f : Fin m ↪ Fin n)
    (E : Finset (Sym2 (Fin m))) (i j : Fin m) :
    (SimpleGraph.fromEdgeSet
      (↑(E.image (Sym2.map f)) : Set (Sym2 (Fin n)))).Reachable (f i) (f j)
    ↔ (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin m)))).Reachable i j := by
  constructor
  · rintro ⟨p⟩
    exact reachable_of_walk_image f E p i j rfl rfl
  · intro h
    have hmaprel : ∀ {a b : Fin m},
        (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin m)))).Adj a b →
        (SimpleGraph.fromEdgeSet
          (↑(E.image (Sym2.map f)) : Set (Sym2 (Fin n)))).Adj (f a) (f b) := by
      intro a b hab
      rw [SimpleGraph.fromEdgeSet_adj] at hab ⊢
      refine ⟨?_, fun hf => hab.2 (f.injective hf)⟩
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨s(a, b), hab.1, rfl⟩
    exact h.map ⟨⇑f, hmaprel⟩

set_option maxHeartbeats 800000 in
open Classical in
/-- **The per-block identification (B0a, step 3):** the alternating sum
over edge sets supported inside a block `B` that connect all of `B` is
exactly the Ursell coefficient of the block-restricted tuple.  This is
the fiber value of the forthcoming component-partition fibration. -/
theorem sum_blockConnected_eq_ursell {n : ℕ} (X : Fin n → P.Polymer)
    (B : Finset (Fin n)) {m : ℕ} (hm : B.card = m) (hB : B.Nonempty) :
    ∑ E ∈ (incompGraph P X).edgeFinset.powerset.filter
      (fun E : Finset (Sym2 (Fin n)) => (∀ e ∈ E, ∀ v ∈ e, v ∈ B) ∧
        ∀ v ∈ B, ∀ w ∈ B, (SimpleGraph.fromEdgeSet
          (↑E : Set (Sym2 (Fin n)))).Reachable v w),
      (-1 : ℤ) ^ E.card
    = ursell P (fun i : Fin m => X ((B.orderIsoOfFin hm i) : Fin n)) := by
  classical
  let femb : Fin m ↪ Fin n :=
    ⟨fun i => ((B.orderIsoOfFin hm i) : Fin n),
      fun i j hij => (B.orderIsoOfFin hm).injective
        (Subtype.val_injective hij)⟩
  have hmem : ∀ i : Fin m, femb i ∈ B := fun i => (B.orderIsoOfFin hm i).2
  have hsurj : ∀ v ∈ B, ∃ i : Fin m, femb i = v := by
    intro v hv
    refine ⟨(B.orderIsoOfFin hm).symm ⟨v, hv⟩, ?_⟩
    show ((B.orderIsoOfFin hm ((B.orderIsoOfFin hm).symm ⟨v, hv⟩)) : Fin n) = v
    rw [OrderIso.apply_symm_apply]
  have hmapinj : Function.Injective (Sym2.map femb) :=
    Sym2.map.injective femb.injective
  have hedge : ∀ a b : Fin m,
      (incompGraph P (fun i : Fin m =>
        X ((B.orderIsoOfFin hm i) : Fin n))).Adj a b
      ↔ (incompGraph P X).Adj (femb a) (femb b) := by
    intro a b
    rw [incompGraph_adj, incompGraph_adj]
    constructor
    · rintro ⟨hne, hinc⟩
      exact ⟨fun h => hne (femb.injective h), hinc⟩
    · rintro ⟨hne, hinc⟩
      exact ⟨fun h => hne (by rw [h]), hinc⟩
  -- the retraction: within-B edge sets are images of their preimages
  have hretract : ∀ E : Finset (Sym2 (Fin n)),
      (∀ e ∈ E, ∀ v ∈ e, v ∈ B) →
      ((Finset.univ : Finset (Sym2 (Fin m))).filter
        (fun e' => Sym2.map femb e' ∈ E)).image (Sym2.map femb) = E := by
    intro E hwithin
    ext e
    rw [Finset.mem_image]
    constructor
    · rintro ⟨e', he', rfl⟩
      exact (Finset.mem_filter.mp he').2
    · intro he
      have hv : ∀ u ∈ e, u ∈ B := hwithin e he
      revert he hv
      refine Sym2.ind (fun v w => ?_) e
      intro he hv
      obtain ⟨a, ha⟩ := hsurj v (hv v (Sym2.mem_iff.mpr (Or.inl rfl)))
      obtain ⟨b, hb⟩ := hsurj w (hv w (Sym2.mem_iff.mpr (Or.inr rfl)))
      refine ⟨s(a, b), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [Sym2.map_mk, ha, hb]; exact he
      · rw [Sym2.map_mk, ha, hb]
  unfold ursell
  refine Eq.symm (Finset.sum_nbij'
    (fun E' : Finset (Sym2 (Fin m)) => E'.image (Sym2.map femb))
    (fun E : Finset (Sym2 (Fin n)) =>
      (Finset.univ : Finset (Sym2 (Fin m))).filter
        (fun e' => Sym2.map femb e' ∈ E)) ?_ ?_ ?_ ?_ ?_)
  · -- forward membership
    intro E' hE'
    rw [Finset.mem_filter, Finset.mem_powerset] at hE'
    obtain ⟨hsub, hconn⟩ := hE'
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rw [Finset.mem_image] at he
      obtain ⟨e', he', rfl⟩ := he
      have hmem' := hsub he'
      revert hmem'
      refine Sym2.ind (fun a b => ?_) e'
      intro hmem'
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem'
      rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact (hedge a b).mp hmem'
    · intro e he
      rw [Finset.mem_image] at he
      obtain ⟨e', _, rfl⟩ := he
      refine Sym2.ind (fun a b => ?_) e'
      intro v hv
      rw [Sym2.map_mk, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact hmem a
      · exact hmem b
    · intro v hv w hw
      obtain ⟨i, rfl⟩ := hsurj v hv
      obtain ⟨j, rfl⟩ := hsurj w hw
      exact (reachable_image_iff femb E' i j).mpr
        (hconn.preconnected i j)
  · -- backward membership
    intro E hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE
    obtain ⟨hsub, hwithin, hreach⟩ := hE
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro e' he'
      have hmemE := (Finset.mem_filter.mp he').2
      revert hmemE
      refine Sym2.ind (fun a b => ?_) e'
      intro hmemE
      rw [Sym2.map_mk] at hmemE
      have := hsub hmemE
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (hedge a b).mpr this
    · rw [SimpleGraph.connected_iff]
      have hm0 : 0 < m := by
        rw [← hm]; exact Finset.card_pos.mpr hB
      refine ⟨?_, ⟨⟨0, hm0⟩⟩⟩
      intro i j
      have h1 := hreach (femb i) (hmem i) (femb j) (hmem j)
      rw [← hretract E hwithin] at h1
      exact (reachable_image_iff femb _ i j).mp h1
  · -- left inverse
    intro E' _
    dsimp only
    ext e''
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩
      rw [Finset.mem_image] at h
      obtain ⟨e₀, he₀, heq⟩ := h
      rwa [← hmapinj heq]
    · intro h
      exact ⟨Finset.mem_univ _,
        Finset.mem_image.mpr ⟨e'', h, rfl⟩⟩
  · -- right inverse
    intro E hE
    dsimp only
    exact hretract E ((Finset.mem_filter.mp hE).2).1
  · -- values
    intro E' _
    dsimp only
    rw [Finset.card_image_of_injective E' hmapinj]

open Classical in
/-- **Walk restriction into an adjacency-closed set (B0a, step 4a):**
reachability from a vertex of an adjacency-closed set is realized by
edges inside the set — walks never leave it. -/
lemma reachable_filter_of_closed {n : ℕ} (E : Finset (Sym2 (Fin n)))
    (B : Finset (Fin n))
    (hcl : ∀ a b : Fin n, s(a, b) ∈ E → a ∈ B → b ∈ B) :
    ∀ {v w : Fin n},
    (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Walk v w →
    v ∈ B →
    (SimpleGraph.fromEdgeSet
      (↑(E.filter (fun e => ∀ u ∈ e, u ∈ B)) :
        Set (Sym2 (Fin n)))).Reachable v w := by
  intro v w p
  induction p with
  | nil => intro _; exact SimpleGraph.Reachable.refl _
  | @cons v u w h q ih =>
      intro hv
      rw [SimpleGraph.fromEdgeSet_adj] at h
      obtain ⟨hmem, hne⟩ := h
      rw [Finset.mem_coe] at hmem
      have hu : u ∈ B := hcl v u hmem hv
      have hadj : (SimpleGraph.fromEdgeSet
          (↑(E.filter (fun e => ∀ x ∈ e, x ∈ B)) :
            Set (Sym2 (Fin n)))).Adj v u := by
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨?_, hne⟩
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨hmem, fun x hx => ?_⟩
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact hv
        · exact hu
      exact hadj.reachable.trans (ih hu)

open Classical in
/-- **The component partition (B0a, step 4a):** the partition of the
vertex set into reachability classes of a spanning edge set. -/
noncomputable def componentPartition {n : ℕ}
    (E : Finset (Sym2 (Fin n))) :
    Finpartition (Finset.univ : Finset (Fin n)) :=
  letI : DecidableRel (SimpleGraph.fromEdgeSet
      (↑E : Set (Sym2 (Fin n)))).reachableSetoid.r :=
    Classical.decRel _
  Finpartition.ofSetoid (SimpleGraph.fromEdgeSet
    (↑E : Set (Sym2 (Fin n)))).reachableSetoid

open Classical in
lemma mem_componentPartition_part_iff {n : ℕ}
    (E : Finset (Sym2 (Fin n))) (a b : Fin n) :
    b ∈ (componentPartition E).part a
    ↔ (SimpleGraph.fromEdgeSet
        (↑E : Set (Sym2 (Fin n)))).Reachable a b := by
  unfold componentPartition
  exact Finpartition.mem_part_ofSetoid_iff_rel

open Classical in
/-- Parts of the component partition are adjacency-closed. -/
lemma componentPartition_part_closed {n : ℕ}
    (E : Finset (Sym2 (Fin n))) (c : Fin n) :
    ∀ a b : Fin n, s(a, b) ∈ E →
    a ∈ (componentPartition E).part c →
    b ∈ (componentPartition E).part c := by
  intro a b hab ha
  rw [mem_componentPartition_part_iff] at ha ⊢
  refine ha.trans ?_
  have hadj : (SimpleGraph.fromEdgeSet
      (↑E : Set (Sym2 (Fin n)))).Adj a b ∨ a = b := by
    by_cases hne : a = b
    · exact Or.inr hne
    · refine Or.inl ?_
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨hab, hne⟩
  rcases hadj with h | rfl
  · exact h.reachable
  · exact SimpleGraph.Reachable.refl _

open Classical in
/-- Vertices joined by an edge of the set lie in the same part. -/
lemma componentPartition_edge_same_part {n : ℕ}
    (E : Finset (Sym2 (Fin n))) {a b : Fin n} (hab : s(a, b) ∈ E) :
    b ∈ (componentPartition E).part a := by
  exact componentPartition_part_closed E a a b hab
    ((componentPartition E).mem_part (Finset.mem_univ a))

end YangMills.KP

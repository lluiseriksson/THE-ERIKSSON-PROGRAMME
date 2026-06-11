/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Ursell
import YangMills.KP.Cluster
import YangMills.KP.SharpShell

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

open Classical in
/-- **A1: fiber components are block data.**  If the component partition
of `E` is `π`, the within-`B` part of `E` is a within-`B`,
`B`-connecting edge set, for every part `B`. -/
lemma filter_within_mem_of_cp_eq {n : ℕ} {A : Finset (Sym2 (Fin n))}
    {E : Finset (Sym2 (Fin n))} (hE : E ∈ A.powerset)
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hcp : componentPartition E = π) {B : Finset (Fin n)}
    (hB : B ∈ π.parts) :
    E.filter (fun e => ∀ u ∈ e, u ∈ B) ∈ A.powerset.filter
      (fun E' : Finset (Sym2 (Fin n)) =>
        (∀ e ∈ E', ∀ v ∈ e, v ∈ B) ∧
        ∀ v ∈ B, ∀ w ∈ B, (SimpleGraph.fromEdgeSet
          (↑E' : Set (Sym2 (Fin n)))).Reachable v w) := by
  subst hcp
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨subset_trans (Finset.filter_subset _ _)
    (Finset.mem_powerset.mp hE), ?_, ?_⟩
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro v hv w hw
    have hBv : (componentPartition E).part v = B :=
      (componentPartition E).part_eq_of_mem hB hv
    have hreach : (SimpleGraph.fromEdgeSet
        (↑E : Set (Sym2 (Fin n)))).Reachable v w := by
      rw [← mem_componentPartition_part_iff, hBv]
      exact hw
    have hcl : ∀ a b : Fin n, s(a, b) ∈ E → a ∈ B → b ∈ B := by
      intro a b hab ha
      rw [← hBv] at ha ⊢
      exact componentPartition_part_closed E v a b hab ha
    obtain ⟨p⟩ := hreach
    exact reachable_filter_of_closed E B hcl p hv

open Classical in
/-- **A2: the edge decomposition.**  An edge set is the union of its
within-part components. -/
lemma biUnion_filter_within_parts {n : ℕ} {E : Finset (Sym2 (Fin n))}
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hcp : componentPartition E = π) :
    π.parts.biUnion (fun B => E.filter (fun e => ∀ u ∈ e, u ∈ B))
      = E := by
  subst hcp
  ext e
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨B, _, he⟩
    exact (Finset.mem_filter.mp he).1
  · intro he
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    refine ⟨(componentPartition E).part a,
      ((componentPartition E).part_mem).mpr (Finset.mem_univ a),
      Finset.mem_filter.mpr ⟨he, fun u hu => ?_⟩⟩
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact (componentPartition E).mem_part (Finset.mem_univ u)
    · exact componentPartition_edge_same_part E he

open Classical in
/-- Within-part edge sets of disjoint parts are disjoint. -/
lemma filter_within_disjoint {n : ℕ} (E : Finset (Sym2 (Fin n)))
    {B B' : Finset (Fin n)} (hd : Disjoint B B') :
    Disjoint (E.filter (fun e => ∀ u ∈ e, u ∈ B))
      (E.filter (fun e => ∀ u ∈ e, u ∈ B')) := by
  rw [Finset.disjoint_left]
  intro e he he'
  have hw1 := (Finset.mem_filter.mp he).2
  have hw2 := (Finset.mem_filter.mp he').2
  obtain ⟨u, hu⟩ : ∃ u, u ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
  exact (Finset.disjoint_left.mp hd (hw1 u hu)) (hw2 u hu)

open Classical in
/-- Endpoints of walks from an adjacency-closed set stay in the set. -/
lemma mem_of_reachable_closed {n : ℕ} {E : Finset (Sym2 (Fin n))}
    {B : Finset (Fin n)}
    (hcl : ∀ a b : Fin n, s(a, b) ∈ E → a ∈ B → b ∈ B) :
    ∀ {v w : Fin n},
    (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Walk v w →
    v ∈ B → w ∈ B := by
  intro v w p
  induction p with
  | nil => exact id
  | @cons v u w h q ih =>
      intro hv
      rw [SimpleGraph.fromEdgeSet_adj] at h
      exact ih (hcl v u (Finset.mem_coe.mp h.1) hv)

open Classical in
/-- **A3: the reconstruction.**  The union of per-part within-part,
part-connecting edge sets has component partition exactly `π`. -/
lemma componentPartition_biUnion_eq {n : ℕ}
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    (g : Finset (Fin n) → Finset (Sym2 (Fin n)))
    (hwithin : ∀ B ∈ π.parts, ∀ e ∈ g B, ∀ u ∈ e, u ∈ B)
    (hconn : ∀ B ∈ π.parts, ∀ v ∈ B, ∀ w ∈ B,
      (SimpleGraph.fromEdgeSet
        (↑(g B) : Set (Sym2 (Fin n)))).Reachable v w) :
    componentPartition (π.parts.biUnion g) = π := by
  classical
  have hcl : ∀ C ∈ π.parts,
      ∀ a b : Fin n, s(a, b) ∈ π.parts.biUnion g → a ∈ C → b ∈ C := by
    intro C hC a b hab ha
    rw [Finset.mem_biUnion] at hab
    obtain ⟨B', hB', habg⟩ := hab
    have haB' : a ∈ B' :=
      hwithin B' hB' _ habg a (Sym2.mem_iff.mpr (Or.inl rfl))
    have hbB' : b ∈ B' :=
      hwithin B' hB' _ habg b (Sym2.mem_iff.mpr (Or.inr rfl))
    have hBC : B' = C := by
      by_contra hne
      exact (Finset.disjoint_left.mp
        (π.disjoint (Finset.mem_coe.mpr hB')
          (Finset.mem_coe.mpr hC) hne) haB') ha
    rwa [← hBC]
  have hpoint : ∀ a : Fin n,
      (componentPartition (π.parts.biUnion g)).part a = π.part a := by
    intro a
    have haπ : a ∈ π.part a := π.mem_part (Finset.mem_univ a)
    have hπparts : π.part a ∈ π.parts :=
      π.part_mem.mpr (Finset.mem_univ a)
    ext b
    rw [mem_componentPartition_part_iff]
    constructor
    · rintro ⟨p⟩
      exact mem_of_reachable_closed (hcl _ hπparts) p haπ
    · intro hb
      have hr := hconn _ hπparts a haπ b hb
      refine hr.mono ?_
      refine SimpleGraph.fromEdgeSet_mono ?_
      exact_mod_cast Finset.subset_biUnion_of_mem g hπparts
  have hparts : (componentPartition (π.parts.biUnion g)).parts
      = π.parts := by
    ext C
    constructor
    · intro hC
      obtain ⟨x, hx⟩ :=
        (componentPartition (π.parts.biUnion g)).nonempty_of_mem_parts hC
      have h1 : (componentPartition (π.parts.biUnion g)).part x = C :=
        (componentPartition (π.parts.biUnion g)).part_eq_of_mem hC hx
      rw [← h1, hpoint x]
      exact π.part_mem.mpr (Finset.mem_univ x)
    · intro hC
      obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hC
      have h1 : π.part x = C := π.part_eq_of_mem hC hx
      rw [← h1, ← hpoint x]
      exact (componentPartition
        (π.parts.biUnion g)).part_mem.mpr (Finset.mem_univ x)
  exact Finpartition.ext hparts

set_option maxHeartbeats 1600000 in
open Classical in
/-- **(★) The fiber factorization (B0a, step A4):** the alternating sum
over edge sets with component partition exactly `π` factorizes as the
product over parts of within-part connecting block sums. -/
theorem fiber_cp_factorization {n : ℕ} (A : Finset (Sym2 (Fin n)))
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ E ∈ A.powerset.filter
      (fun E : Finset (Sym2 (Fin n)) => componentPartition E = π),
      (-1 : ℤ) ^ E.card
    = ∏ B ∈ π.parts, ∑ E' ∈ A.powerset.filter
        (fun E' : Finset (Sym2 (Fin n)) =>
          (∀ e ∈ E', ∀ v ∈ e, v ∈ B) ∧
          ∀ v ∈ B, ∀ w ∈ B, (SimpleGraph.fromEdgeSet
            (↑E' : Set (Sym2 (Fin n)))).Reachable v w),
        (-1 : ℤ) ^ E'.card := by
  classical
  rw [Finset.prod_sum]
  refine Finset.sum_nbij'
    (fun E => fun B _ => E.filter (fun e => ∀ u ∈ e, u ∈ B))
    (fun p => π.parts.biUnion (fun B =>
      if h : B ∈ π.parts then p B h else ∅)) ?_ ?_ ?_ ?_ ?_
  · -- forward membership: components are block data
    intro E hE
    rw [Finset.mem_filter] at hE
    exact Finset.mem_pi.mpr fun B hB =>
      filter_within_mem_of_cp_eq hE.1 hE.2 hB
  · -- backward membership: unions are fiber members
    intro p hp
    have hpmem := Finset.mem_pi.mp hp
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro e he
      rw [Finset.mem_biUnion] at he
      obtain ⟨B, hB, heg⟩ := he
      rw [dif_pos hB] at heg
      have := (Finset.mem_filter.mp (hpmem B hB)).1
      exact Finset.mem_powerset.mp this heg
    · refine componentPartition_biUnion_eq _ ?_ ?_
      · intro B hB e he u hu
        rw [dif_pos hB] at he
        exact (Finset.mem_filter.mp (hpmem B hB)).2.1 e he u hu
      · intro B hB v hv w hw
        rw [dif_pos hB]
        exact (Finset.mem_filter.mp (hpmem B hB)).2.2 v hv w hw
  · -- left inverse
    intro E hE
    dsimp only
    have hcp := (Finset.mem_filter.mp hE).2
    calc π.parts.biUnion (fun B =>
          if h : B ∈ π.parts
          then E.filter (fun e => ∀ u ∈ e, u ∈ B) else ∅)
        = π.parts.biUnion (fun B =>
            E.filter (fun e => ∀ u ∈ e, u ∈ B)) :=
          Finset.biUnion_congr rfl (fun B hB => dif_pos hB)
      _ = E := biUnion_filter_within_parts hcp
  · -- right inverse
    intro p hp
    have hpmem := Finset.mem_pi.mp hp
    dsimp only
    funext B hB
    ext e
    constructor
    · intro he
      rw [Finset.mem_filter] at he
      obtain ⟨hbi, hwB⟩ := he
      rw [Finset.mem_biUnion] at hbi
      obtain ⟨B', hB', heg⟩ := hbi
      rw [dif_pos hB'] at heg
      have hwB' := (Finset.mem_filter.mp (hpmem B' hB')).2.1 e heg
      have hBB' : B' = B := by
        by_contra hne
        obtain ⟨u, hu⟩ : ∃ u, u ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
        exact (Finset.disjoint_left.mp
          (π.disjoint (Finset.mem_coe.mpr hB')
            (Finset.mem_coe.mpr hB) hne) (hwB' u hu)) (hwB u hu)
      subst hBB'
      exact heg
    · intro he
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_biUnion.mpr ⟨B, hB, ?_⟩, ?_⟩
      · rw [dif_pos hB]; exact he
      · exact (Finset.mem_filter.mp (hpmem B hB)).2.1 e he
  · -- values: cardinality additivity over the parts
    intro E hE
    dsimp only
    have hcp := (Finset.mem_filter.mp hE).2
    have hdisj : ∀ B ∈ π.parts, ∀ B' ∈ π.parts, B ≠ B' →
        Disjoint (E.filter (fun e => ∀ u ∈ e, u ∈ B))
          (E.filter (fun e => ∀ u ∈ e, u ∈ B')) := by
      intro B hB B' hB' hne
      exact filter_within_disjoint E
        (π.disjoint (Finset.mem_coe.mpr hB)
          (Finset.mem_coe.mpr hB') hne)
    have hcard : ∑ B ∈ π.parts,
        (E.filter (fun e => ∀ u ∈ e, u ∈ B)).card = E.card := by
      rw [← Finset.card_biUnion hdisj, biUnion_filter_within_parts hcp]
    calc (-1 : ℤ) ^ E.card
        = (-1 : ℤ) ^ (∑ B ∈ π.parts,
            (E.filter (fun e => ∀ u ∈ e, u ∈ B)).card) := by
          rw [hcard]
      _ = ∏ B ∈ π.parts, (-1 : ℤ)
            ^ (E.filter (fun e => ∀ u ∈ e, u ∈ B)).card :=
          (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ = ∏ x ∈ π.parts.attach, (-1 : ℤ)
            ^ (E.filter (fun e => ∀ u ∈ e, u ∈ (x : Finset (Fin n)))).card
          := (Finset.prod_attach _ _).symm

set_option maxHeartbeats 1600000 in
open Classical in
/-- **THE PARTITION IDENTITY (B0a, the combinatorial heart of the
Mayer–Ursell inversion):** summing block-Ursell products over all
partitions of the index set yields the pairwise-compatibility
indicator.  This is the identity that drives `Ξ = exp(clusterSum)`. -/
theorem ursell_partition_identity {n : ℕ} (X : Fin n → P.Polymer) :
    ∑ π : Finpartition (Finset.univ : Finset (Fin n)),
      ∏ B ∈ π.parts,
        ursell P (fun i : Fin B.card =>
          X ((B.orderIsoOfFin rfl i) : Fin n))
    = if PairwiseCompatible P X then 1 else 0 := by
  classical
  rw [← sum_neg_one_pow_eq_indicator P X]
  have hfib : ∑ E ∈ (incompGraph P X).edgeFinset.powerset,
      (-1 : ℤ) ^ E.card
      = ∑ π : Finpartition (Finset.univ : Finset (Fin n)),
          ∑ E ∈ (incompGraph P X).edgeFinset.powerset.filter
            (fun E : Finset (Sym2 (Fin n)) =>
              componentPartition E = π),
            (-1 : ℤ) ^ E.card := by
    have hexp : ∀ E ∈ (incompGraph P X).edgeFinset.powerset,
        (-1 : ℤ) ^ E.card
        = ∑ π : Finpartition (Finset.univ : Finset (Fin n)),
            if componentPartition E = π
            then (-1 : ℤ) ^ E.card else 0 := by
      intro E _
      rw [Finset.sum_eq_single (componentPartition E)
        (fun π _ hne => if_neg fun h => hne h.symm)
        (fun habs => absurd (Finset.mem_univ _) habs)]
      exact (if_pos rfl).symm
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    exact Finset.sum_congr rfl fun π _ => (Finset.sum_filter _ _).symm
  rw [hfib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [fiber_cp_factorization]
  refine Finset.prod_congr rfl fun B hB => ?_
  exact (sum_blockConnected_eq_ursell P X B rfl
    (π.nonempty_of_mem_parts hB)).symm

open Classical in
/-- Pairwise-compatible tuples are injective — a repeated polymer would
be incompatible with itself (the hard core). -/
lemma PairwiseCompatible.injective {n : ℕ} {X : Fin n → P.Polymer}
    (h : PairwiseCompatible P X) : Function.Injective X := by
  intro i j hij
  by_contra hne
  exact h i j hne (by rw [hij]; exact P.incomp_self (X j))

set_option maxHeartbeats 800000 in
open Classical in
/-- **B0b-4 (the injective collapse):** the activity sum over
pairwise-compatible `N`-tuples is `N!` times the admissible-set sum at
cardinality `N` — each admissible set has exactly `N!` enumerations. -/
lemma sum_pairwiseCompatible_eq [Fintype P.Polymer] {N : ℕ} :
    ∑ X ∈ (Finset.univ : Finset (Fin N → P.Polymer)).filter
      (fun X => PairwiseCompatible P X),
      ∏ i, P.activity (X i)
    = (N.factorial : ℂ) * ∑ S ∈ (Finset.univ :
        Finset (Finset P.Polymer)).filter
        (fun S => Admissible P S ∧ S.card = N),
        ∏ c ∈ S, P.activity c := by
  classical
  -- expand each compatible tuple over its image
  have hexpand : ∀ X ∈ (Finset.univ : Finset (Fin N → P.Polymer)).filter
      (fun X => PairwiseCompatible P X),
      (∏ i, P.activity (X i))
      = ∑ S ∈ (Finset.univ : Finset (Finset P.Polymer)).filter
          (fun S => Admissible P S ∧ S.card = N),
          if Finset.univ.image X = S
          then ∏ i, P.activity (X i) else 0 := by
    intro X hX
    have hcomp := (Finset.mem_filter.mp hX).2
    have hinj := hcomp.injective P
    have hmem : Finset.univ.image X ∈ (Finset.univ :
        Finset (Finset P.Polymer)).filter
        (fun S => Admissible P S ∧ S.card = N) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro c hc c' hc' hne
        rw [Finset.mem_image] at hc hc'
        obtain ⟨i, _, rfl⟩ := hc
        obtain ⟨j, _, rfl⟩ := hc'
        exact hcomp i j (fun h => hne (by rw [h]))
      · rw [Finset.card_image_of_injective _ hinj,
          Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_eq_single (Finset.univ.image X)
      (fun S _ hne => if_neg fun h => hne h.symm)
      (fun habs => absurd hmem habs)]
    exact (if_pos rfl).symm
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  obtain ⟨-, hadm, hcard⟩ := Finset.mem_filter.mp hS
  -- collapse the inner sum: the class is the enumerations of S
  have hclass : ∀ X ∈ (Finset.univ : Finset (Fin N → P.Polymer)).filter
      (fun X => PairwiseCompatible P X),
      (if Finset.univ.image X = S
        then ∏ i, P.activity (X i) else 0)
      = (if Function.Injective X ∧ Finset.univ.image X = S
        then ∏ c ∈ S, P.activity c else 0) := by
    intro X hX
    have hcomp := (Finset.mem_filter.mp hX).2
    by_cases h : Finset.univ.image X = S
    · rw [if_pos h, if_pos ⟨hcomp.injective P, h⟩]
      rw [← h, Finset.prod_image
        (fun i _ j _ hij => hcomp.injective P hij)]
    · rw [if_neg h, if_neg fun hc => h hc.2]
  rw [Finset.sum_congr rfl hclass]
  -- extend to the full tuple space: non-compatible terms vanish
  have hfull : ∑ X ∈ (Finset.univ : Finset (Fin N → P.Polymer)).filter
      (fun X => PairwiseCompatible P X),
      (if Function.Injective X ∧ Finset.univ.image X = S
        then ∏ c ∈ S, P.activity c else 0)
      = ∑ X : Fin N → P.Polymer,
        (if Function.Injective X ∧ Finset.univ.image X = S
          then ∏ c ∈ S, P.activity c else 0) := by
    refine Finset.sum_subset (Finset.filter_subset _ _)
      fun X _ hX => ?_
    refine if_neg fun hc => hX ?_
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i j hne hinc
    have hi : X i ∈ S := by
      rw [← hc.2]
      exact Finset.mem_image_of_mem X (Finset.mem_univ i)
    have hj : X j ∈ S := by
      rw [← hc.2]
      exact Finset.mem_image_of_mem X (Finset.mem_univ j)
    exact hadm (X i) hi (X j) hj (fun h => hne (hc.1 h)) hinc
  rw [hfull, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    card_enumerations hcard]

open Classical in
/-- **B0b-3 engine: generic symmetrization** — `sum_symmetrize_fn`
(SharpShell) with arbitrary finite codomain and `ℂ`-values: a sum over
objects equals the `1/k!`-weighted sum over (object, enumeration of its
attached finite set) pairs. -/
lemma sum_symmetrize_gen {nmax : ℕ} {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Finset α) (G : α → ℂ)
    (S : α → Finset β) (hSle : ∀ a ∈ A, (S a).card ≤ nmax) :
    ∑ a ∈ A, G a
    = ∑ k ∈ Finset.range (nmax + 1), ((k.factorial : ℂ))⁻¹ *
        ∑ a ∈ A, ∑ _σ ∈ (Finset.univ : Finset (Fin k → β)).filter
          (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S a),
          G a := by
  classical
  have hswap : ∀ k : ℕ, ((k.factorial : ℂ))⁻¹ *
      ∑ a ∈ A, ∑ _σ ∈ (Finset.univ : Finset (Fin k → β)).filter
        (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S a), G a
      = ∑ a ∈ A, ((k.factorial : ℂ))⁻¹ *
          (((Finset.univ : Finset (Fin k → β)).filter
            (fun σ => Function.Injective σ ∧ Finset.univ.image σ
              = S a)).card : ℂ) * G a := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  calc ∑ a ∈ A, G a
      = ∑ a ∈ A, ∑ k ∈ Finset.range (nmax + 1),
          ((k.factorial : ℂ))⁻¹ *
          (((Finset.univ : Finset (Fin k → β)).filter
            (fun σ => Function.Injective σ ∧ Finset.univ.image σ
              = S a)).card : ℂ) * G a := by
        refine Finset.sum_congr rfl fun a ha => ?_
        have hk0 : (S a).card ∈ Finset.range (nmax + 1) := by
          rw [Finset.mem_range]
          exact Nat.lt_succ_of_le (hSle a ha)
        rw [Finset.sum_eq_single_of_mem (S a).card hk0]
        · rw [card_enumerations rfl]
          have hne : (((S a).card.factorial : ℂ)) ≠ 0 := by
            exact_mod_cast Nat.cast_ne_zero.mpr
              (Nat.factorial_ne_zero _)
          field_simp
        · intro k _ hk
          rw [card_enumerations_ne (fun h => hk h.symm)]
          simp
    _ = ∑ k ∈ Finset.range (nmax + 1), ((k.factorial : ℂ))⁻¹ *
        ∑ a ∈ A, ∑ _σ ∈ (Finset.univ : Finset (Fin k → β)).filter
          (fun σ => Function.Injective σ ∧ Finset.univ.image σ = S a),
          G a := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (hswap k).symm

/-- **Ordered partitions** of `Fin N` into `k` labeled nonempty blocks
(the index of B0b's regrouping — enumerations of `Finpartition` parts). -/
def IsOrdPartition {N k : ℕ} (σ : Fin k → Finset (Fin N)) : Prop :=
  (∀ i, (σ i).Nonempty) ∧
  (∀ i j, i ≠ j → Disjoint (σ i) (σ j)) ∧
  Finset.univ.biUnion σ = Finset.univ

open Classical in
/-- Partitions of `Fin N` have at most `N` parts. -/
lemma parts_card_le {N : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin N))) :
    π.parts.card ≤ N := by
  calc π.parts.card = ∑ _B ∈ π.parts, 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ B ∈ π.parts, B.card :=
        Finset.sum_le_sum fun B hB =>
          Finset.card_pos.mpr (π.nonempty_of_mem_parts hB)
    _ = N := by
        rw [Finpartition.sum_card_parts, Finset.card_univ,
          Fintype.card_fin]

open Classical in
/-- The `Finpartition` carried by an ordered partition: its parts are
the blocks. -/
noncomputable def finpartitionOfOrd {N k : ℕ}
    (σ : Fin k → Finset (Fin N)) (h : IsOrdPartition σ) :
    Finpartition (Finset.univ : Finset (Fin N)) where
  parts := Finset.univ.image σ
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro B hB B' hB' hne
    rw [Finset.mem_coe, Finset.mem_image] at hB hB'
    obtain ⟨i, _, rfl⟩ := hB
    obtain ⟨j, _, rfl⟩ := hB'
    exact h.2.1 i j (fun hij => hne (by rw [hij]))
  sup_parts := by
    rw [Finset.sup_image]
    rw [show (id ∘ σ) = σ from rfl]
    rw [Finset.sup_eq_biUnion]
    exact h.2.2
  bot_notMem := by
    rw [Finset.mem_image]
    rintro ⟨i, _, hi⟩
    exact Finset.Nonempty.ne_empty (h.1 i) hi

open Classical in
@[simp]
lemma finpartitionOfOrd_parts {N k : ℕ}
    (σ : Fin k → Finset (Fin N)) (h : IsOrdPartition σ) :
    (finpartitionOfOrd σ h).parts = Finset.univ.image σ := rfl

/-- Ordered partitions are injective (disjoint nonempty blocks are
distinct). -/
lemma IsOrdPartition.injective {N k : ℕ}
    {σ : Fin k → Finset (Fin N)} (h : IsOrdPartition σ) :
    Function.Injective σ := by
  intro i j hij
  by_contra hne
  have hd := h.2.1 i j hne
  rw [hij] at hd
  exact Finset.Nonempty.ne_empty (h.1 j) (disjoint_self.mp hd)

set_option maxHeartbeats 800000 in
open Classical in
/-- **B0b (ii): the π-collapse** — partition sums of block products
equal `1/k!`-weighted sums over ordered partitions.  Enumerations of a
partition's parts are exactly the ordered partitions, each determining
its partition uniquely. -/
lemma sum_finpartition_eq_ordPartitions {N : ℕ}
    (h : Finset (Fin N) → ℂ) :
    ∑ π : Finpartition (Finset.univ : Finset (Fin N)),
      ∏ B ∈ π.parts, h B
    = ∑ k ∈ Finset.range (N + 1), ((k.factorial : ℂ))⁻¹ *
        ∑ σ ∈ (Finset.univ : Finset (Fin k → Finset (Fin N))).filter
          (fun σ => IsOrdPartition σ),
          ∏ i, h (σ i) := by
  classical
  rw [sum_symmetrize_gen (nmax := N) Finset.univ
    (fun π => ∏ B ∈ π.parts, h B) (fun π => π.parts)
    (fun π _ => parts_card_le π)]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  calc ∑ π ∈ (Finset.univ :
        Finset (Finpartition (Finset.univ : Finset (Fin N)))),
        ∑ _σ ∈ (Finset.univ : Finset (Fin k → Finset (Fin N))).filter
          (fun σ => Function.Injective σ
            ∧ Finset.univ.image σ = π.parts),
          ∏ B ∈ π.parts, h B
      = ∑ π ∈ (Finset.univ :
          Finset (Finpartition (Finset.univ : Finset (Fin N)))),
          ∑ σ ∈ (Finset.univ : Finset (Fin k → Finset (Fin N))).filter
            (fun σ => Function.Injective σ
              ∧ Finset.univ.image σ = π.parts),
            ∏ i, h (σ i) := by
        refine Finset.sum_congr rfl fun π _ => ?_
        refine Finset.sum_congr rfl fun σ hσ => ?_
        obtain ⟨hinj, himg⟩ := (Finset.mem_filter.mp hσ).2
        rw [← himg, Finset.prod_image
          (fun i _ j _ hij => hinj hij)]
    _ = ∑ σ : Fin k → Finset (Fin N),
          ∑ π ∈ (Finset.univ :
            Finset (Finpartition (Finset.univ : Finset (Fin N)))),
            if Function.Injective σ
              ∧ Finset.univ.image σ = π.parts
            then ∏ i, h (σ i) else 0 := by
        rw [Finset.sum_congr rfl
          (fun π _ => Finset.sum_filter _ _), Finset.sum_comm]
    _ = ∑ σ : Fin k → Finset (Fin N),
          (if IsOrdPartition σ then ∏ i, h (σ i) else 0) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        by_cases hord : IsOrdPartition σ
        · rw [Finset.sum_eq_single (finpartitionOfOrd σ hord)
            (fun π _ hne => if_neg fun hc => hne
              (Finpartition.ext
                (by rw [finpartitionOfOrd_parts, ← hc.2])))
            (fun habs => absurd (Finset.mem_univ _) habs)]
          rw [if_pos (⟨hord.injective,
            (finpartitionOfOrd_parts σ hord).symm⟩ :
              Function.Injective σ ∧ _), if_pos hord]
        · rw [if_neg hord]
          refine Finset.sum_eq_zero fun π _ => ?_
          refine if_neg fun hc => hord ?_
          obtain ⟨hinj, himg⟩ := hc
          refine ⟨?_, ?_, ?_⟩
          · intro i
            refine π.nonempty_of_mem_parts ?_
            rw [← himg]
            exact Finset.mem_image_of_mem σ (Finset.mem_univ i)
          · intro i j hij
            refine π.disjoint ?_ ?_ (fun hσ => hij (hinj hσ))
            · rw [Finset.mem_coe, ← himg]
              exact Finset.mem_image_of_mem σ (Finset.mem_univ i)
            · rw [Finset.mem_coe, ← himg]
              exact Finset.mem_image_of_mem σ (Finset.mem_univ j)
          · calc Finset.univ.biUnion σ
                = (Finset.univ.image σ).biUnion id := by
                  rw [Finset.image_biUnion]
                  rfl
              _ = π.parts.sup id := by
                  rw [himg, Finset.sup_eq_biUnion]
              _ = Finset.univ := π.sup_parts
    _ = ∑ σ ∈ (Finset.univ : Finset (Fin k → Finset (Fin N))).filter
          (fun σ => IsOrdPartition σ),
          ∏ i, h (σ i) := (Finset.sum_filter _ _).symm

open Classical in
/-- Ordered partitions carry block data (roots chosen in the nonempty
blocks) — unlocking the SharpShell cover-splitting machinery. -/
lemma IsOrdPartition.toBlockData {N k : ℕ}
    {σ : Fin k → Finset (Fin N)} (h : IsOrdPartition σ) :
    IsBlockData (Finset.univ : Finset (Fin N))
      (fun i => (σ i).card - 1)
      (fun i => (σ i, (h.1 i).choose)) := by
  refine ⟨h.2.1, h.2.2, fun i => (h.1 i).choose_spec, fun i => ?_⟩
  exact (Nat.succ_pred_eq_of_pos
    (Finset.card_pos.mpr (h.1 i))).symm

set_option maxHeartbeats 800000 in
open Classical in
/-- ℂ-valued cover splitting (the SharpShell `sum_coverSplit`, verbatim
at ℂ): block-product sums over cover functions factor into per-block
sums. -/
lemma sum_coverSplit_complex {n k : ℕ} {U : Finset (Fin n)}
    {m : Fin k → ℕ} {ρ : Fin k → Finset (Fin n) × Fin n}
    (hρ : IsBlockData U m ρ) {β : Type*} [Fintype β] [DecidableEq β]
    (G : ∀ i : Fin k, ({x // x ∈ (ρ i).1} → β) → ℂ) :
    ∑ g : {x // x ∈ U} → β, ∏ i, G i (hρ.coverSplitEquiv β g i)
    = ∏ i, ∑ h : {x // x ∈ (ρ i).1} → β, G i h := by
  classical
  rw [← Equiv.sum_comp (hρ.coverSplitEquiv β).symm
    (fun g => ∏ i, G i (hρ.coverSplitEquiv β g i))]
  have hsimp : ∀ t : ∀ i : Fin k, ({x // x ∈ (ρ i).1} → β),
      (∏ i, G i (hρ.coverSplitEquiv β
        ((hρ.coverSplitEquiv β).symm t) i))
      = ∏ i, G i (t i) := by
    intro t
    rw [Equiv.apply_symm_apply]
  rw [Finset.sum_congr rfl (fun t _ => hsimp t)]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **B0b (iii): the X-split** — for an ordered partition, summing a
product of per-block functionals of the restrictions over ALL functions
on `Fin N` factorizes exactly into the product of per-block sums. -/
theorem sum_split_ordPartition [Fintype P.Polymer] {N k : ℕ}
    (σ : Fin k → Finset (Fin N)) (hσ : IsOrdPartition σ)
    (G : ∀ m : ℕ, (Fin m → P.Polymer) → ℂ) :
    ∑ X : Fin N → P.Polymer,
      ∏ i, G (σ i).card
        (fun l => X (((σ i).orderIsoOfFin rfl l) : Fin N))
    = ∏ i, ∑ Y : Fin (σ i).card → P.Polymer, G (σ i).card Y := by
  classical
  have hbd := hσ.toBlockData
  -- the composite splitting equivalence (all sums stay over
  -- Fin-function spaces; the subtype machinery lives inside the equiv)
  let E : (Fin N → P.Polymer)
      ≃ ∀ i : Fin k, (Fin (σ i).card → P.Polymer) :=
    ((Equiv.arrowCongr
        (Equiv.subtypeUnivEquiv (fun x : Fin N => Finset.mem_univ x))
        (Equiv.refl P.Polymer)).symm).trans
      ((hbd.coverSplitEquiv P.Polymer).trans
        (Equiv.piCongrRight fun i =>
          Equiv.arrowCongr ((σ i).orderIsoOfFin rfl).toEquiv.symm
            (Equiv.refl P.Polymer)))
  calc ∑ X : Fin N → P.Polymer,
      ∏ i, G (σ i).card
        (fun l => X (((σ i).orderIsoOfFin rfl l) : Fin N))
      = ∑ X : Fin N → P.Polymer, ∏ i, G (σ i).card (E X i) := by
        refine congrArg (Finset.sum Finset.univ) (funext fun X => ?_)
        refine Finset.prod_congr rfl fun i _ => ?_
        refine congrArg (G (σ i).card) (funext fun l => ?_)
        rfl
    _ = ∑ p : ∀ i : Fin k, (Fin (σ i).card → P.Polymer),
          ∏ i, G (σ i).card (p i) :=
        Equiv.sum_comp E (fun p => ∏ i, G (σ i).card (p i))
    _ = ∏ i, ∑ Y : Fin (σ i).card → P.Polymer, G (σ i).card Y := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

set_option maxHeartbeats 800000 in
open Classical in
/-- **Enumeration tuples are bijections (B0b iv, the equivalence):**
tuples of per-block injections with pairwise-disjoint ranges are exactly
the bijections from the size-sigma to `Fin N`. -/
noncomputable def enumTuplesEquivSigma {N k : ℕ} (m : Fin k → ℕ)
    (hsum : ∑ i, m i = N) :
    {τ : ∀ i : Fin k, Fin (m i) → Fin N //
      (∀ i, Function.Injective (τ i)) ∧
      ∀ i j, i ≠ j → ∀ l l', τ i l ≠ τ j l'}
    ≃ ((Σ i : Fin k, Fin (m i)) ≃ Fin N) where
  toFun τ := Equiv.ofBijective (fun p => τ.1 p.1 p.2) (by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
    · rintro ⟨i, l⟩ ⟨j, l'⟩ h
      by_cases hij : i = j
      · subst hij
        exact congrArg (Sigma.mk i) (τ.2.1 i h)
      · exact absurd h (τ.2.2 i j hij l l')
    · rw [Fintype.card_sigma, Fintype.card_fin]
      simp only [Fintype.card_fin]
      exact hsum)
  invFun e := ⟨fun i l => e ⟨i, l⟩, fun i l l' h => by
      have h2 := e.injective h
      rw [Sigma.mk.injEq] at h2
      exact eq_of_heq h2.2,
    fun i j hij l l' h => by
      have h2 := e.injective h
      rw [Sigma.mk.injEq] at h2
      exact hij h2.1⟩
  left_inv τ := Subtype.ext (funext fun i => funext fun l => rfl)
  right_inv e := Equiv.ext fun p => rfl

set_option maxHeartbeats 1600000 in
open Classical in
/-- **B0b (iv): THE MULTINOMIAL COUNT** — the number of ordered
partitions with prescribed block sizes, multiplicatively:
`#ordp(m) · ∏ mᵢ! = N!`.  Counting enumeration tuples two ways: as
bijections (via `enumTuplesEquivSigma`) and fiberwise over their image
partitions. -/
theorem card_ordPartition_mul {N k : ℕ} (m : Fin k → ℕ)
    (hm : ∀ i, 1 ≤ m i) (hsum : ∑ i, m i = N) :
    ((Finset.univ : Finset (Fin k → Finset (Fin N))).filter
      (fun σ => IsOrdPartition σ ∧ ∀ i, (σ i).card = m i)).card
      * ∏ i, (m i).factorial = N.factorial := by
  classical
  -- count the enumeration tuples as bijections
  have hcards : Fintype.card (Σ i : Fin k, Fin (m i))
      = Fintype.card (Fin N) := by
    rw [Fintype.card_sigma, Fintype.card_fin]
    simp only [Fintype.card_fin]
    exact hsum
  have hcardE : ((Finset.univ :
      Finset (∀ i : Fin k, Fin (m i) → Fin N)).filter
      (fun τ => (∀ i, Function.Injective (τ i)) ∧
        ∀ i j, i ≠ j → ∀ l l', τ i l ≠ τ j l')).card
      = N.factorial := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr (enumTuplesEquivSigma m hsum)]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq hcards), hcards,
      Fintype.card_fin]
  -- count them fiberwise over the image partition
  have hmaps : ∀ τ ∈ (Finset.univ :
      Finset (∀ i : Fin k, Fin (m i) → Fin N)).filter
      (fun τ => (∀ i, Function.Injective (τ i)) ∧
        ∀ i j, i ≠ j → ∀ l l', τ i l ≠ τ j l'),
      (fun i => Finset.univ.image (τ i)) ∈ (Finset.univ :
        Finset (Fin k → Finset (Fin N))).filter
        (fun σ => IsOrdPartition σ ∧ ∀ i, (σ i).card = m i) := by
    intro τ hτ
    obtain ⟨hinj, hcross⟩ := (Finset.mem_filter.mp hτ).2
    have hsurj : Function.Surjective
        (fun p : Σ i : Fin k, Fin (m i) => τ p.1 p.2) := by
      refine ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨?_, hcards⟩).2
      rintro ⟨i, l⟩ ⟨j, l'⟩ h
      by_cases hij : i = j
      · subst hij
        exact congrArg (Sigma.mk i) (hinj i h)
      · exact absurd h (hcross i j hij l l')
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i
      haveI : Nonempty (Fin (m i)) := ⟨⟨0, hm i⟩⟩
      exact (Finset.univ_nonempty).image _
    · intro i j hij
      rw [Finset.disjoint_left]
      intro v hv hv'
      rw [Finset.mem_image] at hv hv'
      obtain ⟨l, _, rfl⟩ := hv
      obtain ⟨l', _, heq⟩ := hv'
      exact hcross i j hij l l' heq.symm
    · rw [Finset.eq_univ_iff_forall]
      intro v
      obtain ⟨p, hp⟩ := hsurj v
      rw [Finset.mem_biUnion]
      exact ⟨p.1, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, hp⟩⟩
    · intro i
      rw [Finset.card_image_of_injective _ (hinj i),
        Finset.card_univ, Fintype.card_fin]
  have hfiber := Finset.card_eq_sum_card_fiberwise hmaps
  -- per-σ fibers are products of per-block enumerations
  have hper : ∀ σ ∈ (Finset.univ :
      Finset (Fin k → Finset (Fin N))).filter
      (fun σ => IsOrdPartition σ ∧ ∀ i, (σ i).card = m i),
      (((Finset.univ :
        Finset (∀ i : Fin k, Fin (m i) → Fin N)).filter
        (fun τ => (∀ i, Function.Injective (τ i)) ∧
          ∀ i j, i ≠ j → ∀ l l', τ i l ≠ τ j l')).filter
        (fun τ => (fun i => Finset.univ.image (τ i)) = σ)).card
      = ∏ i, (m i).factorial := by
    intro σ hσ
    obtain ⟨hord, hcard⟩ := (Finset.mem_filter.mp hσ).2
    have hset : ((Finset.univ :
        Finset (∀ i : Fin k, Fin (m i) → Fin N)).filter
        (fun τ => (∀ i, Function.Injective (τ i)) ∧
          ∀ i j, i ≠ j → ∀ l l', τ i l ≠ τ j l')).filter
        (fun τ => (fun i => Finset.univ.image (τ i)) = σ)
        = Fintype.piFinset (fun i =>
            (Finset.univ : Finset (Fin (m i) → Fin N)).filter
              (fun τi => Function.Injective τi
                ∧ Finset.univ.image τi = σ i)) := by
      ext τ
      rw [Finset.mem_filter, Finset.mem_filter,
        Fintype.mem_piFinset]
      constructor
      · rintro ⟨⟨-, hinj, -⟩, himg⟩
        intro i
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hinj i, congrFun himg i⟩
      · intro hpi
        have hc : ∀ i, Function.Injective (τ i)
            ∧ Finset.univ.image (τ i) = σ i :=
          fun i => (Finset.mem_filter.mp (hpi i)).2
        refine ⟨⟨Finset.mem_univ _, fun i => (hc i).1, ?_⟩, ?_⟩
        · intro i j hij l l' heq
          have hv : τ i l ∈ σ i := by
            rw [← (hc i).2]
            exact Finset.mem_image_of_mem _ (Finset.mem_univ l)
          have hv' : τ j l' ∈ σ j := by
            rw [← (hc j).2]
            exact Finset.mem_image_of_mem _ (Finset.mem_univ l')
          rw [heq] at hv
          exact (Finset.disjoint_left.mp
            (hord.2.1 i j hij) hv) hv'
        · funext i
          exact (hc i).2
    rw [hset, Fintype.card_piFinset]
    exact Finset.prod_congr rfl fun i _ =>
      card_enumerations (hcard i)
  rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul]
    at hfiber
  rw [← hfiber]
  exact hcardE

open Classical in
/-- **B0b (v-a): products split over ordered partitions** — a product
over `Fin N` factors into per-block products through the order
isomorphisms. -/
lemma prod_split_ordPartition {N k : ℕ}
    (σ : Fin k → Finset (Fin N)) (hσ : IsOrdPartition σ)
    (f : Fin N → ℂ) :
    ∏ j, f j
    = ∏ i, ∏ l : Fin (σ i).card,
        f (((σ i).orderIsoOfFin rfl l) : Fin N) := by
  classical
  calc ∏ j, f j = ∏ j ∈ Finset.univ.biUnion σ, f j := by
        rw [hσ.2.2]
    _ = ∏ i, ∏ j ∈ σ i, f j :=
        Finset.prod_biUnion (fun i _ j _ hij => hσ.2.1 i j hij)
    _ = ∏ i, ∏ l : Fin (σ i).card,
          f (((σ i).orderIsoOfFin rfl l) : Fin N) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_coe_sort]
        exact (Equiv.prod_comp ((σ i).orderIsoOfFin rfl).toEquiv
          (fun x => f x)).symm

set_option maxHeartbeats 800000 in
open Classical in
/-- **B0b (v-b): the size fibration** — ordered-partition sums of
size-only weights collect by size vector, with the class count as
coefficient. -/
theorem sum_ordp_fiber_sizes {N k : ℕ} (W : ℕ → ℂ) :
    ∑ σ ∈ (Finset.univ : Finset (Fin k → Finset (Fin N))).filter
      (fun σ => IsOrdPartition σ),
      ∏ i, W ((σ i).card)
    = ∑ m ∈ (Fintype.piFinset
        fun _ : Fin k => Finset.range (N + 1)).filter
        (fun m => (∀ i, 1 ≤ m i) ∧ ∑ i, m i = N),
        (((Finset.univ : Finset (Fin k → Finset (Fin N))).filter
          (fun σ => IsOrdPartition σ ∧ ∀ i, (σ i).card = m i)).card
          : ℂ) * ∏ i, W (m i) := by
  classical
  have hexpand : ∀ σ ∈ (Finset.univ :
      Finset (Fin k → Finset (Fin N))).filter
      (fun σ => IsOrdPartition σ),
      ∏ i, W ((σ i).card)
      = ∑ m ∈ (Fintype.piFinset
          fun _ : Fin k => Finset.range (N + 1)).filter
          (fun m => (∀ i, 1 ≤ m i) ∧ ∑ i, m i = N),
          if (fun i => (σ i).card) = m
          then ∏ i, W ((σ i).card) else 0 := by
    intro σ hσ
    have hord := (Finset.mem_filter.mp hσ).2
    have hmem : (fun i => (σ i).card) ∈ (Fintype.piFinset
        fun _ : Fin k => Finset.range (N + 1)).filter
        (fun m => (∀ i, 1 ≤ m i) ∧ ∑ i, m i = N) := by
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => Finset.mem_range.mpr ?_,
        fun i => Finset.card_pos.mpr (hord.1 i), ?_⟩
      · exact Nat.lt_succ_of_le (Finset.card_le_card
          (Finset.subset_univ (σ i)) |>.trans
          (by rw [Finset.card_univ, Fintype.card_fin]))
      · calc ∑ i, (σ i).card
            = (Finset.univ.biUnion σ).card :=
              (Finset.card_biUnion
                (fun i _ j _ hij => hord.2.1 i j hij)).symm
          _ = N := by rw [hord.2.2, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_eq_single (fun i => (σ i).card)
      (fun m _ hne => if_neg fun h => hne h.symm)
      (fun habs => absurd hmem habs)]
    exact (if_pos rfl).symm
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hval : ∀ σ ∈ (Finset.univ :
      Finset (Fin k → Finset (Fin N))).filter
      (fun σ => IsOrdPartition σ),
      (if (fun i => (σ i).card) = m
        then ∏ i, W ((σ i).card) else 0)
      = (if (fun i => (σ i).card) = m
        then ∏ i, W (m i) else 0) := by
    intro σ _
    by_cases h : (fun i => (σ i).card) = m
    · rw [if_pos h, if_pos h]
      exact Finset.prod_congr rfl fun i _ => by rw [congrFun h i]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
  have hsets : ((Finset.univ : Finset (Fin k → Finset (Fin N))).filter
      (fun σ => IsOrdPartition σ ∧ (fun i => (σ i).card) = m))
      = (Finset.univ : Finset (Fin k → Finset (Fin N))).filter
        (fun σ => IsOrdPartition σ ∧ ∀ i, (σ i).card = m i) := by
    refine Finset.filter_congr fun σ _ => ?_
    constructor
    · rintro ⟨hord, hfn⟩
      exact ⟨hord, fun i => congrFun hfn i⟩
    · rintro ⟨hord, hall⟩
      exact ⟨hord, funext hall⟩
  rw [hsets]

set_option maxHeartbeats 1600000 in
open Classical in
/-- The compatibility indicator expands through ordered partitions
(the partition identity + the π-collapse, ℂ-cast). -/
lemma indicator_eq_ordp {N : ℕ} (X : Fin N → P.Polymer) :
    (if PairwiseCompatible P X then (1 : ℂ) else 0)
    = ∑ k ∈ Finset.range (N + 1), ((k.factorial : ℂ))⁻¹ *
        ∑ σ ∈ (Finset.univ : Finset (Fin k → Finset (Fin N))).filter
          (fun σ => IsOrdPartition σ),
          ∏ i, ((ursell P (fun l : Fin (σ i).card =>
            X (((σ i).orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ) := by
  classical
  have hii := sum_finpartition_eq_ordPartitions (N := N)
    (fun B => ((ursell P (fun l : Fin B.card =>
      X (↑(B.orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ))
  simp only [] at hii
  rw [← hii]
  have h := ursell_partition_identity P X
  by_cases hc : PairwiseCompatible P X
  · rw [if_pos hc] at h ⊢
    have h2 := congrArg (fun z : ℤ => (z : ℂ)) h
    push_cast at h2
    exact h2.symm
  · rw [if_neg hc] at h ⊢
    have h2 := congrArg (fun z : ℤ => (z : ℂ)) h
    push_cast at h2
    exact h2.symm

set_option maxHeartbeats 1600000 in
open Classical in
/-- **B0b (v), part M-a:** the compatible-tuple activity sum expands
through the partition identity into `1/k!`-weighted ordered-partition
sums of per-block cluster weights — the finite heart of
`Ξ = exp(clusterSum)`, with every X-dependence factorized away. -/
theorem sum_compat_eq_ordp [Fintype P.Polymer] (N : ℕ) :
    ∑ X ∈ (Finset.univ : Finset (Fin N → P.Polymer)).filter
      (fun X => PairwiseCompatible P X),
      ∏ j, P.activity (X j)
    = ∑ k ∈ Finset.range (N + 1), ((k.factorial : ℂ))⁻¹ *
        ∑ σ ∈ (Finset.univ : Finset (Fin k → Finset (Fin N))).filter
          (fun σ => IsOrdPartition σ),
          ∏ i, ∑ Y : Fin (σ i).card → P.Polymer,
            (ursell P Y : ℂ) * ∏ l, P.activity (Y l) := by
  classical
  have hX := fun X : Fin N → P.Polymer => indicator_eq_ordp P X
  calc ∑ X ∈ (Finset.univ : Finset (Fin N → P.Polymer)).filter
        (fun X => PairwiseCompatible P X),
        ∏ j, P.activity (X j)
      = ∑ X : Fin N → P.Polymer,
          (if PairwiseCompatible P X then (1 : ℂ) else 0)
            * ∏ j, P.activity (X j) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun X _ => by split_ifs <;> ring
    _ = ∑ X : Fin N → P.Polymer,
          (∑ k ∈ Finset.range (N + 1), ((k.factorial : ℂ))⁻¹ *
            ∑ σ ∈ (Finset.univ :
              Finset (Fin k → Finset (Fin N))).filter
              (fun σ => IsOrdPartition σ),
              ∏ i, ((ursell P (fun l : Fin (σ i).card =>
                X (((σ i).orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ))
            * ∏ j, P.activity (X j) :=
        Finset.sum_congr rfl fun X _ => by rw [hX X]
    _ = ∑ k ∈ Finset.range (N + 1), ((k.factorial : ℂ))⁻¹ *
          ∑ σ ∈ (Finset.univ :
            Finset (Fin k → Finset (Fin N))).filter
            (fun σ => IsOrdPartition σ),
            ∑ X : Fin N → P.Polymer,
              (∏ i, ((ursell P (fun l : Fin (σ i).card =>
                X (((σ i).orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ))
                * ∏ j, P.activity (X j) := by
        rw [Finset.sum_congr rfl (fun X
          (_ : X ∈ (Finset.univ : Finset (Fin N → P.Polymer))) =>
            Finset.sum_mul _ _ _), Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        calc ∑ X : Fin N → P.Polymer, (((k.factorial : ℂ))⁻¹ *
              ∑ σ ∈ (Finset.univ :
                Finset (Fin k → Finset (Fin N))).filter
                (fun σ => IsOrdPartition σ),
                ∏ i, ((ursell P (fun l : Fin (σ i).card =>
                  X (((σ i).orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ))
              * ∏ j, P.activity (X j)
            = ∑ X : Fin N → P.Polymer, ((k.factorial : ℂ))⁻¹ *
                ((∑ σ ∈ (Finset.univ :
                  Finset (Fin k → Finset (Fin N))).filter
                  (fun σ => IsOrdPartition σ),
                  ∏ i, ((ursell P (fun l : Fin (σ i).card =>
                    X (((σ i).orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ))
                  * ∏ j, P.activity (X j)) :=
              Finset.sum_congr rfl fun X _ => by ring
          _ = ((k.factorial : ℂ))⁻¹ * ∑ X : Fin N → P.Polymer,
                (∑ σ ∈ (Finset.univ :
                  Finset (Fin k → Finset (Fin N))).filter
                  (fun σ => IsOrdPartition σ),
                  ∏ i, ((ursell P (fun l : Fin (σ i).card =>
                    X (((σ i).orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ))
                  * ∏ j, P.activity (X j) :=
              (Finset.mul_sum _ _ _).symm
          _ = ((k.factorial : ℂ))⁻¹ * ∑ X : Fin N → P.Polymer,
                ∑ σ ∈ (Finset.univ :
                  Finset (Fin k → Finset (Fin N))).filter
                  (fun σ => IsOrdPartition σ),
                  (∏ i, ((ursell P (fun l : Fin (σ i).card =>
                    X (((σ i).orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ))
                    * ∏ j, P.activity (X j) := by
              congr 1
              exact Finset.sum_congr rfl fun X _ =>
                Finset.sum_mul _ _ _
          _ = ((k.factorial : ℂ))⁻¹ *
                ∑ σ ∈ (Finset.univ :
                  Finset (Fin k → Finset (Fin N))).filter
                  (fun σ => IsOrdPartition σ),
                  ∑ X : Fin N → P.Polymer,
                    (∏ i, ((ursell P (fun l : Fin (σ i).card =>
                      X (((σ i).orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ))
                      * ∏ j, P.activity (X j) := by
              rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (N + 1), ((k.factorial : ℂ))⁻¹ *
          ∑ σ ∈ (Finset.univ :
            Finset (Fin k → Finset (Fin N))).filter
            (fun σ => IsOrdPartition σ),
            ∏ i, ∑ Y : Fin (σ i).card → P.Polymer,
              (ursell P Y : ℂ) * ∏ l, P.activity (Y l) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun σ hσ => ?_
        have hord := (Finset.mem_filter.mp hσ).2
        calc ∑ X : Fin N → P.Polymer,
            (∏ i, ((ursell P (fun l : Fin (σ i).card =>
              X (((σ i).orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ))
              * ∏ j, P.activity (X j)
            = ∑ X : Fin N → P.Polymer,
                ∏ i, (((ursell P (fun l : Fin (σ i).card =>
                  X (((σ i).orderIsoOfFin rfl l) : Fin N)) : ℤ) : ℂ)
                  * ∏ l : Fin (σ i).card,
                    P.activity (X (((σ i).orderIsoOfFin rfl l)
                      : Fin N))) := by
              refine Finset.sum_congr rfl fun X _ => ?_
              rw [prod_split_ordPartition σ hord
                (fun j => P.activity (X j)), ← Finset.prod_mul_distrib]
          _ = ∏ i, ∑ Y : Fin (σ i).card → P.Polymer,
                (ursell P Y : ℂ) * ∏ l, P.activity (Y l) :=
              sum_split_ordPartition P σ hord
                (fun _ Y => (ursell P Y : ℂ) * ∏ l, P.activity (Y l))

set_option maxHeartbeats 1600000 in
open Classical in
/-- **B0b (v), part M-b — THE PER-`N` ENDPOINT:** the admissible-set
activity sum at cardinality `N` equals the `1/k!`-weighted size-vector
sums of normalized per-block cluster weights — the `N`-th coefficient
identity of `Ξ = exp(clusterSum)`. -/
theorem admissible_card_sum_eq [Fintype P.Polymer] (N : ℕ) :
    ∑ S ∈ (Finset.univ : Finset (Finset P.Polymer)).filter
      (fun S => Admissible P S ∧ S.card = N),
      ∏ c ∈ S, P.activity c
    = ∑ k ∈ Finset.range (N + 1), ((k.factorial : ℂ))⁻¹ *
        ∑ m ∈ (Fintype.piFinset
            fun _ : Fin k => Finset.range (N + 1)).filter
            (fun m => (∀ i, 1 ≤ m i) ∧ ∑ i, m i = N),
          ∏ i, (((m i).factorial : ℂ))⁻¹ *
            ∑ Y : Fin (m i) → P.Polymer,
              (ursell P Y : ℂ) * ∏ l, P.activity (Y l) := by
  classical
  have hNfac : ((N.factorial : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  -- from sets to compatible tuples
  have h1 : ∑ S ∈ (Finset.univ : Finset (Finset P.Polymer)).filter
      (fun S => Admissible P S ∧ S.card = N),
      ∏ c ∈ S, P.activity c
      = ((N.factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ : Finset (Fin N → P.Polymer)).filter
          (fun X => PairwiseCompatible P X),
          ∏ j, P.activity (X j) := by
    rw [sum_pairwiseCompatible_eq P, ← mul_assoc,
      inv_mul_cancel₀ hNfac, one_mul]
  rw [h1, sum_compat_eq_ordp P N, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfib := sum_ordp_fiber_sizes (N := N) (k := k)
    (fun m => ∑ Y : Fin m → P.Polymer,
      (ursell P Y : ℂ) * ∏ l, P.activity (Y l))
  simp only [] at hfib
  rw [hfib, ← mul_assoc,
    mul_comm ((N.factorial : ℂ))⁻¹ ((k.factorial : ℂ))⁻¹,
    mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, hmsum⟩ := (Finset.mem_filter.mp hm).2
  have hF : (∏ i, (((m i).factorial : ℕ) : ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    exact_mod_cast Nat.factorial_ne_zero (m i)
  have hc : (((Finset.univ :
      Finset (Fin k → Finset (Fin N))).filter
      (fun σ => IsOrdPartition σ ∧ ∀ i, (σ i).card = m i)).card : ℂ)
      * ∏ i, (((m i).factorial : ℕ) : ℂ) = ((N.factorial : ℕ) : ℂ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ))
      (card_ordPartition_mul m hm1 hmsum)
  have hinv : ((N.factorial : ℂ))⁻¹ * (((Finset.univ :
      Finset (Fin k → Finset (Fin N))).filter
      (fun σ => IsOrdPartition σ ∧ ∀ i, (σ i).card = m i)).card : ℂ)
      = (∏ i, (((m i).factorial : ℕ) : ℂ))⁻¹ := by
    have h2 : ((N.factorial : ℂ))⁻¹ * (((Finset.univ :
        Finset (Fin k → Finset (Fin N))).filter
        (fun σ => IsOrdPartition σ ∧ ∀ i, (σ i).card = m i)).card : ℂ)
        * (∏ i, (((m i).factorial : ℕ) : ℂ)) = 1 := by
      rw [mul_assoc, hc, inv_mul_cancel₀ hNfac]
    field_simp at h2 ⊢
    linear_combination h2
  calc ((N.factorial : ℂ))⁻¹ * ((((Finset.univ :
        Finset (Fin k → Finset (Fin N))).filter
        (fun σ => IsOrdPartition σ ∧ ∀ i, (σ i).card = m i)).card : ℂ)
        * ∏ i, ∑ Y : Fin (m i) → P.Polymer,
          (ursell P Y : ℂ) * ∏ l, P.activity (Y l))
      = (((N.factorial : ℂ))⁻¹ * (((Finset.univ :
          Finset (Fin k → Finset (Fin N))).filter
          (fun σ => IsOrdPartition σ ∧ ∀ i, (σ i).card = m i)).card
          : ℂ)) * ∏ i, ∑ Y : Fin (m i) → P.Polymer,
            (ursell P Y : ℂ) * ∏ l, P.activity (Y l) := by ring
    _ = (∏ i, (((m i).factorial : ℕ) : ℂ))⁻¹
          * ∏ i, ∑ Y : Fin (m i) → P.Polymer,
            (ursell P Y : ℂ) * ∏ l, P.activity (Y l) := by
        rw [hinv]
    _ = ∏ i, (((m i).factorial : ℂ))⁻¹ *
          ∑ Y : Fin (m i) → P.Polymer,
            (ursell P Y : ℂ) * ∏ l, P.activity (Y l) := by
        rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]

open Classical in
/-- **B0b (vi), step 1: the cardinality grading** — the partition
function is the sum of its fixed-cardinality admissible layers. -/
lemma partition_univ_eq_sum_card [Fintype P.Polymer] :
    partition P (Finset.univ : Finset P.Polymer)
    = ∑ N ∈ Finset.range (Fintype.card P.Polymer + 1),
        ∑ S ∈ (Finset.univ : Finset (Finset P.Polymer)).filter
          (fun S => Admissible P S ∧ S.card = N),
          ∏ c ∈ S, P.activity c := by
  classical
  unfold partition
  rw [Finset.powerset_univ]
  have hmaps : ∀ S ∈ (Finset.univ :
      Finset (Finset P.Polymer)).filter (Admissible P),
      S.card ∈ Finset.range (Fintype.card P.Polymer + 1) := by
    intro S _
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.card_le_univ S |>.trans
      (le_of_eq Finset.card_univ))
  rw [Finset.sum_fiberwise_of_maps_to hmaps
    (fun S => ∏ c ∈ S, P.activity c) |>.symm]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [Finset.filter_filter]

open Classical in
/-- **B0b (vi), step 1': the fully finite cluster form of `Ξ`** — the
partition function as the `N`-graded, `1/k!`-weighted size-vector sums
of normalized per-block cluster weights.  The exp-series side of the
Mayer–Ursell inversion matches this termwise. -/
theorem partition_univ_eq_cluster_layers [Fintype P.Polymer] :
    partition P (Finset.univ : Finset P.Polymer)
    = ∑ N ∈ Finset.range (Fintype.card P.Polymer + 1),
        ∑ k ∈ Finset.range (N + 1), ((k.factorial : ℂ))⁻¹ *
          ∑ m ∈ (Fintype.piFinset
              fun _ : Fin k => Finset.range (N + 1)).filter
              (fun m => (∀ i, 1 ≤ m i) ∧ ∑ i, m i = N),
            ∏ i, (((m i).factorial : ℂ))⁻¹ *
              ∑ Y : Fin (m i) → P.Polymer,
                (ursell P Y : ℂ) * ∏ l, P.activity (Y l) := by
  rw [partition_univ_eq_sum_card P]
  exact Finset.sum_congr rfl fun N _ => admissible_card_sum_eq P N

/-- A lightweight non-dependent cons equivalence for tuple spaces. -/
def consE (k : ℕ) : ℕ × (Fin k → ℕ) ≃ (Fin (k + 1) → ℕ) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, fun i => f i.succ)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · show Fin.cons (α := fun _ : Fin (k + 1) => ℕ) p.1 p.2 0 = p.1
      exact Fin.cons_zero _ _
    · funext i
      show Fin.cons (α := fun _ : Fin (k + 1) => ℕ) p.1 p.2 i.succ
        = p.2 i
      exact Fin.cons_succ _ _ _
  right_inv f := Fin.cons_self_tail f

set_option maxHeartbeats 800000 in
open Classical in
/-- **B0b (vi), E1a: norm-summability of product families.** -/
lemma summable_norm_prod_pow {a : ℕ → ℂ}
    (hA : Summable fun n => ‖a n‖) :
    ∀ k : ℕ, Summable fun f : Fin k → ℕ => ‖∏ i, a (f i)‖ := by
  intro k
  induction k with
  | zero =>
      refine (hasSum_single (f := fun f : Fin 0 → ℕ =>
        ‖∏ i, a (f i)‖) (fun i : Fin 0 => i.elim0) ?_).summable
      intro b' hb'
      exact absurd (funext fun i : Fin 0 => i.elim0) hb'
  | succ k ih =>
      have h2 : Summable
          (fun p : ℕ × (Fin k → ℕ) => ‖a p.1 * ∏ i, a (p.2 i)‖) :=
        Summable.mul_norm (f := a)
          (g := fun f : Fin k → ℕ => ∏ i, a (f i)) hA ih
      have h3 : Summable
          ((fun f : Fin (k + 1) → ℕ => ‖∏ i, a (f i)‖)
            ∘ (consE k)) := by
        refine h2.congr fun p => ?_
        show ‖a p.1 * ∏ i, a (p.2 i)‖
          = ‖∏ i : Fin (k + 1),
              a (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) p.1 p.2 i)‖
        congr 1
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
      exact (Equiv.summable_iff (consE k)).mp h3

set_option maxHeartbeats 800000 in
open Classical in
/-- **B0b (vi), E1b: the power Fubini** — powers of an absolutely
convergent series are tsums over tuple spaces. -/
lemma tsum_pow_eq_tsum_pi {a : ℕ → ℂ}
    (hA : Summable fun n => ‖a n‖) :
    ∀ k : ℕ, (∑' n, a n) ^ k = ∑' f : Fin k → ℕ, ∏ i, a (f i) := by
  intro k
  induction k with
  | zero =>
      rw [pow_zero, tsum_eq_single (fun i : Fin 0 => i.elim0)
        (fun b' hb' => absurd (funext fun i : Fin 0 => i.elim0) hb')]
      simp
  | succ k ih =>
      rw [pow_succ', ih,
        tsum_mul_tsum_of_summable_norm hA (summable_norm_prod_pow hA k)]
      calc ∑' z : ℕ × (Fin k → ℕ), a z.1 * ∏ i, a (z.2 i)
          = ∑' z : ℕ × (Fin k → ℕ),
              (fun g : Fin (k + 1) → ℕ => ∏ i, a (g i))
                (consE k z) := by
            refine tsum_congr fun z => ?_
            show a z.1 * ∏ i, a (z.2 i)
              = ∏ i : Fin (k + 1),
                  a (Fin.cons (α := fun _ : Fin (k + 1) => ℕ)
                    z.1 z.2 i)
            rw [Fin.prod_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
        _ = ∑' g : Fin (k + 1) → ℕ, ∏ i, a (g i) :=
            Equiv.tsum_eq (consE k) (fun g => ∏ i, a (g i))

end YangMills.KP

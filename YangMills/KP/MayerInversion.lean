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

end YangMills.KP

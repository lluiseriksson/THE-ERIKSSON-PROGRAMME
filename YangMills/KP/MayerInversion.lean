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

end YangMills.KP

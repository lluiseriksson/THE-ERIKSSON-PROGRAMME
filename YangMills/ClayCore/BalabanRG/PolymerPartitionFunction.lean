import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerCombinatorics

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerPartitionFunction -- Layer 2A (minimal)

Finite polymer partition function.
Reference: E26 P89 (2602.0134), Section 3.
-/

def CompatibleSubfamily {d : ℕ} {L : ℤ} (S : Finset (Polymer d L)) : Prop :=
  ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → Polymer.Compatible X Y

theorem compatibleSubfamily_empty {d : ℕ} {L : ℤ} :
    CompatibleSubfamily (∅ : Finset (Polymer d L)) :=
  fun X hX => by simp at hX

theorem compatibleSubfamily_singleton {d : ℕ} {L : ℤ} (X : Polymer d L) :
    CompatibleSubfamily ({X} : Finset (Polymer d L)) := by
  intro Y hY Z hZ hne
  simp only [Finset.mem_singleton] at hY hZ
  subst hY; subst hZ; exact (hne rfl).elim

noncomputable def compatibleSubfamilies {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) : Finset (Finset (Polymer d L)) :=
  Gamma.powerset.filter (fun S => CompatibleSubfamily S)

theorem mem_compatibleSubfamilies_iff {d : ℕ} {L : ℤ}
    {Gamma S : Finset (Polymer d L)} :
    S ∈ compatibleSubfamilies Gamma ↔ S ⊆ Gamma ∧ CompatibleSubfamily S := by
  simp [compatibleSubfamilies, Finset.mem_filter, Finset.mem_powerset]

theorem empty_mem_compatibleSubfamilies {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) :
    (∅ : Finset (Polymer d L)) ∈ compatibleSubfamilies Gamma := by
  simp [mem_compatibleSubfamilies_iff, compatibleSubfamily_empty]

theorem singleton_mem_compatibleSubfamilies {d : ℕ} {L : ℤ}
    {Gamma : Finset (Polymer d L)} {X : Polymer d L} (hX : X ∈ Gamma) :
    ({X} : Finset (Polymer d L)) ∈ compatibleSubfamilies Gamma := by
  simp [mem_compatibleSubfamilies_iff, hX, compatibleSubfamily_singleton]

def partitionWeight {d : ℕ} {L : ℤ}
    (K : Activity d L) (S : Finset (Polymer d L)) : ℝ :=
  ∏ X ∈ S, K X

theorem partitionWeight_empty {d : ℕ} {L : ℤ} (K : Activity d L) :
    partitionWeight K (∅ : Finset (Polymer d L)) = 1 := by
  simp [partitionWeight]

theorem partitionWeight_singleton {d : ℕ} {L : ℤ}
    (K : Activity d L) (X : Polymer d L) :
    partitionWeight K ({X} : Finset (Polymer d L)) = K X := by
  simp [partitionWeight]

theorem abs_partitionWeight_eq {d : ℕ} {L : ℤ}
    (K : Activity d L) (S : Finset (Polymer d L)) :
    |partitionWeight K S| = ∏ X ∈ S, |K X| := by
  simp [partitionWeight, Finset.abs_prod]

theorem abs_partitionWeight_le {d : ℕ} {L : ℤ}
    (K : Activity d L) (S : Finset (Polymer d L)) :
    |partitionWeight K S| ≤ ∏ X ∈ S, |K X| :=
  le_of_eq (abs_partitionWeight_eq K S)

noncomputable def polymerPartitionFunction {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) : ℝ :=
  ∑ S ∈ compatibleSubfamilies Gamma, partitionWeight K S

theorem polymerPartitionFunction_empty {d : ℕ} {L : ℤ}
    (K : Activity d L) :
    polymerPartitionFunction (∅ : Finset (Polymer d L)) K = 1 := by
  classical
  rw [polymerPartitionFunction, compatibleSubfamilies, Finset.powerset_empty]
  -- goal: ∑ S ∈ {∅}.filter CompatibleSubfamily, partitionWeight K S = 1
  have hf : ({∅} : Finset (Finset (Polymer d L))).filter CompatibleSubfamily = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, by subst h; exact compatibleSubfamily_empty⟩
  rw [hf]
  simp [partitionWeight]

theorem polymerPartitionFunction_singleton {d : ℕ} {L : ℤ}
    (K : Activity d L) (X : Polymer d L) :
    polymerPartitionFunction ({X} : Finset (Polymer d L)) K = 1 + K X := by
  classical
  rw [polymerPartitionFunction, compatibleSubfamilies]
  rw [show ({X} : Finset (Polymer d L)) = insert X ∅ by simp]
  rw [Finset.powerset_insert, Finset.powerset_empty]
  -- goal: ∑ S ∈ ({∅} ∪ image (insert X) {∅}).filter CompatibleSubfamily, ... = 1 + K X
  -- Evaluate the union and filter explicitly
  have hfull : ({∅} ∪ Finset.image (insert X) {∅} : Finset (Finset (Polymer d L))) =
      {∅, {X}} := by
    ext S; simp
  have hf : ({∅, {X}} : Finset (Finset (Polymer d L))).filter CompatibleSubfamily =
      {∅, {X}} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rcases h with rfl | rfl
      · exact compatibleSubfamily_empty
      · exact compatibleSubfamily_singleton X
  rw [hfull, hf]
  simp [partitionWeight, add_comm]

end YangMills.ClayCore

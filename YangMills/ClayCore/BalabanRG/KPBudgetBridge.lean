import Mathlib
import YangMills.ClayCore.BalabanRG.KPFiniteTailBound
import YangMills.ClayCore.BalabanRG.PolymerPartitionFunction

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPBudgetBridge -- Layer 3B

Bridge: KPOnGamma -> SmallActivityBudget.
This file: base cases + singleton + insert-split lemma skeleton.
-/

noncomputable section

def CompatibleFamilyMajorant {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (B : ℝ) : Prop :=
  ∑ S ∈ (compatibleSubfamilies Gamma).erase ∅, ∏ X ∈ S, |K X| ≤ B

theorem compatibleFamilyMajorant_implies_smallActivityBudget {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (B : ℝ)
    (h : CompatibleFamilyMajorant Gamma K B) :
    SmallActivityBudget Gamma K B := h

theorem abs_Z_sub_one_le_of_majorant {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (B : ℝ)
    (h : CompatibleFamilyMajorant Gamma K B) :
    |polymerPartitionFunction Gamma K - 1| ≤ B :=
  abs_polymerPartitionFunction_sub_one_le Gamma K B h

/-! ## Base cases -/

-- L39 fix: unfold CompatibleFamilyMajorant, then show erase gives empty sum
theorem compatibleFamilyMajorant_empty {d : ℕ} {L : ℤ} (K : Activity d L) :
    CompatibleFamilyMajorant (∅ : Finset (Polymer d L)) K 0 := by
  unfold CompatibleFamilyMajorant
  have h : compatibleSubfamilies (∅ : Finset (Polymer d L)) = {∅} := by
    ext S
    constructor
    · intro hS
      rw [mem_compatibleSubfamilies_iff] at hS
      have hEq : S = ∅ := Finset.subset_empty.mp hS.1
      simp [hEq]
    · intro hS
      simp only [Finset.mem_singleton] at hS
      subst hS
      exact empty_mem_compatibleSubfamilies ∅
  rw [h, Finset.erase_singleton, Finset.sum_empty]

theorem smallActivityBudget_empty {d : ℕ} {L : ℤ} (K : Activity d L) :
    SmallActivityBudget (∅ : Finset (Polymer d L)) K 0 :=
  compatibleFamilyMajorant_empty K

/-! ## Singleton case -/

theorem compatibleSubfamilies_singleton_erase_empty {d : ℕ} {L : ℤ}
    (X : Polymer d L) :
    (compatibleSubfamilies ({X} : Finset (Polymer d L))).erase ∅ = {{X}} := by
  ext S
  simp only [Finset.mem_erase, mem_compatibleSubfamilies_iff, Finset.mem_singleton]
  constructor
  · intro ⟨hne, hsub, _⟩
    rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
    · exact absurd rfl hne
    · rfl
  · intro h
    subst h
    refine ⟨Finset.singleton_ne_empty X, ?_, compatibleSubfamily_singleton X⟩
    intro Y hY; exact hY

theorem singleton_activity_bound_implies_majorant {d : ℕ} {L : ℤ}
    (K : Activity d L) (X : Polymer d L) (B : ℝ) (hB : |K X| ≤ B) :
    CompatibleFamilyMajorant ({X} : Finset (Polymer d L)) K B := by
  unfold CompatibleFamilyMajorant
  rw [compatibleSubfamilies_singleton_erase_empty]
  simp [partitionWeight, hB]

theorem kpOnGamma_singleton_budget {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ) (X : Polymer d L)
    (hKP : KPOnGamma ({X} : Finset (Polymer d L)) K a) :
    CompatibleFamilyMajorant ({X} : Finset (Polymer d L)) K
      (a * Real.exp (-a * (X.size : ℝ))) := by
  apply singleton_activity_bound_implies_majorant
  obtain ⟨x, hx⟩ := X.nonEmpty
  -- L92 fix: build hsingle without constructor (simp already closes both directions)
  have hsingle : touchingPolymers ({X} : Finset (Polymer d L)) x =
      ({X} : Finset (Polymer d L)) := by
    ext Y
    simp only [mem_touchingPolymers_iff, Finset.mem_singleton, Polymer.Touches]
    exact ⟨fun h => h.1, fun h => by subst h; exact ⟨rfl, hx⟩⟩
  have hbound := kpOnGamma_singleton_touching_bound hKP hsingle
  simp only [weightedActivity] at hbound
  have hexp : 0 < Real.exp (a * (X.size : ℝ)) := Real.exp_pos _
  calc |K X|
      ≤ a / Real.exp (a * (X.size : ℝ)) :=
          (le_div_iff₀ hexp).mpr (by linarith)
    _ = a * (Real.exp (a * (X.size : ℝ)))⁻¹ := by rw [div_eq_mul_inv]
    _ = a * Real.exp (-(a * (X.size : ℝ))) := by rw [← Real.exp_neg]
    _ = a * Real.exp (-a * (X.size : ℝ)) := by congr 1; ring

end

/-!
## Next: compatibleSubfamilies_insert_split

Key combinatorial lemma for the full induction:

  theorem compatibleSubfamilies_insert_split (X : Polymer d L)
      (hX : X ∉ Gamma) :
      (compatibleSubfamilies (insert X Gamma)).erase ∅ =
      -- subfamilies NOT containing X (= compatibleSubfamilies Gamma erase empty)
      (compatibleSubfamilies Gamma).erase ∅
      -- subfamilies containing X (= {insert X S | S compatible in Gamma, S disjoint from {X}})
      ∪ Finset.image (insert X) (compatibleSubfamilies Gamma)

This split + Finset.sum_union (disjoint) + IH closes the induction.
-/

end YangMills.ClayCore

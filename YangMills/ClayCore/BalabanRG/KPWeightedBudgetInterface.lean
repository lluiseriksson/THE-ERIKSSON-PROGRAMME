import Mathlib
import YangMills.ClayCore.BalabanRG.KPWeightedActivityInterface
import YangMills.ClayCore.BalabanRG.KPBudgetBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPWeightedBudgetInterface — (v1.0.17-alpha repair)

Weighted compatible-family budget layer over the abstract KP weight interface.

Conservative design:
- preserve the old "KPWeightedActivity" naming as a compatibility alias,
- define weighted family weight / weighted majorant / weighted induction budget,
- prove empty and singleton cases,
- package the exponential polymer-size weight as the first concrete instance.
-/

noncomputable section

/-- Compatibility alias for the old name used in earlier drafts. -/
abbrev KPWeightedActivity (d : ℕ) (L : ℤ) := KPWeight d L

/-- Weighted absolute family weight:
`∏_{X∈S} (|K X| * w X)`. -/
noncomputable def kpWeightedFamilyWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPWeightedActivity d L)
    (S : Finset (Polymer d L)) : ℝ :=
  ∏ X ∈ S, (|K X| * w X)

/-- Weighted compatible-family majorant. -/
def KPWeightedCompatibleFamilyMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ) : Prop :=
  ∑ S ∈ (compatibleSubfamilies Gamma).erase ∅,
      kpWeightedFamilyWeight K w S ≤ B

/-- Weighted induction budget. -/
noncomputable def KPWeightedInductionBudget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L) : ℝ :=
  ∑ S ∈ (compatibleSubfamilies Gamma).erase ∅,
      kpWeightedFamilyWeight K w S

/-- The weighted induction budget is tautologically a weighted compatible-family
majorant. -/
theorem kpWeightedInductionBudget_is_majorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L) :
    KPWeightedCompatibleFamilyMajorant Gamma K w
      (KPWeightedInductionBudget Gamma K w) := by
  unfold KPWeightedCompatibleFamilyMajorant KPWeightedInductionBudget
  exact le_rfl

/-- Empty weighted majorant. -/
theorem kpWeightedCompatibleFamilyMajorant_empty
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    (w : KPWeightedActivity d L) :
    KPWeightedCompatibleFamilyMajorant (∅ : Finset (Polymer d L)) K w 0 := by
  unfold KPWeightedCompatibleFamilyMajorant
  have h :
      compatibleSubfamilies (∅ : Finset (Polymer d L)) = {∅} := by
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

/-- Empty weighted induction budget. -/
theorem kpWeightedInductionBudget_empty
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    (w : KPWeightedActivity d L) :
    KPWeightedInductionBudget (∅ : Finset (Polymer d L)) K w = 0 := by
  unfold KPWeightedInductionBudget
  have h :
      compatibleSubfamilies (∅ : Finset (Polymer d L)) = {∅} := by
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

/-- Weighted family weight on a singleton support. -/
theorem kpWeightedFamilyWeight_singleton
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (X : Polymer d L) :
    kpWeightedFamilyWeight K w ({X} : Finset (Polymer d L)) = |K X| * w X := by
  simp [kpWeightedFamilyWeight]

/-- Singleton weighted majorant from a single weighted activity bound. -/
theorem kpWeightedCompatibleFamilyMajorant_singleton
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (X : Polymer d L)
    (B : ℝ)
    (hB : |K X| * w X ≤ B) :
    KPWeightedCompatibleFamilyMajorant ({X} : Finset (Polymer d L)) K w B := by
  unfold KPWeightedCompatibleFamilyMajorant
  rw [compatibleSubfamilies_singleton_erase_empty]
  simpa [kpWeightedFamilyWeight, hB]

/-- Singleton weighted induction budget computes exactly to the weighted activity
of the single polymer. -/
theorem kpWeightedInductionBudget_singleton
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (X : Polymer d L) :
    KPWeightedInductionBudget ({X} : Finset (Polymer d L)) K w = |K X| * w X := by
  unfold KPWeightedInductionBudget
  rw [compatibleSubfamilies_singleton_erase_empty]
  simp [kpWeightedFamilyWeight]

/-! ## First concrete instance: exponential polymer-size weight -/

/-- Compatibility alias with the parameter order used by older local proofs. -/
theorem kp_weightedActivity_bound_via_kpExpSizeWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (hKP : KoteckyPreiss K a) :
    |K X| * kpExpSizeWeight a d L X ≤ a := by
  exact kp_weighted_activity_bound_via_expSizeWeight K a hKP X

/-- Exponential size weight gives a singleton weighted majorant directly from KP. -/
theorem kpWeightedCompatibleFamilyMajorant_singleton_expSizeWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (hKP : KoteckyPreiss K a) :
    KPWeightedCompatibleFamilyMajorant ({X} : Finset (Polymer d L))
      K (kpExpSizeWeight a d L) a := by
  apply kpWeightedCompatibleFamilyMajorant_singleton
  exact kp_weightedActivity_bound_via_kpExpSizeWeight K a X hKP

/-- Exponential size weight gives the singleton weighted induction budget bound
directly from KP. -/
theorem kpWeightedInductionBudget_singleton_expSizeWeight_le
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (hKP : KoteckyPreiss K a) :
    KPWeightedInductionBudget ({X} : Finset (Polymer d L))
      K (kpExpSizeWeight a d L) ≤ a := by
  rw [kpWeightedInductionBudget_singleton]
  exact kp_weightedActivity_bound_via_kpExpSizeWeight K a X hKP

end

end YangMills.ClayCore

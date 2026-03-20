import Mathlib
import YangMills.ClayCore.BalabanRG.KPBudgetBridge
import YangMills.ClayCore.BalabanRG.KPWeightedActivityInterface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPWeightedBudgetInterface — (v1.0.16-alpha Phase 2)

Weighted compatible-family budget layer on the native KP side.

This phase remains conservative:
- it does not alter the existing unweighted KP induction,
- it introduces the weighted analogue of the family majorant/budget objects,
- it proves the empty/singleton cases,
- and it packages the exponential size weight as the first concrete instance.
-/

noncomputable section

/-- Weighted family weight:
product of weighted activities over a compatible subfamily. -/
noncomputable def KPWeightedFamilyWeight {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L)
    (S : Finset (Polymer d L)) : ℝ :=
  ∏ X ∈ S, KPWeightedActivity K w X

/-- Weighted compatible-family majorant. -/
def KPWeightedCompatibleFamilyMajorant {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L) (w : KPPolymerWeight d L) (B : ℝ) : Prop :=
  ∑ S ∈ (compatibleSubfamilies Gamma).erase ∅, KPWeightedFamilyWeight K w S ≤ B

/-- Weighted induction budget attached to a polymer weight. -/
noncomputable def KPWeightedInductionBudget {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L) (w : KPPolymerWeight d L) : ℝ :=
  ∑ S ∈ (compatibleSubfamilies Gamma).erase ∅, KPWeightedFamilyWeight K w S

/-- Nonnegativity of the weighted family weight under a nonnegative weight.
0 sorrys. -/
theorem kpWeightedFamilyWeight_nonneg
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L)
    (hw : KPWeightNonneg d L w) (S : Finset (Polymer d L)) :
    0 ≤ KPWeightedFamilyWeight K w S := by
  unfold KPWeightedFamilyWeight
  exact Finset.prod_nonneg (fun X hX => kpWeightedActivity_nonneg K w hw X)

/-- Singleton family weight reduces to the singleton weighted activity.
0 sorrys. -/
theorem kpWeightedFamilyWeight_singleton
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L)
    (X : Polymer d L) :
    KPWeightedFamilyWeight K w ({X} : Finset (Polymer d L)) =
      KPWeightedActivity K w X := by
  simp [KPWeightedFamilyWeight]

/-- The weighted induction budget is tautologically a weighted majorant.
0 sorrys. -/
theorem kpWeightedInductionBudget_is_majorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L) (w : KPPolymerWeight d L) :
    KPWeightedCompatibleFamilyMajorant Gamma K w
      (KPWeightedInductionBudget Gamma K w) := by
  unfold KPWeightedCompatibleFamilyMajorant KPWeightedInductionBudget
  exact le_rfl

/-! ## Base cases -/

/-- Empty-support weighted majorant. 0 sorrys. -/
theorem kpWeightedCompatibleFamilyMajorant_empty
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L) :
    KPWeightedCompatibleFamilyMajorant (∅ : Finset (Polymer d L)) K w 0 := by
  unfold KPWeightedCompatibleFamilyMajorant
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

/-- Empty weighted induction budget is zero. 0 sorrys. -/
theorem kpWeightedInductionBudget_empty
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L) :
    KPWeightedInductionBudget (∅ : Finset (Polymer d L)) K w = 0 := by
  unfold KPWeightedInductionBudget
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

/-! ## Singleton case -/

/-- Singleton weighted majorant from a single weighted activity bound.
0 sorrys. -/
theorem kpWeightedCompatibleFamilyMajorant_singleton
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L)
    (X : Polymer d L) (B : ℝ)
    (hB : KPWeightedActivity K w X ≤ B) :
    KPWeightedCompatibleFamilyMajorant ({X} : Finset (Polymer d L)) K w B := by
  unfold KPWeightedCompatibleFamilyMajorant
  rw [compatibleSubfamilies_singleton_erase_empty]
  simpa [kpWeightedFamilyWeight_singleton] using hB

/-- Singleton weighted induction budget evaluates to the weighted activity.
0 sorrys. -/
theorem kpWeightedInductionBudget_singleton
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L)
    (X : Polymer d L) :
    KPWeightedInductionBudget ({X} : Finset (Polymer d L)) K w =
      KPWeightedActivity K w X := by
  unfold KPWeightedInductionBudget
  rw [compatibleSubfamilies_singleton_erase_empty]
  simpa [kpWeightedFamilyWeight_singleton]

/-! ## First concrete instance: exponential size weight -/

/-- Singleton weighted majorant for the KP exponential size weight.
0 sorrys. -/
theorem kpExpSizeWeight_singleton_majorant
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ) (X : Polymer d L)
    (hKP : KoteckyPreiss K a) :
    KPWeightedCompatibleFamilyMajorant ({X} : Finset (Polymer d L))
      K (kpExpSizeWeight a d L) a := by
  apply kpWeightedCompatibleFamilyMajorant_singleton
  exact kp_weightedActivity_bound_via_kpExpSizeWeight K a hKP X

/-- Singleton weighted induction budget for the exponential size weight is
bounded by `a` under KP. 0 sorrys. -/
theorem kpExpSizeWeight_singleton_budget_le
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (a : ℝ) (X : Polymer d L)
    (hKP : KoteckyPreiss K a) :
    KPWeightedInductionBudget ({X} : Finset (Polymer d L))
      K (kpExpSizeWeight a d L) ≤ a := by
  rw [kpWeightedInductionBudget_singleton]
  exact kp_weightedActivity_bound_via_kpExpSizeWeight K a hKP X

/-- Scale-specialized singleton weighted majorant for `ActivityFamily`.
0 sorrys. -/
theorem kpExpSizeWeight_singleton_majorant_scale
    {d k : ℕ}
    (K : ActivityFamily d k) (a : ℝ) (X : Polymer d (Int.ofNat k))
    (hKP : KoteckyPreiss K a) :
    KPWeightedCompatibleFamilyMajorant ({X} : Finset (Polymer d (Int.ofNat k)))
      K (kpExpSizeWeight a d (Int.ofNat k)) a := by
  exact kpExpSizeWeight_singleton_majorant
    (d := d) (L := Int.ofNat k) K a X hKP

end

end YangMills.ClayCore

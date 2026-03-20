import Mathlib
import YangMills.ClayCore.BalabanRG.KPWeightedBudgetInterface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPWeightedBudgetToPartition — (v1.0.16-alpha Phase 3, conservative)

Bridge from weighted KP-compatible-family budgets back to the native
partition-function control.

Conservative design:
- weighted family weights dominate native absolute family weights,
- weighted compatible-family majorants imply native compatible-family majorants,
- hence recover `SmallActivityBudget` and `|Z - 1| ≤ B`,
- exponential-size-weight specialization is kept, but its `w ≥ 1` fact is passed
  explicitly instead of being reconstructed inside this file.
-/

noncomputable section

/-- Native absolute family weight written explicitly. 0 sorrys. -/
theorem absFamilyWeight_eq_unweightedFamilyWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (S : Finset (Polymer d L)) :
    absFamilyWeight K S = ∏ X ∈ S, |K X| := by
  rfl

/-- If `1 ≤ w(X)` pointwise, then native absolute family weight is bounded by
the weighted family weight. 0 sorrys. -/
theorem absFamilyWeight_le_kpWeightedFamilyWeight
    {d : ℕ} {L : ℤ}
    (K : Activity d L) (w : KPPolymerWeight d L)
    (hw_ge_one : KPWeightGeOne d L w)
    (S : Finset (Polymer d L)) :
    absFamilyWeight K S ≤ KPWeightedFamilyWeight K w S := by
  classical
  unfold absFamilyWeight KPWeightedFamilyWeight KPWeightedActivity
  refine Finset.prod_le_prod ?_ ?_
  · intro X hX
    exact abs_nonneg (K X)
  · intro X hX
    have hw : 1 ≤ w X := hw_ge_one X
    calc
      |K X| = |K X| * 1 := by ring
      _ ≤ |K X| * w X := by
        exact mul_le_mul_of_nonneg_left hw (abs_nonneg (K X))

/-- Native induction budget is bounded by the weighted induction budget
when `w ≥ 1`. 0 sorrys. -/
theorem inductionBudget_le_kpWeightedInductionBudget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L) (w : KPPolymerWeight d L)
    (hw_ge_one : KPWeightGeOne d L w) :
    InductionBudget Gamma K 0 ≤ KPWeightedInductionBudget Gamma K w := by
  unfold InductionBudget KPWeightedInductionBudget
  refine Finset.sum_le_sum ?_
  intro S hS
  exact absFamilyWeight_le_kpWeightedFamilyWeight K w hw_ge_one S

/-- Weighted compatible-family majorant implies the native one when `w ≥ 1`.
0 sorrys. -/
theorem compatibleFamilyMajorant_of_kpWeighted
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L) (w : KPPolymerWeight d L) (B : ℝ)
    (hw_ge_one : KPWeightGeOne d L w)
    (hweighted : KPWeightedCompatibleFamilyMajorant Gamma K w B) :
    CompatibleFamilyMajorant Gamma K B := by
  unfold CompatibleFamilyMajorant KPWeightedCompatibleFamilyMajorant at *
  exact le_trans
    (Finset.sum_le_sum (fun S hS =>
      absFamilyWeight_le_kpWeightedFamilyWeight K w hw_ge_one S))
    hweighted

/-- Weighted compatible-family majorant implies the native small-activity
budget. 0 sorrys. -/
theorem smallActivityBudget_of_kpWeighted
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L) (w : KPPolymerWeight d L) (B : ℝ)
    (hw_ge_one : KPWeightGeOne d L w)
    (hweighted : KPWeightedCompatibleFamilyMajorant Gamma K w B) :
    SmallActivityBudget Gamma K B := by
  exact compatibleFamilyMajorant_implies_smallActivityBudget
    Gamma K B
    (compatibleFamilyMajorant_of_kpWeighted Gamma K w B hw_ge_one hweighted)

/-- Weighted compatible-family majorant implies the native partition-function
deviation bound. 0 sorrys. -/
theorem abs_Z_sub_one_le_of_kpWeightedMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L) (w : KPPolymerWeight d L) (B : ℝ)
    (hw_ge_one : KPWeightGeOne d L w)
    (hweighted : KPWeightedCompatibleFamilyMajorant Gamma K w B) :
    |polymerPartitionFunction Gamma K - 1| ≤ B := by
  exact abs_Z_sub_one_le_of_majorant
    Gamma K B
    (compatibleFamilyMajorant_of_kpWeighted Gamma K w B hw_ge_one hweighted)

/-! ## Conservative exponential-size-weight specialization -/

/-- Exponential-size-weight majorant implies the native partition-function
deviation bound, assuming its `w ≥ 1` fact explicitly. 0 sorrys. -/
theorem abs_Z_sub_one_le_of_kpExpSizeWeightMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L) (a B : ℝ)
    (hw_ge_one : KPWeightGeOne d L (kpExpSizeWeight a d L))
    (hweighted : KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d L) B) :
    |polymerPartitionFunction Gamma K - 1| ≤ B := by
  exact abs_Z_sub_one_le_of_kpWeightedMajorant
    Gamma K (kpExpSizeWeight a d L) B hw_ge_one hweighted

/-- Scale-specialized exponential-size-weight majorant implies the native
partition-function deviation bound, assuming its `w ≥ 1` fact explicitly.
0 sorrys. -/
theorem abs_Z_sub_one_le_of_kpExpSizeWeightMajorant_scale
    {d k : ℕ}
    (Gamma : Finset (Polymer d (Int.ofNat k)))
    (K : Activity d (Int.ofNat k)) (a B : ℝ)
    (hw_ge_one : KPWeightGeOne d (Int.ofNat k) (kpExpSizeWeight a d (Int.ofNat k)))
    (hweighted :
      KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d (Int.ofNat k)) B) :
    |polymerPartitionFunction Gamma K - 1| ≤ B := by
  exact abs_Z_sub_one_le_of_kpExpSizeWeightMajorant
    (d := d) (L := Int.ofNat k) Gamma K a B hw_ge_one hweighted

end

end YangMills.ClayCore

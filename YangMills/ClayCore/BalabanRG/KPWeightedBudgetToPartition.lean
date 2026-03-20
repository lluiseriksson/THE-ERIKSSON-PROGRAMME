import Mathlib
import YangMills.ClayCore.BalabanRG.KPWeightedBudgetInterface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPWeightedBudgetToPartition — (v1.0.17-alpha repair)

Bridge from weighted KP-family budgets back to the native partition-function
control layer.

Conservative design:
- compare native absolute family weights with weighted family weights under
  the explicit hypothesis `1 ≤ w(X)`,
- deduce native `CompatibleFamilyMajorant`,
- recover `SmallActivityBudget`,
- recover `|Z - 1| ≤ B`,
- specialize automatically to the exponential polymer-size KP weight.
-/

noncomputable section

/-- Pointwise lower bound `1 ≤ w` implies pointwise nonnegativity. -/
theorem kpWeightNonneg_of_ge_one
    {d : ℕ} {L : ℤ}
    {w : KPWeightedActivity d L}
    (hge : KPWeightGeOne d L w) :
    KPWeightNonneg d L w := by
  intro X
  linarith [hge X]

/-- Nonnegativity of the weighted family weight. -/
theorem kpWeightedFamilyWeight_nonneg
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (hw : KPWeightNonneg d L w)
    (S : Finset (Polymer d L)) :
    0 ≤ kpWeightedFamilyWeight K w S := by
  unfold kpWeightedFamilyWeight
  exact Finset.prod_nonneg (by
    intro X hX
    exact mul_nonneg (abs_nonneg (K X)) (hw X))

/-- Native absolute family weight is bounded by the weighted family weight when
`1 ≤ w(X)` pointwise. -/
theorem absFamilyWeight_le_kpWeightedFamilyWeight_of_ge_one
    {d : ℕ} {L : ℤ}
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (hge : KPWeightGeOne d L w)
    (S : Finset (Polymer d L)) :
    absFamilyWeight K S ≤ kpWeightedFamilyWeight K w S := by
  classical
  have hw : KPWeightNonneg d L w := kpWeightNonneg_of_ge_one hge
  induction S using Finset.induction_on with
  | empty =>
      simp [absFamilyWeight, kpWeightedFamilyWeight]
  | @insert X S hX ih =>
      have hXle : |K X| ≤ |K X| * w X := by
        simpa [one_mul] using
          (mul_le_mul_of_nonneg_left (hge X) (abs_nonneg (K X)))
      have hS_nonneg : 0 ≤ absFamilyWeight K S := by
        unfold absFamilyWeight
        exact Finset.prod_nonneg (by
          intro Y hY
          exact abs_nonneg (K Y))
      have hW_nonneg : 0 ≤ |K X| * w X := by
        exact mul_nonneg (abs_nonneg (K X)) (hw X)
      simp [absFamilyWeight, kpWeightedFamilyWeight, Finset.prod_insert, hX]
      exact mul_le_mul hXle ih hS_nonneg hW_nonneg

/-- Weighted compatible-family majorant implies the native compatible-family
majorant under the explicit hypothesis `1 ≤ w(X)`. -/
theorem compatibleFamilyMajorant_of_kpWeightedMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B) :
    CompatibleFamilyMajorant Gamma K B := by
  unfold KPWeightedCompatibleFamilyMajorant CompatibleFamilyMajorant at *
  have hsum :
      ∑ S ∈ (compatibleSubfamilies Gamma).erase ∅, absFamilyWeight K S
        ≤
      ∑ S ∈ (compatibleSubfamilies Gamma).erase ∅, kpWeightedFamilyWeight K w S := by
    refine Finset.sum_le_sum ?_
    intro S hS
    exact absFamilyWeight_le_kpWeightedFamilyWeight_of_ge_one K w hge S
  exact le_trans hsum hB

/-- Weighted compatible-family majorant implies native `SmallActivityBudget`
under the explicit hypothesis `1 ≤ w(X)`. -/
theorem smallActivityBudget_of_kpWeightedMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B) :
    SmallActivityBudget Gamma K B := by
  exact compatibleFamilyMajorant_implies_smallActivityBudget
    Gamma K B
    (compatibleFamilyMajorant_of_kpWeightedMajorant Gamma K w B hge hB)

/-- Weighted compatible-family majorant implies the native partition-function
bound `|Z - 1| ≤ B` under the explicit hypothesis `1 ≤ w(X)`. -/
theorem abs_Z_sub_one_le_of_kpWeightedMajorant
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K w B) :
    |polymerPartitionFunction Gamma K - 1| ≤ B := by
  exact abs_Z_sub_one_le_of_majorant
    Gamma K B
    (compatibleFamilyMajorant_of_kpWeightedMajorant Gamma K w B hge hB)

/-- A weighted induction-budget bound implies native `SmallActivityBudget`
under the explicit hypothesis `1 ≤ w(X)`. -/
theorem smallActivityBudget_of_kpWeightedBudget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B) :
    SmallActivityBudget Gamma K B := by
  have hmajor :
      KPWeightedCompatibleFamilyMajorant Gamma K w
        (KPWeightedInductionBudget Gamma K w) :=
    kpWeightedInductionBudget_is_majorant Gamma K w
  have hsmall :
      SmallActivityBudget Gamma K (KPWeightedInductionBudget Gamma K w) :=
    smallActivityBudget_of_kpWeightedMajorant
      Gamma K w (KPWeightedInductionBudget Gamma K w) hge hmajor
  exact le_trans hsmall hB

/-- A weighted induction-budget bound implies the native partition-function
bound `|Z - 1| ≤ B` under the explicit hypothesis `1 ≤ w(X)`. -/
theorem abs_Z_sub_one_le_of_kpWeightedBudget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B) :
    |polymerPartitionFunction Gamma K - 1| ≤ B := by
  exact abs_polymerPartitionFunction_sub_one_le
    Gamma K B
    (smallActivityBudget_of_kpWeightedBudget Gamma K w B hge hB)

/-! ## Automatic specialization: exponential polymer-size KP weight -/

/-- Exponential polymer-size weighted majorant implies native
`SmallActivityBudget`. -/
theorem smallActivityBudget_of_kpWeightedMajorant_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d L) B) :
    SmallActivityBudget Gamma K B := by
  exact smallActivityBudget_of_kpWeightedMajorant
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB

/-- Exponential polymer-size weighted majorant implies the native
partition-function bound `|Z - 1| ≤ B`. -/
theorem abs_Z_sub_one_le_of_kpWeightedMajorant_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedCompatibleFamilyMajorant Gamma K (kpExpSizeWeight a d L) B) :
    |polymerPartitionFunction Gamma K - 1| ≤ B := by
  exact abs_Z_sub_one_le_of_kpWeightedMajorant
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB

/-- Exponential polymer-size weighted induction-budget bound implies native
`SmallActivityBudget`. -/
theorem smallActivityBudget_of_kpWeightedBudget_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B) :
    SmallActivityBudget Gamma K B := by
  exact smallActivityBudget_of_kpWeightedBudget
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB

/-- Exponential polymer-size weighted induction-budget bound implies the native
partition-function bound `|Z - 1| ≤ B`. -/
theorem abs_Z_sub_one_le_of_kpWeightedBudget_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B) :
    |polymerPartitionFunction Gamma K - 1| ≤ B := by
  exact abs_Z_sub_one_le_of_kpWeightedBudget
    Gamma K (kpExpSizeWeight a d L) B
    (kpExpSizeWeight_ge_one_interface a ha) hB

end

end YangMills.ClayCore

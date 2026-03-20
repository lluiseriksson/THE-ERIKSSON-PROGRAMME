import Mathlib
import YangMills.ClayCore.BalabanRG.KPWeightedToLSIBridge
import YangMills.ClayCore.BalabanRG.FreeEnergyControlReduction

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedFreeEnergyControlReduction — Layer 7W

This file packages the new weighted KP lane as a consumer-facing reduction layer.

Purpose:
* expose the weighted free-energy control as a named reduction target,
* connect weighted free-energy control to the existing native
  `FreeEnergyControlAtScale` interface under an explicit comparison hypothesis,
* provide automatic specialization to the exponential polymer-size weight.

This does **not** claim the full RG / DLR-LSI closure.
It only says: once a weighted budget is available, the free-energy layer can be
exported in the same language already used by the native reduction files.
-/

noncomputable section

/-- Consumer-facing weighted free-energy control at a fixed scale. -/
def WeightedFreeEnergyControlAtScale
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ) : Prop :=
  WeightedFreeEnergyReadyAtScale Gamma K w B

/-- Two-sided weighted free-energy control at a fixed scale. -/
def WeightedFreeEnergyControlTwoSidedAtScale
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ) : Prop :=
  WeightedFreeEnergyTwoSidedAtScale Gamma K w B

/-- A weighted induction-budget bound with `B < 1` discharges the weighted
free-energy control layer. -/
theorem weighted_freeEnergyControlAtScale_of_budget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hsmall : B < 1) :
    WeightedFreeEnergyControlAtScale Gamma K w B := by
  dsimp [WeightedFreeEnergyControlAtScale]
  exact weighted_clayCore_free_energy_ready Gamma K w B hge hB hsmall

/-- `log 2` threshold variant of weighted free-energy control. -/
theorem weighted_freeEnergyControlAtScale_of_lt_log2
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (t : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ Real.exp t - 1)
    (ht : t < Real.log 2) :
    WeightedFreeEnergyControlAtScale Gamma K w (Real.exp t - 1) := by
  dsimp [WeightedFreeEnergyControlAtScale]
  exact weighted_clayCore_free_energy_ready_of_lt_log2 Gamma K w t hge hB ht

/-- A weighted induction-budget bound with `B ≤ 1/2` discharges the two-sided
free-energy control layer. -/
theorem weighted_freeEnergyControlTwoSidedAtScale_of_budget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hhalf : B ≤ 1 / 2) :
    WeightedFreeEnergyControlTwoSidedAtScale Gamma K w B := by
  dsimp [WeightedFreeEnergyControlTwoSidedAtScale]
  exact kpWeightedBudget_log_free_energy_bound Gamma K w B hge hB hhalf

/-- Weighted free-energy control implies positivity of the partition function. -/
theorem partitionFunction_pos_of_weighted_freeEnergyControl
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (h : WeightedFreeEnergyControlAtScale Gamma K w B) :
    0 < polymerPartitionFunction Gamma K := by
  exact h.1

/-- Weighted free-energy control implies the expected one-sided log bound. -/
theorem log_partitionFunction_le_of_weighted_freeEnergyControl
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (h : WeightedFreeEnergyControlAtScale Gamma K w B) :
    Real.log (polymerPartitionFunction Gamma K) ≤ B := by
  exact h.2

/-- Key adapter:
weighted free-energy control upgrades to the existing native
`FreeEnergyControlAtScale` interface once the weighted bound is known to sit
below the native target budget.

This is the honest interface contract between the weighted route and the older
native reduction layer.
-/
theorem freeEnergyControlAtScale_of_weighted
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hready : WeightedFreeEnergyControlAtScale Gamma K w B)
    (hcompare : B ≤ Real.exp (theoreticalBudget Gamma K a) - 1) :
    FreeEnergyControlAtScale Gamma K a := by
  rcases hready with ⟨hpos, hlog⟩
  exact ⟨hpos, le_trans hlog hcompare⟩

/-- Budget-level adapter:
a weighted induction-budget bound plus a comparison with the native target
budget discharges the existing native free-energy layer. -/
theorem freeEnergyControlAtScale_of_weighted_budget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (w : KPWeightedActivity d L)
    (B : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ B)
    (hsmall : B < 1)
    (hcompare : B ≤ Real.exp (theoreticalBudget Gamma K a) - 1) :
    FreeEnergyControlAtScale Gamma K a := by
  exact freeEnergyControlAtScale_of_weighted
    Gamma K a w B
    (weighted_freeEnergyControlAtScale_of_budget Gamma K w B hge hB hsmall)
    hcompare

/-- `log 2` threshold adapter from the weighted lane to the existing native
free-energy layer. -/
theorem freeEnergyControlAtScale_of_weighted_budget_lt_log2
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (w : KPWeightedActivity d L)
    (t : ℝ)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w ≤ Real.exp t - 1)
    (ht : t < Real.log 2)
    (hcompare : Real.exp t - 1 ≤ Real.exp (theoreticalBudget Gamma K a) - 1) :
    FreeEnergyControlAtScale Gamma K a := by
  exact freeEnergyControlAtScale_of_weighted
    Gamma K a w (Real.exp t - 1)
    (weighted_freeEnergyControlAtScale_of_lt_log2 Gamma K w t hge hB ht)
    hcompare

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- Consumer-facing weighted free-energy control for the exponential
polymer-size route. -/
def ExpSizeWeightFreeEnergyControlAtScale
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ) : Prop :=
  WeightedFreeEnergyControlAtScale Gamma K (kpExpSizeWeight a d L) B

/-- Two-sided version for the exponential polymer-size route. -/
def ExpSizeWeightFreeEnergyControlTwoSidedAtScale
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ) : Prop :=
  WeightedFreeEnergyControlTwoSidedAtScale Gamma K (kpExpSizeWeight a d L) B

/-- Exponential size-weight budget discharges the weighted free-energy layer. -/
theorem expSizeWeight_freeEnergyControlAtScale_of_budget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hsmall : B < 1) :
    ExpSizeWeightFreeEnergyControlAtScale Gamma K a B := by
  dsimp [ExpSizeWeightFreeEnergyControlAtScale, WeightedFreeEnergyControlAtScale]
  exact weighted_clayCore_free_energy_ready_expSizeWeight Gamma K a B ha hB hsmall

/-- `log 2` threshold version for the exponential polymer-size route. -/
theorem expSizeWeight_freeEnergyControlAtScale_of_lt_log2
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (t : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L)
      ≤ Real.exp t - 1)
    (ht : t < Real.log 2) :
    ExpSizeWeightFreeEnergyControlAtScale Gamma K a (Real.exp t - 1) := by
  dsimp [ExpSizeWeightFreeEnergyControlAtScale, WeightedFreeEnergyControlAtScale]
  exact weighted_clayCore_free_energy_ready_expSizeWeight_of_lt_log2 Gamma K a t ha hB ht

/-- Exponential size-weight budget yields the two-sided free-energy bound. -/
theorem expSizeWeight_freeEnergyControlTwoSidedAtScale_of_budget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hhalf : B ≤ 1 / 2) :
    ExpSizeWeightFreeEnergyControlTwoSidedAtScale Gamma K a B := by
  dsimp [ExpSizeWeightFreeEnergyControlTwoSidedAtScale,
    WeightedFreeEnergyControlTwoSidedAtScale]
  exact kpWeightedBudget_log_free_energy_bound_expSizeWeight Gamma K a B ha hB hhalf

/-- Exponential size-weight control upgrades to the native free-energy layer
under an explicit comparison with the native target budget. -/
theorem freeEnergyControlAtScale_of_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (B : ℝ)
    (hready : ExpSizeWeightFreeEnergyControlAtScale Gamma K a_weight B)
    (hcompare : B ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1) :
    FreeEnergyControlAtScale Gamma K a_native := by
  exact freeEnergyControlAtScale_of_weighted
    Gamma K a_native (kpExpSizeWeight a_weight d L) B hready hcompare

/-- Budget-level exponential size-weight adapter to the native
`FreeEnergyControlAtScale` interface. -/
theorem freeEnergyControlAtScale_of_expSizeWeight_budget
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (B : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L) ≤ B)
    (hsmall : B < 1)
    (hcompare : B ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1) :
    FreeEnergyControlAtScale Gamma K a_native := by
  exact freeEnergyControlAtScale_of_expSizeWeight
    Gamma K a_native a_weight B
    (expSizeWeight_freeEnergyControlAtScale_of_budget
      Gamma K a_weight B ha hB hsmall)
    hcompare

end

end YangMills.ClayCore

import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedFreeEnergyControlReduction
import YangMills.ClayCore.BalabanRG.KPToLSIBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedKPToNativeFreeEnergy — Layer 7W+

Thin mirror of the native KP → free-energy bridge at the *native* target budget.

Purpose:
* specialize the comparison hypothesis in `WeightedFreeEnergyControlReduction`
  to the canonical native target `exp(theoreticalBudget) - 1`,
* expose weighted analogues of the native KP bridge theorems with the same
  consumer-facing shape,
* provide automatic specialization to the exponential polymer-size route.

This does not add new mathematics. It removes friction:
the weighted lane can now be consumed directly at the native target budget.
-/

noncomputable section

/-- Weighted budget control at the native target budget implies the existing
native `FreeEnergyControlAtScale` interface. -/
theorem weighted_clayCore_free_energy_ready_at_native_target
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (w : KPWeightedActivity d L)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    FreeEnergyControlAtScale Gamma K a := by
  exact freeEnergyControlAtScale_of_weighted_budget_lt_log2
    Gamma K a w (theoreticalBudget Gamma K a)
    hge hB hb le_rfl

/-- Positivity of the partition function at the native target budget via the
weighted route. -/
theorem weighted_partition_function_pos_at_native_target
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (w : KPWeightedActivity d L)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    0 < polymerPartitionFunction Gamma K := by
  exact (weighted_clayCore_free_energy_ready_at_native_target
    Gamma K a w hge hB hb).1

/-- One-sided free-energy bound at the native target budget via the
weighted route. -/
theorem weighted_log_partitionFunction_le_at_native_target
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (w : KPWeightedActivity d L)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
  exact (weighted_clayCore_free_energy_ready_at_native_target
    Gamma K a w hge hB hb).2

/-- Two-sided log-free-energy bound at the native target budget via the
weighted route. This is the weighted mirror of
`kpOnGamma_log_free_energy_bound`. -/
theorem weighted_log_free_energy_bound_at_native_target
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (w : KPWeightedActivity d L)
    (hge : KPWeightGeOne d L w)
    (hB : KPWeightedInductionBudget Gamma K w
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1)
    (hhalf : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  simpa [WeightedFreeEnergyControlTwoSidedAtScale, WeightedFreeEnergyTwoSidedAtScale]
    using
      (weighted_freeEnergyControlTwoSidedAtScale_of_budget
        Gamma K w (Real.exp (theoreticalBudget Gamma K a) - 1)
        hge hB hhalf)

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- Exponential size-weight route at the native target budget discharges the
existing native `FreeEnergyControlAtScale` interface. -/
theorem expSizeWeight_clayCore_free_energy_ready_at_native_target
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2) :
    FreeEnergyControlAtScale Gamma K a_native := by
  exact weighted_clayCore_free_energy_ready_at_native_target
    Gamma K a_native (kpExpSizeWeight a_weight d L)
    (kpExpSizeWeight_ge_one_interface a_weight ha) hB hb

/-- Exponential size-weight positivity at the native target budget. -/
theorem expSizeWeight_partition_function_pos_at_native_target
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2) :
    0 < polymerPartitionFunction Gamma K := by
  exact (expSizeWeight_clayCore_free_energy_ready_at_native_target
    Gamma K a_native a_weight ha hB hb).1

/-- Exponential size-weight one-sided free-energy bound at the native target
budget. -/
theorem expSizeWeight_log_partitionFunction_le_at_native_target
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2) :
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1 := by
  exact (expSizeWeight_clayCore_free_energy_ready_at_native_target
    Gamma K a_native a_weight ha hB hb).2

/-- Exponential size-weight two-sided log-free-energy bound at the native
target budget. -/
theorem expSizeWeight_log_free_energy_bound_at_native_target
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hhalf : Real.exp (theoreticalBudget Gamma K a_native) - 1 ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a_native) - 1) := by
  exact weighted_log_free_energy_bound_at_native_target
    Gamma K a_native (kpExpSizeWeight a_weight d L)
    (kpExpSizeWeight_ge_one_interface a_weight ha) hB hhalf

end

end YangMills.ClayCore

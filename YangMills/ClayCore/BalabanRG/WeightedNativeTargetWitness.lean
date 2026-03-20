import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedKPToNativeFreeEnergy

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedNativeTargetWitness — Layer 7W++

Reusable witness packaging for the weighted route at the native target budget.

Purpose:
* bundle the three pieces of data that are repeatedly needed upstairs:
  a weight `w`, the lower bound `1 ≤ w`, and the weighted budget bound at the
  native target `exp(theoreticalBudget) - 1`,
* let higher layers consume the weighted route without repeating plumbing,
* provide automatic specialization to the exponential polymer-size route.

This does not add new mathematics.
It packages the already-green weighted native-target bridge as a reusable object.
-/

noncomputable section

/-- A reusable witness that the weighted route reaches the native target budget. -/
structure WeightedNativeTargetWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ) where
  w : KPWeightedActivity d L
  ge_one : KPWeightGeOne d L w
  budget_le_native :
    KPWeightedInductionBudget Gamma K w
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1

/-- A witness immediately discharges the native free-energy control interface,
provided the native target budget lies below `log 2`. -/
theorem freeEnergyControlAtScale_of_weightedNativeTargetWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedNativeTargetWitness Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    FreeEnergyControlAtScale Gamma K a := by
  exact weighted_clayCore_free_energy_ready_at_native_target
    Gamma K a hwit.w hwit.ge_one hwit.budget_le_native hb

/-- Positivity of the partition function from a weighted native-target witness. -/
theorem partitionFunction_pos_of_weightedNativeTargetWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedNativeTargetWitness Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    0 < polymerPartitionFunction Gamma K := by
  exact (freeEnergyControlAtScale_of_weightedNativeTargetWitness
    Gamma K a hwit hb).1

/-- One-sided free-energy bound from a weighted native-target witness. -/
theorem log_partitionFunction_le_of_weightedNativeTargetWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedNativeTargetWitness Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
  exact (freeEnergyControlAtScale_of_weightedNativeTargetWitness
    Gamma K a hwit hb).2

/-- Two-sided log-free-energy bound from a weighted native-target witness. -/
theorem log_free_energy_bound_of_weightedNativeTargetWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedNativeTargetWitness Gamma K a)
    (hhalf : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  exact weighted_log_free_energy_bound_at_native_target
    Gamma K a hwit.w hwit.ge_one hwit.budget_le_native hhalf

/-- A witness gives the consumer-facing weighted two-sided free-energy control
at the native target budget. -/
theorem weightedTwoSidedControl_of_weightedNativeTargetWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedNativeTargetWitness Gamma K a)
    (hhalf : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1 / 2) :
    WeightedFreeEnergyControlTwoSidedAtScale
      Gamma K hwit.w (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  dsimp [WeightedFreeEnergyControlTwoSidedAtScale, WeightedFreeEnergyTwoSidedAtScale]
  exact weighted_freeEnergyControlTwoSidedAtScale_of_budget
    Gamma K hwit.w (Real.exp (theoreticalBudget Gamma K a) - 1)
    hwit.ge_one hwit.budget_le_native hhalf

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- The exponential polymer-size route produces a canonical witness at the
native target budget. -/
def expSizeWeightNativeTargetWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1) :
    WeightedNativeTargetWitness Gamma K a_native where
  w := kpExpSizeWeight a_weight d L
  ge_one := kpExpSizeWeight_ge_one_interface a_weight ha
  budget_le_native := hB

/-- Exponential size-weight witness discharges the native free-energy control
interface. -/
theorem freeEnergyControlAtScale_of_expSizeWeightNativeTargetWitness
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
  exact freeEnergyControlAtScale_of_weightedNativeTargetWitness
    Gamma K a_native
    (expSizeWeightNativeTargetWitness
      Gamma K a_native a_weight ha hB)
    hb

/-- Exponential size-weight witness implies positivity of the partition
function at the native target budget. -/
theorem partitionFunction_pos_of_expSizeWeightNativeTargetWitness
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
  exact (freeEnergyControlAtScale_of_expSizeWeightNativeTargetWitness
    Gamma K a_native a_weight ha hB hb).1

/-- Exponential size-weight witness implies the one-sided native-target
free-energy bound. -/
theorem log_partitionFunction_le_of_expSizeWeightNativeTargetWitness
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
  exact (freeEnergyControlAtScale_of_expSizeWeightNativeTargetWitness
    Gamma K a_native a_weight ha hB hb).2

/-- Exponential size-weight witness implies the two-sided native-target
free-energy bound. -/
theorem log_free_energy_bound_of_expSizeWeightNativeTargetWitness
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
  exact log_free_energy_bound_of_weightedNativeTargetWitness
    Gamma K a_native
    (expSizeWeightNativeTargetWitness
      Gamma K a_native a_weight ha hB)
    hhalf

end

end YangMills.ClayCore

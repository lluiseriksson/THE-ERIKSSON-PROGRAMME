import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedNativeTargetWitness
import YangMills.ClayCore.BalabanRG.PhysicalWitnessToDirichletBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedPhysicalWitness — Layer 8W

Reusable "physical witness" packaging for the weighted route.

Purpose:
* bundle the weighted native-target witness together with the smallness
  condition `theoreticalBudget < log 2`,
* export the native `FreeEnergyControlAtScale` interface from a single object,
* expose positivity / one-sided / two-sided free-energy consequences,
* provide automatic specialization to the exponential polymer-size route.

This does not claim full DLR-LSI closure.
It packages the already-green weighted native-target lane as an upstairs-ready
witness object.
-/

noncomputable section

/-- A weighted physical witness at scale packages:
1. a weighted native-target witness,
2. the native smallness threshold `theoreticalBudget < log 2`.
-/
structure WeightedPhysicalWitnessAtScale
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ) where
  nativeWitness : WeightedNativeTargetWitness Gamma K a
  small_target : theoreticalBudget Gamma K a < Real.log 2

/-- A weighted physical witness immediately discharges the native
free-energy control interface. -/
theorem freeEnergyControlAtScale_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    FreeEnergyControlAtScale Gamma K a := by
  exact freeEnergyControlAtScale_of_weightedNativeTargetWitness
    Gamma K a hwit.nativeWitness hwit.small_target

/-- Positivity of the partition function from a weighted physical witness. -/
theorem partitionFunction_pos_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    0 < polymerPartitionFunction Gamma K := by
  exact (freeEnergyControlAtScale_of_weightedPhysicalWitness
    Gamma K a hwit).1

/-- One-sided free-energy bound from a weighted physical witness. -/
theorem log_partitionFunction_le_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
  exact (freeEnergyControlAtScale_of_weightedPhysicalWitness
    Gamma K a hwit).2

/-- Two-sided log-free-energy bound from a weighted physical witness,
under the standard half-budget hypothesis. -/
theorem log_free_energy_bound_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a)
    (hhalf : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  exact log_free_energy_bound_of_weightedNativeTargetWitness
    Gamma K a hwit.nativeWitness hhalf

/-- Consumer-facing weighted two-sided control at the native target budget. -/
theorem weightedTwoSidedControl_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a)
    (hhalf : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1 / 2) :
    WeightedFreeEnergyControlTwoSidedAtScale
      Gamma K hwit.nativeWitness.w
      (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  exact weightedTwoSidedControl_of_weightedNativeTargetWitness
    Gamma K a hwit.nativeWitness hhalf

/-- A weighted physical witness also yields the reusable weighted one-sided
control object at the native target budget. -/
theorem weightedOneSidedControl_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    WeightedFreeEnergyControlAtScale
      Gamma K hwit.nativeWitness.w
      (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  dsimp [WeightedFreeEnergyControlAtScale, WeightedFreeEnergyReadyAtScale]
  constructor
  · exact partitionFunction_pos_of_weightedPhysicalWitness Gamma K a hwit
  · exact log_partitionFunction_le_of_weightedPhysicalWitness Gamma K a hwit

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- The exponential polymer-size route gives a canonical weighted physical
witness. -/
def expSizeWeightPhysicalWitnessAtScale
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2) :
    WeightedPhysicalWitnessAtScale Gamma K a_native where
  nativeWitness := expSizeWeightNativeTargetWitness
    Gamma K a_native a_weight ha hB
  small_target := hb

/-- Exponential size-weight physical witness discharges the native
free-energy control interface. -/
theorem freeEnergyControlAtScale_of_expSizeWeightPhysicalWitness
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
  exact freeEnergyControlAtScale_of_weightedPhysicalWitness
    Gamma K a_native
    (expSizeWeightPhysicalWitnessAtScale
      Gamma K a_native a_weight ha hB hb)

/-- Exponential size-weight physical witness implies positivity. -/
theorem partitionFunction_pos_of_expSizeWeightPhysicalWitness
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
  exact (freeEnergyControlAtScale_of_expSizeWeightPhysicalWitness
    Gamma K a_native a_weight ha hB hb).1

/-- Exponential size-weight physical witness implies the one-sided free-energy
bound at the native target budget. -/
theorem log_partitionFunction_le_of_expSizeWeightPhysicalWitness
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
  exact (freeEnergyControlAtScale_of_expSizeWeightPhysicalWitness
    Gamma K a_native a_weight ha hB hb).2

/-- Exponential size-weight physical witness implies the two-sided free-energy
bound at the native target budget. -/
theorem log_free_energy_bound_of_expSizeWeightPhysicalWitness
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hhalf : Real.exp (theoreticalBudget Gamma K a_native) - 1 ≤ 1 / 2)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a_native) - 1) := by
  exact log_free_energy_bound_of_weightedPhysicalWitness
    Gamma K a_native
    (expSizeWeightPhysicalWitnessAtScale
      Gamma K a_native a_weight ha hB hb)
    hhalf

end

end YangMills.ClayCore

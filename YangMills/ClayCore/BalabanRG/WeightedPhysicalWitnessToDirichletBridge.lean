import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedPhysicalWitness
import YangMills.ClayCore.BalabanRG.PhysicalWitnessToDirichletBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedPhysicalWitnessToDirichletBridge — Layer 9W

Packages the weighted physical witness together with the already-discharged
abstract Dirichlet/LSI bridge targets.

Honest scope:
* this file does **not** prove that the weighted route itself establishes the
  bridge hypotheses `PhysicalContractionRealized`, `PhysicalPoincareRealized`,
  `PhysicalLSIRealized`;
* instead, it combines:
  1. the new weighted free-energy witness lane, and
  2. the existing abstract bridge layer already discharged in
     `PhysicalWitnessToDirichletBridge`.

This yields a single upstairs-ready package carrying:
* finite-volume free-energy control from the weighted route, and
* global `ClayCoreLSI` from the abstract physical bridge.
-/

noncomputable section

/-- A combined package: weighted physical witness + abstract Dirichlet bridge. -/
structure WeightedDirichletBridgePackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ) where
  weightedWitness : WeightedPhysicalWitnessAtScale Gamma K a
  dirichletBridge : PhysicalWitnessBridge d N_c

/-- The weighted half of the package discharges native free-energy control. -/
theorem freeEnergyControlAtScale_of_weightedDirichletBridgePackage
    {d : ℕ} {L : ℤ} {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedDirichletBridgePackage N_c Gamma K a) :
    FreeEnergyControlAtScale Gamma K a := by
  exact freeEnergyControlAtScale_of_weightedPhysicalWitness
    Gamma K a pkg.weightedWitness

/-- The abstract bridge half of the package closes the uniform-LSI gap. -/
theorem clayCoreLSI_of_weightedDirichletBridgePackage
    {d : ℕ} {L : ℤ} {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedDirichletBridgePackage N_c Gamma K a) :
    ∃ c > 0, ClayCoreLSI d N_c c := by
  exact physical_bridge_closes_lsi_gap d N_c pkg.dirichletBridge

/-- Summary theorem: the combined package is enough to expose both the
finite-volume free-energy statement and the global uniform-LSI statement. -/
theorem weightedDirichletBridgePackage_ready
    {d : ℕ} {L : ℤ} {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedDirichletBridgePackage N_c Gamma K a) :
    FreeEnergyControlAtScale Gamma K a ∧
      ∃ c > 0, ClayCoreLSI d N_c c := by
  constructor
  · exact freeEnergyControlAtScale_of_weightedDirichletBridgePackage
      Gamma K a pkg
  · exact clayCoreLSI_of_weightedDirichletBridgePackage
      Gamma K a pkg

/-- Positivity of the partition function from the combined package. -/
theorem partitionFunction_pos_of_weightedDirichletBridgePackage
    {d : ℕ} {L : ℤ} {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedDirichletBridgePackage N_c Gamma K a) :
    0 < polymerPartitionFunction Gamma K := by
  exact (freeEnergyControlAtScale_of_weightedDirichletBridgePackage
    Gamma K a pkg).1

/-- One-sided free-energy bound from the combined package. -/
theorem log_partitionFunction_le_of_weightedDirichletBridgePackage
    {d : ℕ} {L : ℤ} {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedDirichletBridgePackage N_c Gamma K a) :
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
  exact (freeEnergyControlAtScale_of_weightedDirichletBridgePackage
    Gamma K a pkg).2

/-- Two-sided free-energy bound from the combined package. -/
theorem log_free_energy_bound_of_weightedDirichletBridgePackage
    {d : ℕ} {L : ℤ} {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedDirichletBridgePackage N_c Gamma K a)
    (hhalf : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  exact log_free_energy_bound_of_weightedPhysicalWitness
    Gamma K a pkg.weightedWitness hhalf

/-! ## Canonical package using the already-discharged abstract bridge targets -/

/-- Canonical combined package:
weighted witness + `abstract_rates_satisfy_bridge_targets`. -/
def weightedDirichletBridgePackage_of_abstract_rates
    {d : ℕ} {L : ℤ} (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    WeightedDirichletBridgePackage N_c Gamma K a where
  weightedWitness := hwit
  dirichletBridge := abstract_rates_satisfy_bridge_targets d N_c

/-- A weighted physical witness alone already plugs into the abstract bridge
targets currently formalized in the repo. -/
theorem weightedPhysicalWitness_closes_lsi_gap
    {d : ℕ} {L : ℤ} (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    ∃ c > 0, ClayCoreLSI d N_c c := by
  exact clayCoreLSI_of_weightedDirichletBridgePackage
    Gamma K a
    (weightedDirichletBridgePackage_of_abstract_rates
      N_c Gamma K a hwit)

/-- Weighted physical witness + abstract bridge targets:
the full upstairs-ready pair. -/
theorem weightedPhysicalWitness_ready_for_lsi
    {d : ℕ} {L : ℤ} (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    FreeEnergyControlAtScale Gamma K a ∧
      ∃ c > 0, ClayCoreLSI d N_c c := by
  exact weightedDirichletBridgePackage_ready
    Gamma K a
    (weightedDirichletBridgePackage_of_abstract_rates
      N_c Gamma K a hwit)

/-- Two-sided free-energy control together with global LSI from a weighted
physical witness. -/
theorem weightedPhysicalWitness_twoSided_and_lsi
    {d : ℕ} {L : ℤ} (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a)
    (hhalf : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a) - 1) ∧
      ∃ c > 0, ClayCoreLSI d N_c c := by
  constructor
  · exact log_free_energy_bound_of_weightedPhysicalWitness
      Gamma K a hwit hhalf
  · exact weightedPhysicalWitness_closes_lsi_gap
      N_c Gamma K a hwit

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- Canonical exp-size-weight package into the abstract Dirichlet bridge. -/
def expSizeWeightDirichletBridgePackage_of_abstract_rates
    {d : ℕ} {L : ℤ} (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2) :
    WeightedDirichletBridgePackage N_c Gamma K a_native :=
  weightedDirichletBridgePackage_of_abstract_rates
    N_c Gamma K a_native
    (expSizeWeightPhysicalWitnessAtScale
      Gamma K a_native a_weight ha hB hb)

/-- Exp-size-weight route yields free-energy control together with global LSI. -/
theorem expSizeWeightPhysicalWitness_ready_for_lsi
    {d : ℕ} {L : ℤ} (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2) :
    FreeEnergyControlAtScale Gamma K a_native ∧
      ∃ c > 0, ClayCoreLSI d N_c c := by
  exact weightedDirichletBridgePackage_ready
    Gamma K a_native
    (expSizeWeightDirichletBridgePackage_of_abstract_rates
      N_c Gamma K a_native a_weight ha hB hb)

/-- Exp-size-weight route yields the two-sided free-energy bound together with
global LSI. -/
theorem expSizeWeightPhysicalWitness_twoSided_and_lsi
    {d : ℕ} {L : ℤ} (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2)
    (hhalf : Real.exp (theoreticalBudget Gamma K a_native) - 1 ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a_native) - 1) ∧
      ∃ c > 0, ClayCoreLSI d N_c c := by
  constructor
  · exact log_free_energy_bound_of_expSizeWeightPhysicalWitness
      Gamma K a_native a_weight ha hB hhalf hb
  · exact weightedPhysicalWitness_closes_lsi_gap
      N_c Gamma K a_native
      (expSizeWeightPhysicalWitnessAtScale
        Gamma K a_native a_weight ha hB hb)

end

end YangMills.ClayCore

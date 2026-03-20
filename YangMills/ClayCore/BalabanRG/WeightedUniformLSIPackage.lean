import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedPhysicalWitnessToDirichletBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedUniformLSIPackage — Layer 10W

Packages the weighted upstairs-ready lane with an explicit positive LSI constant.

Purpose:
* replace the existential output `∃ c > 0, ClayCoreLSI d N_c c` by a reusable
  structure carrying a chosen witness `c`,
* keep the weighted free-energy witness and the LSI witness together,
* expose standard consequences from a single object,
* provide automatic specialization to the exponential polymer-size route.

This does not add new mathematics.
It turns the already-green theorem
`weightedPhysicalWitness_ready_for_lsi`
into a more convenient consumer-facing package.
-/

noncomputable section

/-- A reusable package carrying both:
1. the weighted physical witness at scale,
2. an explicit positive LSI constant witness.
-/
structure WeightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ) where
  weightedWitness : WeightedPhysicalWitnessAtScale Gamma K a
  lsiConst : ℝ
  lsiConst_pos : 0 < lsiConst
  uniform_lsi : ClayCoreLSI d N_c lsiConst

/-- A weighted physical witness canonically yields a weighted uniform-LSI
package by choosing the LSI witness from the existing existential theorem. -/
def weightedUniformLSIPackage_of_physicalWitness
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    WeightedUniformLSIPackage N_c Gamma K a := by
  have hlsi : ∃ c > 0, ClayCoreLSI d N_c c :=
    weightedPhysicalWitness_closes_lsi_gap N_c Gamma K a hwit
  refine
    { weightedWitness := hwit
      lsiConst := Classical.choose hlsi
      lsiConst_pos := (Classical.choose_spec hlsi).1
      uniform_lsi := (Classical.choose_spec hlsi).2 }

/-- The package discharges native free-energy control. -/
theorem freeEnergyControlAtScale_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedUniformLSIPackage N_c Gamma K a) :
    FreeEnergyControlAtScale Gamma K a := by
  exact freeEnergyControlAtScale_of_weightedPhysicalWitness
    Gamma K a pkg.weightedWitness

/-- The package exposes an explicit positive LSI witness. -/
theorem explicit_uniform_lsi_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedUniformLSIPackage N_c Gamma K a) :
    ClayCoreLSI d N_c pkg.lsiConst := by
  exact pkg.uniform_lsi

/-- The package also exposes the existential LSI statement. -/
theorem clayCoreLSI_exists_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedUniformLSIPackage N_c Gamma K a) :
    ∃ c > 0, ClayCoreLSI d N_c c := by
  exact ⟨pkg.lsiConst, pkg.lsiConst_pos, pkg.uniform_lsi⟩

/-- Summary theorem: one package yields both free-energy control and an
explicit positive LSI witness. -/
theorem weightedUniformLSIPackage_ready
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedUniformLSIPackage N_c Gamma K a) :
    FreeEnergyControlAtScale Gamma K a ∧
      ClayCoreLSI d N_c pkg.lsiConst := by
  constructor
  · exact freeEnergyControlAtScale_of_weightedUniformLSIPackage
      Gamma K a pkg
  · exact pkg.uniform_lsi

/-- Positivity of the partition function from the package. -/
theorem partitionFunction_pos_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedUniformLSIPackage N_c Gamma K a) :
    0 < polymerPartitionFunction Gamma K := by
  exact (freeEnergyControlAtScale_of_weightedUniformLSIPackage
    Gamma K a pkg).1

/-- One-sided free-energy bound from the package. -/
theorem log_partitionFunction_le_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedUniformLSIPackage N_c Gamma K a) :
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
  exact (freeEnergyControlAtScale_of_weightedUniformLSIPackage
    Gamma K a pkg).2

/-- Two-sided free-energy bound from the package. -/
theorem log_free_energy_bound_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedUniformLSIPackage N_c Gamma K a)
    (hhalf : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1 / 2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  exact log_free_energy_bound_of_weightedPhysicalWitness
    Gamma K a pkg.weightedWitness hhalf

/-- The package exposes the weighted one-sided control object at the native
target budget. -/
theorem weightedOneSidedControl_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedUniformLSIPackage N_c Gamma K a) :
    WeightedFreeEnergyControlAtScale
      Gamma K pkg.weightedWitness.nativeWitness.w
      (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  exact weightedOneSidedControl_of_weightedPhysicalWitness
    Gamma K a pkg.weightedWitness

/-- The package exposes the weighted two-sided control object at the native
target budget. -/
theorem weightedTwoSidedControl_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedUniformLSIPackage N_c Gamma K a)
    (hhalf : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1 / 2) :
    WeightedFreeEnergyControlTwoSidedAtScale
      Gamma K pkg.weightedWitness.nativeWitness.w
      (Real.exp (theoreticalBudget Gamma K a) - 1) := by
  exact weightedTwoSidedControl_of_weightedPhysicalWitness
    Gamma K a pkg.weightedWitness hhalf

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- Canonical uniform-LSI package for the exponential polymer-size route. -/
def expSizeWeightUniformLSIPackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2) :
    WeightedUniformLSIPackage N_c Gamma K a_native :=
  weightedUniformLSIPackage_of_physicalWitness
    N_c Gamma K a_native
    (expSizeWeightPhysicalWitnessAtScale
      Gamma K a_native a_weight ha hB hb)

/-- Exp-size-weight route yields native free-energy control plus an explicit
positive LSI constant witness. -/
theorem expSizeWeightUniformLSIPackage_ready
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native : ℝ)
    (a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2) :
    FreeEnergyControlAtScale Gamma K a_native ∧
      ClayCoreLSI d N_c
        (expSizeWeightUniformLSIPackage
          N_c Gamma K a_native a_weight ha hB hb).lsiConst := by
  exact weightedUniformLSIPackage_ready
    Gamma K a_native
    (expSizeWeightUniformLSIPackage
      N_c Gamma K a_native a_weight ha hB hb)

/-- Exp-size-weight route yields the two-sided free-energy bound together with
an explicit positive LSI witness. -/
theorem expSizeWeightUniformLSIPackage_twoSided
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
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
      ClayCoreLSI d N_c
        (expSizeWeightUniformLSIPackage
          N_c Gamma K a_native a_weight ha hB hb).lsiConst := by
  constructor
  · exact log_free_energy_bound_of_weightedUniformLSIPackage
      Gamma K a_native
      (expSizeWeightUniformLSIPackage
        N_c Gamma K a_native a_weight ha hB hb)
      hhalf
  · exact explicit_uniform_lsi_of_weightedUniformLSIPackage
      Gamma K a_native
      (expSizeWeightUniformLSIPackage
        N_c Gamma K a_native a_weight ha hB hb)

end

end YangMills.ClayCore

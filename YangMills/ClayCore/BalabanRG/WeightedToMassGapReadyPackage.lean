import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedUniformLSIPackage

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedToMassGapReadyPackage — Layer 11W

Consumer-facing package exported from the weighted route.

Purpose:
* forget the internal weighted plumbing once it has done its job,
* retain exactly the data the upper "LSI → mass gap" layer wants:
  native free-energy control + an explicit positive uniform-LSI constant,
* provide a reusable package independent of the chosen weight,
* provide automatic specialization to the exponential polymer-size route.

Honest scope:
* this file does **not** prove a mass-gap theorem;
* this file also does **not** retain the weighted witness after export, so it
  intentionally only exposes the consequences actually stored in the package.
-/

noncomputable section

/-- Weight-free consumer-facing package for the upper mass-gap layer. -/
structure MassGapReadyPackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ) where
  freeEnergyControl : FreeEnergyControlAtScale Gamma K a
  lsiConst : ℝ
  lsiConst_pos : 0 < lsiConst
  uniform_lsi : ClayCoreLSI d N_c lsiConst

/-- Any weighted uniform-LSI package canonically yields a weight-free
mass-gap-ready package. -/
def massGapReadyPackage_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : WeightedUniformLSIPackage N_c Gamma K a) :
    MassGapReadyPackage N_c Gamma K a where
  freeEnergyControl :=
    freeEnergyControlAtScale_of_weightedUniformLSIPackage Gamma K a pkg
  lsiConst := pkg.lsiConst
  lsiConst_pos := pkg.lsiConst_pos
  uniform_lsi := pkg.uniform_lsi

/-- The weighted route can be exported directly from a weighted physical witness
to a weight-free mass-gap-ready package. -/
def massGapReadyPackage_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    MassGapReadyPackage N_c Gamma K a :=
  massGapReadyPackage_of_weightedUniformLSIPackage
    N_c Gamma K a
    (weightedUniformLSIPackage_of_physicalWitness N_c Gamma K a hwit)

/-- Free-energy control exposed by the mass-gap-ready package. -/
theorem freeEnergyControlAtScale_of_massGapReadyPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : MassGapReadyPackage N_c Gamma K a) :
    FreeEnergyControlAtScale Gamma K a := by
  exact pkg.freeEnergyControl

/-- Explicit positive uniform-LSI witness exposed by the package. -/
theorem explicit_uniform_lsi_of_massGapReadyPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : MassGapReadyPackage N_c Gamma K a) :
    ClayCoreLSI d N_c pkg.lsiConst := by
  exact pkg.uniform_lsi

/-- Existential uniform-LSI statement exposed by the package. -/
theorem clayCoreLSI_exists_of_massGapReadyPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : MassGapReadyPackage N_c Gamma K a) :
    ∃ c > 0, ClayCoreLSI d N_c c := by
  exact ⟨pkg.lsiConst, pkg.lsiConst_pos, pkg.uniform_lsi⟩

/-- Summary theorem in the exact language the next mass-gap layer wants:
free-energy control plus an explicit positive LSI constant. -/
theorem massGapReadyPackage_ready
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : MassGapReadyPackage N_c Gamma K a) :
    FreeEnergyControlAtScale Gamma K a ∧
      ClayCoreLSI d N_c pkg.lsiConst := by
  constructor
  · exact pkg.freeEnergyControl
  · exact pkg.uniform_lsi

/-- Positivity of the partition function from the package. -/
theorem partitionFunction_pos_of_massGapReadyPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : MassGapReadyPackage N_c Gamma K a) :
    0 < polymerPartitionFunction Gamma K := by
  exact pkg.freeEnergyControl.1

/-- One-sided free-energy bound from the package. -/
theorem log_partitionFunction_le_of_massGapReadyPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (pkg : MassGapReadyPackage N_c Gamma K a) :
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
  exact pkg.freeEnergyControl.2

/-- Existential consumer-facing theorem:
the weighted route already provides exactly the data needed for the next
"LSI → mass gap" layer. -/
theorem exists_massGapReadyPackage_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    ∃ _ : MassGapReadyPackage N_c Gamma K a, True := by
  exact ⟨massGapReadyPackage_of_weightedPhysicalWitness N_c Gamma K a hwit, trivial⟩

/-- Stronger consumer-facing theorem:
from the weighted route we can export a package together with the exact
upstairs consequences it is meant to carry. -/
theorem weightedPhysicalWitness_exports_massGapReadyPackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    ∃ pkg : MassGapReadyPackage N_c Gamma K a,
      FreeEnergyControlAtScale Gamma K a ∧ ClayCoreLSI d N_c pkg.lsiConst := by
  refine ⟨massGapReadyPackage_of_weightedPhysicalWitness N_c Gamma K a hwit, ?_⟩
  exact massGapReadyPackage_ready
    Gamma K a
    (massGapReadyPackage_of_weightedPhysicalWitness N_c Gamma K a hwit)

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- Canonical mass-gap-ready package for the exponential polymer-size route. -/
def expSizeWeightMassGapReadyPackage
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
    MassGapReadyPackage N_c Gamma K a_native :=
  massGapReadyPackage_of_weightedPhysicalWitness
    N_c Gamma K a_native
    (expSizeWeightPhysicalWitnessAtScale
      Gamma K a_native a_weight ha hB hb)

/-- Exp-size-weight route yields the exact consumer-facing package for the next
mass-gap layer. -/
theorem expSizeWeightMassGapReadyPackage_ready
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
        (expSizeWeightMassGapReadyPackage
          N_c Gamma K a_native a_weight ha hB hb).lsiConst := by
  exact massGapReadyPackage_ready
    Gamma K a_native
    (expSizeWeightMassGapReadyPackage
      N_c Gamma K a_native a_weight ha hB hb)

end

end YangMills.ClayCore

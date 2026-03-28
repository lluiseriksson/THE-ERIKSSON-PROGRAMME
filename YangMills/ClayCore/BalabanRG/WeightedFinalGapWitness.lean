import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedToPhysicalMassGapInterface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedFinalGapWitness — Layer 13W

Reusable package for the **last explicitly isolated obstruction**
on the weighted route.

What is already done:
* weighted route exports `MassGapReadyPackage`,
* the exact missing final bridge is isolated as
  `ClayCoreLSIToSUNDLRTransfer d N_c`.

What this file does:
* bundle those data into one witness object,
* export the concrete P8 DLR-LSI statement from it,
* export `ClayYangMillsTheorem` from it,
* provide canonical constructors from
  - `MassGapReadyPackage`,
  - `WeightedPhysicalWitnessAtScale`,
  - `WeightedUniformLSIPackage`,
  - exponential polymer-size packages.

This adds no new mathematics.
It only packages the last remaining bridge in a reusable form.
-/

noncomputable section

/-- Single object carrying the last isolated bridge on the weighted route. -/
structure WeightedFinalGapWitness
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ) where
  _ : MassGapReadyPackage N_c Gamma K a
  β : ℝ
  hN_c : 2 ≤ N_c
  hβ : pkg.lsiConst ≤ β
  transfer : ClayCoreLSIToSUNDLRTransfer d N_c

/-- The witness exposes native free-energy control. -/
theorem freeEnergyControlAtScale_of_weightedFinalGapWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : WeightedFinalGapWitness N_c Gamma K a) :
    FreeEnergyControlAtScale Gamma K a := by
  exact wit.pkg.freeEnergyControl

/-- The witness exposes an explicit positive uniform-LSI witness. -/
theorem explicit_uniform_lsi_of_weightedFinalGapWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : WeightedFinalGapWitness N_c Gamma K a) :
    ClayCoreLSI d N_c wit.pkg.lsiConst := by
  exact wit.pkg.uniform_lsi

/-- The witness discharges the concrete P8 DLR-LSI consumer statement. -/
theorem sun_dlr_lsi_of_weightedFinalGapWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : WeightedFinalGapWitness N_c Gamma K a) :
    ∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI
        (YangMills.sunGibbsFamily d N_c wit.β)
        (YangMills.sunDirichletForm N_c)
        α_star := by
  exact sun_dlr_lsi_of_massGapReadyPackage_and_transfer
    Gamma K a wit.β wit.hN_c wit.pkg wit.hβ wit.transfer

/-- Main consequence: the witness closes the weighted route all the way to the
existing P8 consumer theorem. -/
theorem clayTheorem_of_weightedFinalGapWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : WeightedFinalGapWitness N_c Gamma K a) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_and_transfer
    Gamma K a wit.β wit.hN_c wit.pkg wit.hβ wit.transfer

/-- Positivity of the partition function still comes for free from the stored
mass-gap-ready package. -/
theorem partitionFunction_pos_of_weightedFinalGapWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : WeightedFinalGapWitness N_c Gamma K a) :
    0 < polymerPartitionFunction Gamma K := by
  exact wit.pkg.freeEnergyControl.1

/-- One-sided free-energy bound exposed by the witness. -/
theorem log_partitionFunction_le_of_weightedFinalGapWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : WeightedFinalGapWitness N_c Gamma K a) :
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
  exact wit.pkg.freeEnergyControl.2

/-! ## Canonical constructors -/

/-- Build the final-gap witness directly from a mass-gap-ready package. -/
def weightedFinalGapWitness_of_massGapReadyPackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a β : ℝ)
    (pkg : MassGapReadyPackage N_c Gamma K a)
    (hN_c : 2 ≤ N_c)
    (hβ : pkg.lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    WeightedFinalGapWitness N_c Gamma K a where
  _ := pkg
  β := β
  hN_c := hN_c
  hβ := hβ
  transfer := tr

/-- Build the final-gap witness from a weighted physical witness. -/
def weightedFinalGapWitness_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a β : ℝ)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a)
    (hN_c : 2 ≤ N_c)
    (hβ :
      (massGapReadyPackage_of_weightedPhysicalWitness
        N_c Gamma K a hwit).lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    WeightedFinalGapWitness N_c Gamma K a :=
  weightedFinalGapWitness_of_massGapReadyPackage
    N_c Gamma K a β
    (massGapReadyPackage_of_weightedPhysicalWitness N_c Gamma K a hwit)
    hN_c hβ tr

/-- Build the final-gap witness from a weighted uniform-LSI package. -/
def weightedFinalGapWitness_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a β : ℝ)
    (pkgW : WeightedUniformLSIPackage N_c Gamma K a)
    (hN_c : 2 ≤ N_c)
    (hβ :
      (massGapReadyPackage_of_weightedUniformLSIPackage
        N_c Gamma K a pkgW).lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    WeightedFinalGapWitness N_c Gamma K a :=
  weightedFinalGapWitness_of_massGapReadyPackage
    N_c Gamma K a β
    (massGapReadyPackage_of_weightedUniformLSIPackage N_c Gamma K a pkgW)
    hN_c hβ tr

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- Canonical final-gap witness for the exp-size-weight route. -/
def expSizeWeightFinalGapWitness
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native a_weight β : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (hβ :
      (expSizeWeightMassGapReadyPackage
        N_c Gamma K a_native a_weight ha hB hb).lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    WeightedFinalGapWitness N_c Gamma K a_native :=
  weightedFinalGapWitness_of_massGapReadyPackage
    N_c Gamma K a_native β
    (expSizeWeightMassGapReadyPackage
      N_c Gamma K a_native a_weight ha hB hb)
    hN_c hβ tr

/-- Exp-size-weight route discharges the concrete P8 DLR-LSI consumer. -/
theorem sun_dlr_lsi_of_expSizeWeightFinalGapWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native a_weight β : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (hβ :
      (expSizeWeightMassGapReadyPackage
        N_c Gamma K a_native a_weight ha hB hb).lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    ∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI
        (YangMills.sunGibbsFamily d N_c β)
        (YangMills.sunDirichletForm N_c)
        α_star := by
  exact sun_dlr_lsi_of_weightedFinalGapWitness
    Gamma K a_native
    (expSizeWeightFinalGapWitness
      N_c Gamma K a_native a_weight β ha hB hb hN_c hβ tr)

/-- Exp-size-weight route reaches the terminal P8 consumer theorem. -/
theorem clayTheorem_of_expSizeWeightFinalGapWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native a_weight β : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (hβ :
      (expSizeWeightMassGapReadyPackage
        N_c Gamma K a_native a_weight ha hB hb).lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_weightedFinalGapWitness
    Gamma K a_native
    (expSizeWeightFinalGapWitness
      N_c Gamma K a_native a_weight β ha hB hb hN_c hβ tr)

end

end YangMills.ClayCore

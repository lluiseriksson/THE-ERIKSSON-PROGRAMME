import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedToMassGapReadyPackage
import YangMills.P8_PhysicalGap.BalabanToLSI
import YangMills.P8_PhysicalGap.PhysicalMassGap

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedToPhysicalMassGapInterface — Layer 12W

This file isolates the **actual remaining consumer interface** between the
weighted BalabanRG lane and the P8 physical mass-gap lane.

What the weighted lane currently exports:
* `FreeEnergyControlAtScale`
* an explicit positive `ClayCoreLSI` witness packaged in
  `MassGapReadyPackage`

What `P8_PhysicalGap/PhysicalMassGap.lean` actually consumes:
* `∃ α_star > 0, DLR_LSI (sunGibbsFamily ...) (sunDirichletForm ...) α_star`

So the remaining step is not another weighted free-energy lemma.
It is an explicit transfer interface:
`ClayCoreLSI`  →  `DLR_LSI` for the concrete SU(N) Gibbs family.

This file does not fake that transfer.
It packages it as the exact bridge still needed upstairs.
-/

noncomputable section

/-- Exact missing bridge from the Clay-core LSI package to the concrete P8
DLR-LSI statement for SU(N). -/
structure ClayCoreLSIToSUNDLRTransfer
    (d N_c : ℕ) [NeZero N_c] where
  transfer :
    ∀ {c β : ℝ},
      2 ≤ N_c →
      0 < c →
      ClayCoreLSI d N_c c →
      c ≤ β →
      ∃ α_star : ℝ, 0 < α_star ∧
        DLR_LSI
          (YangMills.sunGibbsFamily d N_c β)
          (YangMills.sunDirichletForm N_c)
          α_star

/-- A mass-gap-ready package plus the explicit `ClayCoreLSI → DLR_LSI` bridge
yields the concrete P8 DLR-LSI statement. -/
theorem sun_dlr_lsi_of_massGapReadyPackage_and_transfer
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a β : ℝ)
    (hN_c : 2 ≤ N_c)
    (pkg : MassGapReadyPackage N_c Gamma K a)
    (hβ : pkg.lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    ∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI
        (YangMills.sunGibbsFamily d N_c β)
        (YangMills.sunDirichletForm N_c)
        α_star := by
  exact tr.transfer hN_c pkg.lsiConst_pos pkg.uniform_lsi hβ

/-- Main adapter:
once the explicit `ClayCoreLSI → DLR_LSI` bridge is supplied, the weighted
route reaches `ClayYangMillsTheorem` through the existing P8 consumer. -/
theorem clayTheorem_of_massGapReadyPackage_and_transfer
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a β : ℝ)
    (hN_c : 2 ≤ N_c)
    (pkg : MassGapReadyPackage N_c Gamma K a)
    (hβ : pkg.lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact YangMills.sun_clay_conditional
    d N_c hN_c β pkg.lsiConst hβ pkg.lsiConst_pos
    (sun_dlr_lsi_of_massGapReadyPackage_and_transfer
      Gamma K a β hN_c pkg hβ tr)

/-- Direct export from a weighted physical witness to `ClayYangMillsTheorem`,
conditional only on the now-explicit `ClayCoreLSI → DLR_LSI` bridge. -/
theorem clayTheorem_of_weightedPhysicalWitness_and_transfer
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a β : ℝ)
    (hN_c : 2 ≤ N_c)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a)
    (hβ :
      (massGapReadyPackage_of_weightedPhysicalWitness
        N_c Gamma K a hwit).lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_and_transfer
    Gamma K a β hN_c
    (massGapReadyPackage_of_weightedPhysicalWitness N_c Gamma K a hwit)
    hβ tr

/-- Direct export from a weighted uniform-LSI package to `ClayYangMillsTheorem`,
conditional only on the now-explicit `ClayCoreLSI → DLR_LSI` bridge. -/
theorem clayTheorem_of_weightedUniformLSIPackage_and_transfer
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a β : ℝ)
    (hN_c : 2 ≤ N_c)
    (pkgW : WeightedUniformLSIPackage N_c Gamma K a)
    (hβ :
      (massGapReadyPackage_of_weightedUniformLSIPackage
        N_c Gamma K a pkgW).lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_and_transfer
    Gamma K a β hN_c
    (massGapReadyPackage_of_weightedUniformLSIPackage N_c Gamma K a pkgW)
    hβ tr

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- Exp-size-weight route reaches the concrete P8 DLR-LSI statement once the
explicit `ClayCoreLSI → DLR_LSI` transfer is supplied. -/
theorem sun_dlr_lsi_of_expSizeWeightPackage_and_transfer
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native a_weight β : ℝ)
    (hN_c : 2 ≤ N_c)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2)
    (hβ :
      (expSizeWeightMassGapReadyPackage
        N_c Gamma K a_native a_weight ha hB hb).lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    ∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI
        (YangMills.sunGibbsFamily d N_c β)
        (YangMills.sunDirichletForm N_c)
        α_star := by
  exact sun_dlr_lsi_of_massGapReadyPackage_and_transfer
    Gamma K a_native β hN_c
    (expSizeWeightMassGapReadyPackage
      N_c Gamma K a_native a_weight ha hB hb)
    hβ tr

/-- Exp-size-weight route reaches `ClayYangMillsTheorem` once the explicit
`ClayCoreLSI → DLR_LSI` transfer is supplied. -/
theorem clayTheorem_of_expSizeWeightPackage_and_transfer
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native a_weight β : ℝ)
    (hN_c : 2 ≤ N_c)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2)
    (hβ :
      (expSizeWeightMassGapReadyPackage
        N_c Gamma K a_native a_weight ha hB hb).lsiConst ≤ β)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_and_transfer
    Gamma K a_native β hN_c
    (expSizeWeightMassGapReadyPackage
      N_c Gamma K a_native a_weight ha hB hb)
    hβ tr

end

end YangMills.ClayCore

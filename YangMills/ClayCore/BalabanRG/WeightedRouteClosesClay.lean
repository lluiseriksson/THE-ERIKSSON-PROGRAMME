import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedFinalGapWitness

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedRouteClosesClay — Layer 14W

This file closes the weighted route to `ClayYangMillsTheorem` once the explicit
final bridge

  `ClayCoreLSIToSUNDLRTransfer d N_c`

is supplied.  The former canonical instantiation through the legacy
un-normalized P8 Holley-Stroock axiom has been removed; the transfer is now
visible at the call site.
-/

noncomputable section

/-- A mass-gap-ready package already closes `ClayYangMillsTheorem` in the
current abstract P8 interface, once `β` dominates the stored LSI constant and
the final P8 transfer is supplied. -/
theorem clayTheorem_of_massGapReadyPackage
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
  exact clayTheorem_of_massGapReadyPackage_and_transfer
    Gamma K a β hN_c pkg hβ
    tr

/-- Specialization at the stored LSI constant itself. -/
theorem clayTheorem_of_massGapReadyPackage_at_lsiConst
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hN_c : 2 ≤ N_c)
    (pkg : MassGapReadyPackage N_c Gamma K a)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage
    Gamma K a pkg.lsiConst hN_c pkg le_rfl tr

/-- Direct closure from a weighted physical witness. -/
theorem clayTheorem_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hN_c : 2 ≤ N_c)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_at_lsiConst
    Gamma K a hN_c
    (massGapReadyPackage_of_weightedPhysicalWitness N_c Gamma K a hwit)
    tr

/-- Direct closure from a weighted uniform-LSI package. -/
theorem clayTheorem_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hN_c : 2 ≤ N_c)
    (pkgW : WeightedUniformLSIPackage N_c Gamma K a)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_at_lsiConst
    Gamma K a hN_c
    (massGapReadyPackage_of_weightedUniformLSIPackage N_c Gamma K a pkgW)
    tr

/-- Direct closure from a weighted final-gap witness using its stored transfer. -/
theorem clayTheorem_of_weightedFinalGapWitness_canonical
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : WeightedFinalGapWitness N_c Gamma K a) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage
    Gamma K a wit.β wit.hN_c wit.pkg wit.hβ wit.transfer

/-! ## Automatic specialization: exponential polymer-size weight -/

/-- The exp-size-weight route closes `ClayYangMillsTheorem` directly. -/
theorem clayTheorem_of_expSizeWeightPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
      ≤ Real.exp (theoreticalBudget Gamma K a_native) - 1)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_at_lsiConst
    Gamma K a_native hN_c
    (expSizeWeightMassGapReadyPackage
      N_c Gamma K a_native a_weight ha hB hb)
    tr

/-- Final-gap closure for exp-size-weight once the final transfer is supplied. -/
theorem clayTheorem_of_expSizeWeightFinalGapWitness_canonical
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
  exact clayTheorem_of_massGapReadyPackage
    Gamma K a_native β hN_c
    (expSizeWeightMassGapReadyPackage
      N_c Gamma K a_native a_weight ha hB hb)
    hβ
    tr

end

end YangMills.ClayCore

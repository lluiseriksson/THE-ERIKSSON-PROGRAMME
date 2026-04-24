import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedRouteClosesClay
import YangMills.ClayCore.BalabanRG.KPWeightedBudgetInterface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPExpSizeWeightToClay — Layer 15W

Direct terminal closures from the concrete KP exponential-size-weight lane.

Purpose:
* expose the already-green terminal closure
  `clayTheorem_of_expSizeWeightPackage`
  under a more concrete KP-facing API,
* keep the final `ClayCoreLSIToSUNDLRTransfer` input explicit,
* provide a first direct theorem from a genuine KP hypothesis on a singleton
  support all the way to `ClayYangMillsTheorem`.

This file does not add new mathematics.
It packages the route:

  KP / exp-size-weight budget
    → weighted terminal closure
    → ClayYangMillsTheorem
-/

noncomputable section

/-- Direct alias:
an exponential-size-weight weighted budget at the native target budget closes
`ClayYangMillsTheorem`. -/
theorem clayTheorem_of_expSizeWeightBudget
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
  exact clayTheorem_of_expSizeWeightPackage
    Gamma K a_native a_weight ha hB hb hN_c tr

/-- KP-shaped specialization:
use the same parameter `a` for both the exp-size-weight and the native target
budget. -/
theorem clayTheorem_of_kpExpSizeWeightBudget
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (ha : 0 ≤ a)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1)
    (hb : theoreticalBudget Gamma K a < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_expSizeWeightBudget
    Gamma K a a ha hB hb hN_c tr

/-- First genuinely concrete terminal closure from KP:
if the singleton exp-size-weight budget is small enough to fit below the native
target budget, then `ClayYangMillsTheorem` follows. -/
theorem clayTheorem_of_kpSingleton_expSizeWeight
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (ha : 0 ≤ a)
    (hKP : KoteckyPreiss K a)
    (hfit :
      a ≤ Real.exp (theoreticalBudget ({X} : Finset (Polymer d L)) K a) - 1)
    (hb :
      theoreticalBudget ({X} : Finset (Polymer d L)) K a < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  apply clayTheorem_of_kpExpSizeWeightBudget
    ({X} : Finset (Polymer d L)) K a ha ?_ hb hN_c tr
  exact le_trans
    (kpWeightedInductionBudget_singleton_expSizeWeight_le
      (d := d) (L := L) K a X hKP)
    hfit

/-- Same singleton closure, but phrased through the weighted induction budget
directly rather than through `KoteckyPreiss`. -/
theorem clayTheorem_of_singleton_expSizeWeightBudget
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (ha : 0 ≤ a)
    (hB :
      KPWeightedInductionBudget ({X} : Finset (Polymer d L))
        K (kpExpSizeWeight a d L)
        ≤ Real.exp (theoreticalBudget ({X} : Finset (Polymer d L)) K a) - 1)
    (hb :
      theoreticalBudget ({X} : Finset (Polymer d L)) K a < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : ClayCoreLSIToSUNDLRTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_kpExpSizeWeightBudget
    ({X} : Finset (Polymer d L)) K a ha hB hb hN_c tr

end

end YangMills.ClayCore

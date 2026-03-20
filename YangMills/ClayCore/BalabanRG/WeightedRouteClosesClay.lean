import Mathlib
import YangMills.ClayCore.BalabanRG.WeightedFinalGapWitness

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# WeightedRouteClosesClay — Layer 14W

This file closes the weighted route to `ClayYangMillsTheorem` **within the
current abstract P8 interface**.

Key observation:
`BalabanToLSI.lean` already provides

  `sun_gibbs_dlr_lsi d N_c hN_c β β₀ hβ hβ₀`

for arbitrary `β₀ > 0` and `β ≥ β₀`.

Therefore the previously isolated bridge

  `ClayCoreLSIToSUNDLRTransfer d N_c`

can be instantiated canonically by choosing `β₀ := c`.

This file does not add new mathematics.
It just removes the last extra witness parameter by reusing the already-green
P8 consumer theorem.
-/

noncomputable section

/-- Canonical realization of the final isolated bridge, using the existing
P8 theorem `sun_gibbs_dlr_lsi` with `β₀ := c`. -/
def canonicalClayCoreLSIToSUNDLRTransfer
    (d N_c : ℕ) [NeZero N_c] :
    ClayCoreLSIToSUNDLRTransfer d N_c where
  transfer := by
    intro c β hN_c hc _hClay hle
    exact YangMills.sun_gibbs_dlr_lsi d N_c hN_c β c hle hc

/-- A mass-gap-ready package already closes `ClayYangMillsTheorem` in the
current abstract P8 interface, once `β` dominates the stored LSI constant. -/
theorem clayTheorem_of_massGapReadyPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a β : ℝ)
    (hN_c : 2 ≤ N_c)
    (pkg : MassGapReadyPackage N_c Gamma K a)
    (hβ : pkg.lsiConst ≤ β) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_and_transfer
    Gamma K a β hN_c pkg hβ
    (canonicalClayCoreLSIToSUNDLRTransfer d N_c)

/-- Specialization at the stored LSI constant itself. -/
theorem clayTheorem_of_massGapReadyPackage_at_lsiConst
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hN_c : 2 ≤ N_c)
    (pkg : MassGapReadyPackage N_c Gamma K a) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage
    Gamma K a pkg.lsiConst hN_c pkg le_rfl

/-- Direct closure from a weighted physical witness. -/
theorem clayTheorem_of_weightedPhysicalWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hN_c : 2 ≤ N_c)
    (hwit : WeightedPhysicalWitnessAtScale Gamma K a) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_at_lsiConst
    Gamma K a hN_c
    (massGapReadyPackage_of_weightedPhysicalWitness N_c Gamma K a hwit)

/-- Direct closure from a weighted uniform-LSI package. -/
theorem clayTheorem_of_weightedUniformLSIPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (hN_c : 2 ≤ N_c)
    (pkgW : WeightedUniformLSIPackage N_c Gamma K a) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_at_lsiConst
    Gamma K a hN_c
    (massGapReadyPackage_of_weightedUniformLSIPackage N_c Gamma K a pkgW)

/-- Direct closure from a weighted final-gap witness, ignoring the stored
transfer and using the canonical one from the current P8 interface. -/
theorem clayTheorem_of_weightedFinalGapWitness_canonical
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : WeightedFinalGapWitness N_c Gamma K a) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage
    Gamma K a wit.β wit.hN_c wit.pkg wit.hβ

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
    (hN_c : 2 ≤ N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage_at_lsiConst
    Gamma K a_native hN_c
    (expSizeWeightMassGapReadyPackage
      N_c Gamma K a_native a_weight ha hB hb)

/-- Canonical final-gap witness for exp-size-weight, now with no extra bridge
parameter needed for terminal closure. -/
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
        N_c Gamma K a_native a_weight ha hB hb).lsiConst ≤ β) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_massGapReadyPackage
    Gamma K a_native β hN_c
    (expSizeWeightMassGapReadyPackage
      N_c Gamma K a_native a_weight ha hB hb)
    hβ

end

end YangMills.ClayCore

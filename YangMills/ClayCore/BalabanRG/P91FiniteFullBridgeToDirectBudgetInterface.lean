import Mathlib
import YangMills.ClayCore.BalabanRG.P91FiniteFullSmallConstantsToDirectBudgetInterface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open Filter

/-!
# P91FiniteFullBridgeToDirectBudgetInterface — compatibility shim

This file now re-exports the honest finite-full small-constants interface under
the legacy filename.

Historical note:
the previous version packaged the transfer with coarse hypotheses
`1 ≤ exp(-β_k)` and `1 ≤ physicalContractionRate β_k`. The honest interface now
isolates the real finite-full gap via explicit small constants
`A_large`, `A_cauchy` and their refinements to the physical targets.

No fake decay is introduced here; this file is only a compatibility layer.
-/

noncomputable section

/-- Legacy name, now redirected to the honest small-constants transfer
interface. -/
abbrev ExpSizeWeightFiniteFullToDirectBudgetTransfer
    (d N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))] :=
  ExpSizeWeightFiniteFullSmallConstantToDirectBudgetTransfer d N_c

/-- Legacy name, now redirected to the honest small-constants package. -/
abbrev P91FiniteFullBridgeToDirectBudgetPackage
    {d : ℕ} (N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0)) (β : ℕ → ℝ) (r : ℕ → ℝ) :=
  P91FiniteFullSmallConstantToDirectBudgetPackage N_c K β r

/-- Legacy top-level closure theorem, now phrased through the honest
small-constants package. -/
theorem clayTheorem_of_expSizeWeightFiniteFullTransfer
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (pkg : ExpSizeWeightFiniteFullSmallConstantPackage d N_c)
    (K : Activity d (Int.ofNat 0))
    (htarget : theoreticalBudget pkg.polys K pkg.a < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : ExpSizeWeightFiniteFullToDirectBudgetTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_expSizeWeightFiniteFullSmallConstantTransfer
    pkg K htarget hN_c tr

/-- The P91 half still gives decay of the physical contraction rate. -/
theorem rate_to_zero_of_p91FiniteFullBridgeToDirectBudgetPackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullBridgeToDirectBudgetPackage N_c K β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  exact rate_to_zero_of_p91FiniteFullSmallConstantToDirectBudgetPackage K β r pkg

/-- The transfer half closes `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_p91FiniteFullBridgeToDirectBudgetPackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullBridgeToDirectBudgetPackage N_c K β r) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_p91FiniteFullSmallConstantToDirectBudgetPackage K β r pkg

/-- Summary theorem: P91 data supplies rate decay, and the honest finite-full
small-constants → direct-budget transfer supplies terminal closure. -/
theorem p91_rate_and_clay_of_p91FiniteFullBridgeToDirectBudgetPackage
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (pkg : P91FiniteFullBridgeToDirectBudgetPackage N_c K β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  exact p91_rate_and_clay_of_p91FiniteFullSmallConstantToDirectBudgetPackage
    K β r pkg

/-- Convenience constructor from raw ingredients, now targeting the honest
small-constants package. -/
def p91FiniteFullBridgeToDirectBudgetPackage_mk
    {d : ℕ} (N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (K : Activity d (Int.ofNat 0))
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (data : P91RecursionData N_c)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c)
    (smallConstants : ExpSizeWeightFiniteFullSmallConstantPackage d N_c)
    (htarget : theoreticalBudget smallConstants.polys K smallConstants.a < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : ExpSizeWeightFiniteFullToDirectBudgetTransfer d N_c) :
    P91FiniteFullBridgeToDirectBudgetPackage N_c K β r := by
  refine
    { data := data
      hβ0 := hβ0
      hstep := hstep
      hr := hr
      hβ_upper := hβ_upper
      smallConstants := smallConstants
      target_lt_log2 := htarget
      rank_ok := hN_c
      directBudgetTransfer := tr }

/-! ## Singleton specialization -/

/-- Singleton specialization of the honest finite-full transfer. -/
abbrev SingletonExpSizeWeightFiniteFullToDirectBudgetTransfer
    (d N_c : ℕ) [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))] :=
  ExpSizeWeightFiniteFullToDirectBudgetTransfer d N_c

/-- Singleton consumer theorem through the honest small-constants package. -/
theorem clayTheorem_of_singletonExpSizeWeightFiniteFullTransfer
    {d : ℕ} {N_c : ℕ} [NeZero N_c]
    [∀ j, Fintype (Polymer d (Int.ofNat j))]
    [∀ j, DecidableEq (Polymer d (Int.ofNat j))]
    (pkg : ExpSizeWeightFiniteFullSmallConstantPackage d N_c)
    (X : Polymer d (Int.ofNat 0))
    (hpolys : pkg.polys = ({X} : Finset (Polymer d (Int.ofNat 0))))
    (K : Activity d (Int.ofNat 0))
    (htarget :
      theoreticalBudget ({X} : Finset (Polymer d (Int.ofNat 0))) K pkg.a < Real.log 2)
    (hN_c : 2 ≤ N_c)
    (tr : SingletonExpSizeWeightFiniteFullToDirectBudgetTransfer d N_c) :
    YangMills.ClayYangMillsTheorem := by
  have htarget' : theoreticalBudget pkg.polys K pkg.a < Real.log 2 := by
    simpa [hpolys] using htarget
  exact clayTheorem_of_expSizeWeightFiniteFullTransfer
    pkg K htarget' hN_c tr

end

end YangMills.ClayCore

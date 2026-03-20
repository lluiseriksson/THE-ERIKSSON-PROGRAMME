import Mathlib
import YangMills.ClayCore.BalabanRG.P91ExpSizeWeightLogBudgetWitness
import YangMills.ClayCore.BalabanRG.CauchyDecayFromAF

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# P91DataToClayPackage — Layer 18W

Combined package:
* upstream P91 recursion data, which already yields β-divergence and
  contraction-rate decay to 0,
* downstream exp-size-weight log-budget witness, which already closes the
  terminal KP route to `ClayYangMillsTheorem`.

Honest scope:
this file does **not** prove that P91 data itself implies the weighted budget.
It packages the exact current meeting point between:
* P91 / AF / rate-decay infrastructure, and
* the terminal exp-size-weight KP closure.
-/

noncomputable section

/-- Combined package: P91 recursion data + the exact terminal exp-size-weight
log-budget witness. -/
structure P91DataExpSizeWeightLogBudgetPackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ) where
  data : P91RecursionData N_c
  hβ0 : 1 ≤ β 0
  hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)
  hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2
  hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c
  terminalWitness : P91ExpSizeWeightLogBudgetWitness N_c Gamma K a

/-- The P91 half of the package yields β-divergence. -/
theorem beta_tendsto_top_of_p91DataExpSizeWeightLogBudgetPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91DataExpSizeWeightLogBudgetPackage N_c Gamma K a β r) :
    Tendsto β atTop atTop := by
  exact beta_tendsto_top_from_data_closed
    N_c pkg.data β r pkg.hβ0 pkg.hstep pkg.hr pkg.hβ_upper

/-- The P91 half of the package yields contraction-rate decay to 0. -/
theorem rate_to_zero_of_p91DataExpSizeWeightLogBudgetPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91DataExpSizeWeightLogBudgetPackage N_c Gamma K a β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  exact rate_to_zero_from_af
    N_c pkg.data β r pkg.hβ0 pkg.hstep pkg.hr pkg.hβ_upper

/-- The terminal witness half of the package closes `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_p91DataExpSizeWeightLogBudgetPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91DataExpSizeWeightLogBudgetPackage N_c Gamma K a β r) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_p91ExpSizeWeightLogBudgetWitness
    Gamma K a pkg.terminalWitness

/-- Combined summary:
the package simultaneously exposes AF-side rate decay and the terminal Clay
closure. -/
theorem p91_rate_and_clay_of_p91DataExpSizeWeightLogBudgetPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91DataExpSizeWeightLogBudgetPackage N_c Gamma K a β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  constructor
  · exact rate_to_zero_of_p91DataExpSizeWeightLogBudgetPackage
      Gamma K a β r pkg
  · exact clayTheorem_of_p91DataExpSizeWeightLogBudgetPackage
      Gamma K a β r pkg

/-- Convenience constructor from raw inputs. -/
def p91DataExpSizeWeightLogBudgetPackage_mk
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (data : P91RecursionData N_c)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c)
    (wit : P91ExpSizeWeightLogBudgetWitness N_c Gamma K a) :
    P91DataExpSizeWeightLogBudgetPackage N_c Gamma K a β r where
  data := data
  hβ0 := hβ0
  hstep := hstep
  hr := hr
  hβ_upper := hβ_upper
  terminalWitness := wit

/-! ## Singleton specialization -/

/-- Singleton specialization of the combined P91/package interface. -/
abbrev P91SingletonDataExpSizeWeightLogBudgetPackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ) :=
  P91DataExpSizeWeightLogBudgetPackage
    N_c ({X} : Finset (Polymer d L)) K a β r

/-- Combined singleton theorem:
future producers can aim directly for this package-level output. -/
theorem p91_rate_and_clay_of_singletonPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91SingletonDataExpSizeWeightLogBudgetPackage N_c K a X β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  exact p91_rate_and_clay_of_p91DataExpSizeWeightLogBudgetPackage
    ({X} : Finset (Polymer d L)) K a β r pkg

/-- Concrete singleton theorem:
P91 recursion data + a scalar budget envelope + a logarithmic target fit
yield both AF-side rate decay and terminal Clay closure. -/
theorem p91_rate_and_clay_of_kpSingletonBudgetEnvelope
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c)
    (K : Activity d L)
    (a B : ℝ)
    (X : Polymer d L)
    (ha : 0 ≤ a)
    (hKP : KoteckyPreiss K a)
    (haB : a ≤ B)
    (hB_nonneg : 0 ≤ B)
    (hlogfit :
      Real.log (1 + B) ≤ theoreticalBudget ({X} : Finset (Polymer d L)) K a)
    (htarget :
      theoreticalBudget ({X} : Finset (Polymer d L)) K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  constructor
  · exact rate_to_zero_from_af
      N_c data β r hβ0 hstep hr hβ_upper
  · exact clayTheorem_of_kpSingleton_via_p91BudgetEnvelope
      (K := K) (a := a) (B := B) (X := X)
      ha hKP haB hB_nonneg hlogfit htarget hN_c

end

end YangMills.ClayCore

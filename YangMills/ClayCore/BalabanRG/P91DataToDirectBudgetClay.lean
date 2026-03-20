import Mathlib
import YangMills.ClayCore.BalabanRG.KPExpSizeWeightDirectBudgetToClay
import YangMills.ClayCore.BalabanRG.CauchyDecayFromAF

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# P91DataToDirectBudgetClay — Layer 21W

Combined package in the cleanest currently honest form:

upstream:
* P91 recursion data (enough to get `β_k → +∞` and
  `physicalContractionRate (β_k) → 0`),

downstream:
* a direct exp-size-weight weighted-budget fit
    `KPWeightedInductionBudget ... ≤ theoreticalBudget ...`,

output:
* AF-side rate decay,
* `ClayYangMillsTheorem`.

This file does not claim to derive the direct budget fit from P91.
It packages the current meeting point after removing the extra scalar envelope.
-/

noncomputable section

/-- Exact terminal witness in the direct-budget form. -/
structure P91ExpSizeWeightDirectBudgetWitness
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ) where
  a_nonneg : 0 ≤ a
  direct_fit :
    KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L)
      ≤ theoreticalBudget Gamma K a
  target_lt_log2 :
    theoreticalBudget Gamma K a < Real.log 2
  rank_ok : 2 ≤ N_c

/-- The direct-budget witness closes `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_p91ExpSizeWeightDirectBudgetWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : P91ExpSizeWeightDirectBudgetWitness N_c Gamma K a) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_kpExpSizeWeightDirectBudget
    Gamma K a wit.a_nonneg wit.direct_fit wit.target_lt_log2 wit.rank_ok

/-- Combined package:
P91 recursion data together with the direct terminal budget witness. -/
structure P91DataExpSizeWeightDirectBudgetPackage
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
  terminalWitness : P91ExpSizeWeightDirectBudgetWitness N_c Gamma K a

/-- The P91 half gives rate decay to 0. -/
theorem rate_to_zero_of_p91DataExpSizeWeightDirectBudgetPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91DataExpSizeWeightDirectBudgetPackage N_c Gamma K a β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  exact rate_to_zero_from_af
    N_c pkg.data β r pkg.hβ0 pkg.hstep pkg.hr pkg.hβ_upper

/-- The terminal witness half gives `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_p91DataExpSizeWeightDirectBudgetPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91DataExpSizeWeightDirectBudgetPackage N_c Gamma K a β r) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_p91ExpSizeWeightDirectBudgetWitness
    Gamma K a pkg.terminalWitness

/-- Combined summary theorem. -/
theorem p91_rate_and_clay_of_p91DataExpSizeWeightDirectBudgetPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91DataExpSizeWeightDirectBudgetPackage N_c Gamma K a β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  constructor
  · exact rate_to_zero_of_p91DataExpSizeWeightDirectBudgetPackage
      Gamma K a β r pkg
  · exact clayTheorem_of_p91DataExpSizeWeightDirectBudgetPackage
      Gamma K a β r pkg

/-- Convenience constructor from raw inputs. -/
def p91DataExpSizeWeightDirectBudgetPackage_mk
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
    (wit : P91ExpSizeWeightDirectBudgetWitness N_c Gamma K a) :
    P91DataExpSizeWeightDirectBudgetPackage N_c Gamma K a β r where
  data := data
  hβ0 := hβ0
  hstep := hstep
  hr := hr
  hβ_upper := hβ_upper
  terminalWitness := wit

/-! ## Singleton specialization -/

/-- Singleton specialization of the combined direct-budget package. -/
abbrev P91SingletonDataExpSizeWeightDirectBudgetPackage
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ) :=
  P91DataExpSizeWeightDirectBudgetPackage
    N_c ({X} : Finset (Polymer d L)) K a β r

/-- Singleton version of the combined summary theorem. -/
theorem p91_rate_and_clay_of_singletonDirectBudgetPackage
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (β : ℕ → ℝ)
    (r : ℕ → ℝ)
    (pkg : P91SingletonDataExpSizeWeightDirectBudgetPackage N_c K a X β r) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  exact p91_rate_and_clay_of_p91DataExpSizeWeightDirectBudgetPackage
    ({X} : Finset (Polymer d L)) K a β r pkg

/-- Concrete singleton theorem with the cleanest current upstream condition:
P91 recursion data plus `a ≤ theoreticalBudget` already give rate decay and
terminal Clay closure. -/
theorem p91_rate_and_clay_of_kpSingletonDirectBudget
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
    (a : ℝ)
    (X : Polymer d L)
    (ha : 0 ≤ a)
    (hKP : KoteckyPreiss K a)
    (hfit :
      a ≤ theoreticalBudget ({X} : Finset (Polymer d L)) K a)
    (htarget :
      theoreticalBudget ({X} : Finset (Polymer d L)) K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  constructor
  · exact rate_to_zero_from_af
      N_c data β r hβ0 hstep hr hβ_upper
  · exact clayTheorem_of_kpSingleton_expSizeWeight_directBudget
      (K := K) (a := a) (X := X)
      ha hKP hfit htarget hN_c

end

end YangMills.ClayCore

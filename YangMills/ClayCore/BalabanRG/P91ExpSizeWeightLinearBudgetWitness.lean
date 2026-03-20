import Mathlib
import YangMills.ClayCore.BalabanRG.P91DataToClayPackage

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# P91ExpSizeWeightLinearBudgetWitness — Layer 19W

Linear-budget producer interface for future P91 / AF closures.

This file simplifies the upstream scalar interface one more step:

old producer-side fit:
  `Real.log (1 + B) ≤ theoreticalBudget ...`

new producer-side fit:
  `B ≤ theoreticalBudget ...`

This is sound because for `B ≥ 0` we have `log(1+B) ≤ B`.
So this file does not add new mathematics; it only makes the future producer
API more ergonomic.
-/

noncomputable section

/-- Linear budget fit implies the logarithmic fit used downstream. -/
theorem logfit_of_linearBudgetFit
    {B t : ℝ}
    (hB : 0 ≤ B)
    (hfit : B ≤ t) :
    Real.log (1 + B) ≤ t := by
  have hpos : 0 < 1 + B := by linarith
  have hlogB : Real.log (1 + B) ≤ B := by
    have := log_le_sub_one_of_pos (1 + B) hpos
    linarith
  linarith

/-- Producer-side witness with a linear scalar fit `B ≤ theoreticalBudget`. -/
structure P91ExpSizeWeightLinearBudgetWitness
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ) where
  a_nonneg : 0 ≤ a
  B : ℝ
  B_nonneg : 0 ≤ B
  budget_le :
    KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B
  linear_fit :
    B ≤ theoreticalBudget Gamma K a
  target_lt_log2 :
    theoreticalBudget Gamma K a < Real.log 2
  rank_ok : 2 ≤ N_c

/-- Convert the simpler linear-budget witness into the already existing
log-budget witness. -/
def P91ExpSizeWeightLinearBudgetWitness.toLogWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    {Gamma : Finset (Polymer d L)}
    {K : Activity d L}
    {a : ℝ}
    (wit : P91ExpSizeWeightLinearBudgetWitness N_c Gamma K a) :
    P91ExpSizeWeightLogBudgetWitness N_c Gamma K a :=
  p91ExpSizeWeightLogBudgetWitness_mk
    N_c Gamma K a wit.B
    wit.a_nonneg
    wit.B_nonneg
    wit.budget_le
    (logfit_of_linearBudgetFit wit.B_nonneg wit.linear_fit)
    wit.target_lt_log2
    wit.rank_ok

/-- Main consumer theorem from the simpler linear-budget witness. -/
theorem clayTheorem_of_p91ExpSizeWeightLinearBudgetWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : P91ExpSizeWeightLinearBudgetWitness N_c Gamma K a) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_p91ExpSizeWeightLogBudgetWitness
    Gamma K a wit.toLogWitness

/-- Convenience constructor from raw scalar data. -/
def p91ExpSizeWeightLinearBudgetWitness_mk
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a B : ℝ)
    (ha_nonneg : 0 ≤ a)
    (hB_nonneg : 0 ≤ B)
    (hbudget :
      KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hfit :
      B ≤ theoreticalBudget Gamma K a)
    (htarget :
      theoreticalBudget Gamma K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    P91ExpSizeWeightLinearBudgetWitness N_c Gamma K a where
  a_nonneg := ha_nonneg
  B := B
  B_nonneg := hB_nonneg
  budget_le := hbudget
  linear_fit := hfit
  target_lt_log2 := htarget
  rank_ok := hN_c

/-! ## Singleton specialization -/

/-- Singleton specialization of the linear-budget witness. -/
abbrev P91SingletonExpSizeWeightLinearBudgetWitness
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L) :=
  P91ExpSizeWeightLinearBudgetWitness
    N_c ({X} : Finset (Polymer d L)) K a

/-- Singleton closure from the simpler linear-budget witness. -/
theorem clayTheorem_of_p91SingletonExpSizeWeightLinearBudgetWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (wit : P91SingletonExpSizeWeightLinearBudgetWitness N_c K a X) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_p91ExpSizeWeightLinearBudgetWitness
    ({X} : Finset (Polymer d L)) K a wit

/-- Concrete singleton theorem:
P91 recursion data + a scalar budget envelope + a linear target fit
yield both AF-side rate decay and terminal Clay closure. -/
theorem p91_rate_and_clay_of_kpSingletonLinearBudgetEnvelope
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
    (hfit :
      B ≤ theoreticalBudget ({X} : Finset (Polymer d L)) K a)
    (htarget :
      theoreticalBudget ({X} : Finset (Polymer d L)) K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) ∧
      YangMills.ClayYangMillsTheorem := by
  exact p91_rate_and_clay_of_kpSingletonBudgetEnvelope
    data β r hβ0 hstep hr hβ_upper
    K a B X ha hKP haB hB_nonneg
    (logfit_of_linearBudgetFit hB_nonneg hfit)
    htarget hN_c

end

end YangMills.ClayCore

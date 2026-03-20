import Mathlib
import YangMills.ClayCore.BalabanRG.KPExpSizeWeightLogBudgetToClay

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91ExpSizeWeightLogBudgetWitness — Layer 17W

Producer-side witness target for future P91 / AF closures.

Honest role:
* this file does **not** derive the witness from `P91RecursionData`,
* instead it packages the exact object that a future P91-side producer must
  manufacture in order to trigger the already-green terminal theorem
  `clayTheorem_of_kpExpSizeWeightBudget_logFit`.

So this is the correct "meeting point" between:
* upstream P91 / AF / Cauchy producers, and
* downstream KP exp-size-weight terminal closures.
-/

noncomputable section

/-- Exact producer-side witness needed to close the exp-size-weight KP route
through the logarithmic budget-fit theorem. -/
structure P91ExpSizeWeightLogBudgetWitness
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
  logfit :
    Real.log (1 + B) ≤ theoreticalBudget Gamma K a
  target_lt_log2 :
    theoreticalBudget Gamma K a < Real.log 2
  rank_ok : 2 ≤ N_c

/-- Main consumer theorem:
once a P91-side producer yields the witness below, the exp-size-weight KP lane
closes `ClayYangMillsTheorem`. -/
theorem clayTheorem_of_p91ExpSizeWeightLogBudgetWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : P91ExpSizeWeightLogBudgetWitness N_c Gamma K a) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_kpExpSizeWeightBudget_logFit
    Gamma K a wit.B
    wit.a_nonneg
    wit.B_nonneg
    wit.budget_le
    wit.logfit
    wit.target_lt_log2
    wit.rank_ok

/-- The witness exposes the exact weighted budget bound needed by the terminal
log-budget closure. -/
theorem kpWeightedBudget_le_of_p91ExpSizeWeightLogBudgetWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : P91ExpSizeWeightLogBudgetWitness N_c Gamma K a) :
    KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ wit.B := by
  exact wit.budget_le

/-- The witness exposes the logarithmic target fit expected by the terminal
closure. -/
theorem logfit_of_p91ExpSizeWeightLogBudgetWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (wit : P91ExpSizeWeightLogBudgetWitness N_c Gamma K a) :
    Real.log (1 + wit.B) ≤ theoreticalBudget Gamma K a := by
  exact wit.logfit

/-- Convenience constructor from raw scalar data. -/
def p91ExpSizeWeightLogBudgetWitness_mk
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a B : ℝ)
    (ha_nonneg : 0 ≤ a)
    (hB_nonneg : 0 ≤ B)
    (hbudget :
      KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hlogfit :
      Real.log (1 + B) ≤ theoreticalBudget Gamma K a)
    (htarget :
      theoreticalBudget Gamma K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    P91ExpSizeWeightLogBudgetWitness N_c Gamma K a where
  a_nonneg := ha_nonneg
  B := B
  B_nonneg := hB_nonneg
  budget_le := hbudget
  logfit := hlogfit
  target_lt_log2 := htarget
  rank_ok := hN_c

/-! ## Singleton specialization -/

/-- Singleton producer-side witness. -/
abbrev P91SingletonExpSizeWeightLogBudgetWitness
    {d : ℕ} {L : ℤ}
    (N_c : ℕ) [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L) :=
  P91ExpSizeWeightLogBudgetWitness
    N_c ({X} : Finset (Polymer d L)) K a

/-- Singleton closure from the producer-side witness. -/
theorem clayTheorem_of_p91SingletonExpSizeWeightLogBudgetWitness
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (wit : P91SingletonExpSizeWeightLogBudgetWitness N_c K a X) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_p91ExpSizeWeightLogBudgetWitness
    ({X} : Finset (Polymer d L)) K a wit

/-- Concrete singleton KP constructor:
a future P91-side producer only needs to prove a scalar bound `a ≤ B`
and the logarithmic fit `log(1+B) ≤ theoreticalBudget`, since the singleton
weighted budget is already bounded by `a` from KP. -/
theorem clayTheorem_of_kpSingleton_via_p91BudgetEnvelope
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
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
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_p91SingletonExpSizeWeightLogBudgetWitness
    (K := K) (a := a) (X := X)
    (p91ExpSizeWeightLogBudgetWitness_mk
      N_c ({X} : Finset (Polymer d L)) K a B
      ha hB_nonneg
      (le_trans
        (kpWeightedInductionBudget_singleton_expSizeWeight_le
          (d := d) (L := L) K a X hKP)
        haB)
      hlogfit htarget hN_c)

end

end YangMills.ClayCore

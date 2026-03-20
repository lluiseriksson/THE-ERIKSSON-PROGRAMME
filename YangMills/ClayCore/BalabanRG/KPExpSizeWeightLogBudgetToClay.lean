import Mathlib
import YangMills.ClayCore.BalabanRG.KPExpSizeWeightToClay

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPExpSizeWeightLogBudgetToClay — Layer 16W

Logarithmic budget-fit wrappers for the concrete exponential-size-weight route.

Purpose:
* replace the exponential target-fit condition
    `B ≤ exp(theoreticalBudget) - 1`
  by the equivalent more ergonomic logarithmic form
    `log (1 + B) ≤ theoreticalBudget`,
* expose this both for general weighted budgets and for the concrete singleton
  KP route,
* reduce the scalar plumbing expected from future AF / P91-facing producers.

This adds no new mathematics.
It is a monotonicity wrapper around the already-green file
`KPExpSizeWeightToClay.lean`.
-/

noncomputable section

/-- Log-budget fit implies the exponential target fit used by the terminal
exp-size-weight closure. -/
theorem exp_budget_fit_of_log_budget_fit
    {B t : ℝ}
    (hB : 0 ≤ B)
    (hlog : Real.log (1 + B) ≤ t) :
    B ≤ Real.exp t - 1 := by
  have h1Bpos : 0 < 1 + B := by linarith
  have hexp : Real.exp (Real.log (1 + B)) ≤ Real.exp t := by
    exact Real.exp_le_exp.mpr hlog
  have hEq : Real.exp (Real.log (1 + B)) = 1 + B := by
    rw [Real.exp_log h1Bpos]
  linarith

/-- Logarithmic version of the direct exp-size-weight budget closure. -/
theorem clayTheorem_of_expSizeWeightBudget_logFit
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native a_weight B : ℝ)
    (ha : 0 ≤ a_weight)
    (hB_nonneg : 0 ≤ B)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L) ≤ B)
    (hlogfit : Real.log (1 + B) ≤ theoreticalBudget Gamma K a_native)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    YangMills.ClayYangMillsTheorem := by
  apply clayTheorem_of_expSizeWeightBudget
    Gamma K a_native a_weight ha ?_ hb hN_c
  exact le_trans hB (exp_budget_fit_of_log_budget_fit hB_nonneg hlogfit)

/-- KP-shaped logarithmic closure where the same parameter `a` controls the
weight and the native target budget. -/
theorem clayTheorem_of_kpExpSizeWeightBudget_logFit
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a B : ℝ)
    (ha : 0 ≤ a)
    (hB_nonneg : 0 ≤ B)
    (hB : KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) ≤ B)
    (hlogfit : Real.log (1 + B) ≤ theoreticalBudget Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_expSizeWeightBudget_logFit
    Gamma K a a B ha hB_nonneg hB hlogfit hb hN_c

/-- Singleton weighted-budget closure in logarithmic form. -/
theorem clayTheorem_of_singleton_expSizeWeightBudget_logFit
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d L)
    (a B : ℝ)
    (X : Polymer d L)
    (ha : 0 ≤ a)
    (hB_nonneg : 0 ≤ B)
    (hB :
      KPWeightedInductionBudget ({X} : Finset (Polymer d L))
        K (kpExpSizeWeight a d L) ≤ B)
    (hlogfit :
      Real.log (1 + B) ≤ theoreticalBudget ({X} : Finset (Polymer d L)) K a)
    (hb :
      theoreticalBudget ({X} : Finset (Polymer d L)) K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_kpExpSizeWeightBudget_logFit
    ({X} : Finset (Polymer d L)) K a B ha hB_nonneg hB hlogfit hb hN_c

/-- First concrete KP singleton terminal theorem in logarithmic form:
Kotecký–Preiss on a singleton support closes the route once `log(1+a)` fits
below the native target budget. -/
theorem clayTheorem_of_kpSingleton_expSizeWeight_logFit
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (ha : 0 ≤ a)
    (hKP : KoteckyPreiss K a)
    (hlogfit :
      Real.log (1 + a) ≤ theoreticalBudget ({X} : Finset (Polymer d L)) K a)
    (hb :
      theoreticalBudget ({X} : Finset (Polymer d L)) K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    YangMills.ClayYangMillsTheorem := by
  apply clayTheorem_of_singleton_expSizeWeightBudget_logFit
    (K := K) (a := a) (B := a) (X := X)
    ha ha ?_ hlogfit hb hN_c
  exact kpWeightedInductionBudget_singleton_expSizeWeight_le
    (d := d) (L := L) K a X hKP

end

end YangMills.ClayCore

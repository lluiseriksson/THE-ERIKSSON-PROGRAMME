import Mathlib
import YangMills.ClayCore.BalabanRG.KPExpSizeWeightLogBudgetToClay
import YangMills.ClayCore.BalabanRG.KPWeightedBudgetToPartition

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPExpSizeWeightDirectBudgetToClay — Layer 20W

Direct-budget terminal closures for the concrete exp-size-weight KP route.

Purpose:
* remove the extra scalar envelope `B`,
* let upstream producers target the most natural condition
    `KPWeightedInductionBudget ... ≤ theoreticalBudget ...`,
* retain the already-green terminal closure through the logarithmic wrapper.

This adds no new mathematics.
It just packages the observation that the exp-size-weight weighted budget is
nonnegative, so we may choose `B := theoreticalBudget ...`.
-/

noncomputable section

/-- Generic nonnegativity of the weighted induction budget from pointwise
nonnegative weights. -/
theorem kpWeightedInductionBudget_nonneg_of_nonneg
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (w : KPWeightedActivity d L)
    (hw : KPWeightNonneg d L w) :
    0 ≤ KPWeightedInductionBudget Gamma K w := by
  unfold KPWeightedInductionBudget
  refine Finset.sum_nonneg ?_
  intro S hS
  exact kpWeightedFamilyWeight_nonneg K w hw S

/-- The exp-size-weight weighted induction budget is always nonnegative when
`a ≥ 0`. -/
theorem kpWeightedInductionBudget_nonneg_expSizeWeight
    {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (ha : 0 ≤ a) :
    0 ≤ KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L) := by
  apply kpWeightedInductionBudget_nonneg_of_nonneg
  exact kpWeightNonneg_of_ge_one
    (kpExpSizeWeight_ge_one_interface a ha)

/-- If `T ≥ 0`, then `log (1 + T) ≤ T`. -/
theorem log_one_add_le_self_of_nonneg
    {T : ℝ}
    (hT : 0 ≤ T) :
    Real.log (1 + T) ≤ T := by
  have hpos : 0 < 1 + T := by linarith
  have hlog : Real.log (1 + T) ≤ (1 + T) - 1 := by
    exact log_le_sub_one_of_pos (1 + T) hpos
  linarith

/-- Direct closure from the concrete exp-size-weight budget to
`ClayYangMillsTheorem`, with no extra scalar envelope parameter. -/
theorem clayTheorem_of_expSizeWeightDirectBudget
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a_native a_weight : ℝ)
    (ha : 0 ≤ a_weight)
    (hfit :
      KPWeightedInductionBudget Gamma K (kpExpSizeWeight a_weight d L)
        ≤ theoreticalBudget Gamma K a_native)
    (hb : theoreticalBudget Gamma K a_native < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    YangMills.ClayYangMillsTheorem := by
  have hT_nonneg : 0 ≤ theoreticalBudget Gamma K a_native := by
    exact le_trans
      (kpWeightedInductionBudget_nonneg_expSizeWeight Gamma K a_weight ha)
      hfit
  exact clayTheorem_of_expSizeWeightBudget_logFit
    Gamma K a_native a_weight (theoreticalBudget Gamma K a_native)
    ha
    hT_nonneg
    hfit
    (log_one_add_le_self_of_nonneg hT_nonneg)
    hb
    hN_c

/-- KP-shaped specialization using the same parameter `a` for both the weight
and the native target budget. -/
theorem clayTheorem_of_kpExpSizeWeightDirectBudget
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (Gamma : Finset (Polymer d L))
    (K : Activity d L)
    (a : ℝ)
    (ha : 0 ≤ a)
    (hfit :
      KPWeightedInductionBudget Gamma K (kpExpSizeWeight a d L)
        ≤ theoreticalBudget Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_expSizeWeightDirectBudget
    Gamma K a a ha hfit hb hN_c

/-- Direct singleton closure from a weighted induction-budget fit. -/
theorem clayTheorem_of_singletonExpSizeWeightDirectBudget
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (ha : 0 ≤ a)
    (hfit :
      KPWeightedInductionBudget ({X} : Finset (Polymer d L))
        K (kpExpSizeWeight a d L)
        ≤ theoreticalBudget ({X} : Finset (Polymer d L)) K a)
    (hb :
      theoreticalBudget ({X} : Finset (Polymer d L)) K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    YangMills.ClayYangMillsTheorem := by
  exact clayTheorem_of_kpExpSizeWeightDirectBudget
    ({X} : Finset (Polymer d L)) K a ha hfit hb hN_c

/-- First concrete singleton KP theorem with the direct target-budget fit:
the singleton exp-size-weight weighted budget is bounded by `a`, so it suffices
to prove `a ≤ theoreticalBudget`. -/
theorem clayTheorem_of_kpSingleton_expSizeWeight_directBudget
    {d : ℕ} {L : ℤ}
    {N_c : ℕ} [NeZero N_c]
    (K : Activity d L)
    (a : ℝ)
    (X : Polymer d L)
    (ha : 0 ≤ a)
    (hKP : KoteckyPreiss K a)
    (hfit :
      a ≤ theoreticalBudget ({X} : Finset (Polymer d L)) K a)
    (hb :
      theoreticalBudget ({X} : Finset (Polymer d L)) K a < Real.log 2)
    (hN_c : 2 ≤ N_c) :
    YangMills.ClayYangMillsTheorem := by
  apply clayTheorem_of_singletonExpSizeWeightDirectBudget
    (K := K) (a := a) (X := X) ha ?_ hb hN_c
  exact le_trans
    (kpWeightedInductionBudget_singleton_expSizeWeight_le
      (d := d) (L := L) K a X hKP)
    hfit

end

end YangMills.ClayCore

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedWeightedRowKernel

/-!
# Weighted rows from normalized row sums

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

This adapter preserves an already proved row normalization.  Finite range is
used only to bound the exponential weight; no range-ball cardinality is
introduced.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- An unweighted row-sum bound and finite range give a fixed-rate weighted
row bound with only the maximal exponential weight as cost. -/
theorem finitePiLpTypedWeightedRowKernelBound_of_rowSum_and_finiteRange
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) (range : ℕ) {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 ≤ rate)
    (hfinite : FinitePiLpTypedFiniteRange T dist range)
    (hrow : ∀ source (v : g),
      ∑ target : κ, ‖T (singleFinitePiLp source v) target‖ ≤ A * ‖v‖) :
    FinitePiLpTypedWeightedRowKernelBound T dist
      (Real.exp (rate * (range : ℝ)) * A) rate := by
  refine ⟨mul_nonneg (Real.exp_pos _).le hA, hrate, ?_⟩
  intro source v
  calc
    ∑ target : κ,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T (singleFinitePiLp source v) target‖
        ≤ ∑ target : κ,
            Real.exp (rate * (range : ℝ)) *
              ‖T (singleFinitePiLp source v) target‖ := by
          apply Finset.sum_le_sum
          intro target _
          by_cases hfar : range < dist target source
          · rw [hfinite source target v hfar, norm_zero, mul_zero, mul_zero]
          · have hdist : (dist target source : ℝ) ≤ (range : ℝ) := by
              exact_mod_cast Nat.le_of_not_gt hfar
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left hdist hrate
    _ = Real.exp (rate * (range : ℝ)) *
          ∑ target : κ, ‖T (singleFinitePiLp source v) target‖ := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (rate * (range : ℝ)) * (A * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hrow source v) (Real.exp_pos _).le
    _ = (Real.exp (rate * (range : ℝ)) * A) * ‖v‖ := by ring

end

end YangMills.RG

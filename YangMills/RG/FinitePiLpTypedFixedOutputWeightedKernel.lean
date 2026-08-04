/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedKernel

/-!
# Fixed-output weighted sums for rectangular finite kernels

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

CMP99 (3.88) fixes the displayed output coordinate and sums over input
coordinates.  This is not the source-fixed convention of
`FinitePiLpTypedWeightedRowKernelBound`.  For vector-valued kernels the two
predicates do not follow from self-adjointness alone: adjunction transposes
each fibre block, while a sum of norms evaluated on one common vector need
not be preserved.

This file therefore records the printed orientation as a separate predicate.
Only direct finite-range, row-sum, scalar, and addition rules are supplied;
there is deliberately no generic self-adjoint transport theorem.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- A fixed-output weighted estimate.  The target is fixed and the sum runs
over source coordinates, matching the orientation printed in CMP99 (3.88). -/
def FinitePiLpTypedFixedOutputWeightedKernelBound
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) (A rate : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ rate ∧
    ∀ target (v : g),
      ∑ source : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T (singleFinitePiLp source v) target‖ ≤
        A * ‖v‖

/-- A finite-range pointwise kernel bound gives a fixed-output weighted sum
once the number of sources in every output-centred range ball is controlled.
-/
theorem finitePiLpTypedFixedOutputWeightedKernelBound_of_finiteRange
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) (R C : ℕ) {beta rate : ℝ}
    (hbeta : 0 ≤ beta) (hrate : 0 ≤ rate)
    (hrange : FinitePiLpTypedFiniteRange T dist R)
    (hbound : FinitePiLpTypedKernelBound T (fun _ _ => beta))
    (hcard : ∀ target,
      (Finset.univ.filter (fun source : ι => dist target source ≤ R)).card ≤ C) :
    FinitePiLpTypedFixedOutputWeightedKernelBound T dist
      (beta * Real.exp (rate * (R : ℝ)) * C) rate := by
  classical
  refine ⟨mul_nonneg (mul_nonneg hbeta (Real.exp_pos _).le)
      (Nat.cast_nonneg C), hrate, ?_⟩
  intro target v
  let near := Finset.univ.filter (fun source : ι => dist target source ≤ R)
  let f := fun source : ι =>
    Real.exp (rate * (dist target source : ℝ)) *
      ‖T (singleFinitePiLp source v) target‖
  have hsumNear : (∑ source : ι, f source) = ∑ source ∈ near, f source := by
    refine (Finset.sum_subset (Finset.subset_univ near) ?_).symm
    intro source _ hsource
    have hnear : ¬dist target source ≤ R := by
      simpa [near] using hsource
    have hfar : R < dist target source := Nat.lt_of_not_ge hnear
    dsimp [f]
    rw [hrange source target v hfar]
    simp
  rw [hsumNear]
  calc
    ∑ source ∈ near, f source ≤
        ∑ _source ∈ near,
          (beta * Real.exp (rate * (R : ℝ))) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro source hsource
      have hdist : dist target source ≤ R := (Finset.mem_filter.mp hsource).2
      have hdistReal : (dist target source : ℝ) ≤ (R : ℝ) := by
        exact_mod_cast hdist
      have hexp :
          Real.exp (rate * (dist target source : ℝ)) ≤
            Real.exp (rate * (R : ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hdistReal hrate
      calc
        f source ≤ Real.exp (rate * (dist target source : ℝ)) *
            (beta * ‖v‖) :=
          mul_le_mul_of_nonneg_left (hbound source target v)
            (Real.exp_pos _).le
        _ ≤ Real.exp (rate * (R : ℝ)) * (beta * ‖v‖) :=
          mul_le_mul_of_nonneg_right hexp
            (mul_nonneg hbeta (norm_nonneg v))
        _ = (beta * Real.exp (rate * (R : ℝ))) * ‖v‖ := by ring
    _ = (near.card : ℝ) *
        ((beta * Real.exp (rate * (R : ℝ))) * ‖v‖) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C : ℝ) *
        ((beta * Real.exp (rate * (R : ℝ))) * ‖v‖) := by
      gcongr
      exact_mod_cast hcard target
    _ = (beta * Real.exp (rate * (R : ℝ)) * C) * ‖v‖ := by ring

/-- A normalized fixed-output sum and finite range pay only the maximal
exponential weight, with no range-ball cardinality. -/
theorem finitePiLpTypedFixedOutputWeightedKernelBound_of_outputSum_and_finiteRange
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) (range : ℕ) {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 ≤ rate)
    (hfinite : FinitePiLpTypedFiniteRange T dist range)
    (hsum : ∀ target (v : g),
      ∑ source : ι, ‖T (singleFinitePiLp source v) target‖ ≤ A * ‖v‖) :
    FinitePiLpTypedFixedOutputWeightedKernelBound T dist
      (Real.exp (rate * (range : ℝ)) * A) rate := by
  refine ⟨mul_nonneg (Real.exp_pos _).le hA, hrate, ?_⟩
  intro target v
  calc
    ∑ source : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T (singleFinitePiLp source v) target‖
        ≤ ∑ source : ι,
            Real.exp (rate * (range : ℝ)) *
              ‖T (singleFinitePiLp source v) target‖ := by
          apply Finset.sum_le_sum
          intro source _
          by_cases hfar : range < dist target source
          · rw [hfinite source target v hfar, norm_zero, mul_zero, mul_zero]
          · have hdist : (dist target source : ℝ) ≤ (range : ℝ) := by
              exact_mod_cast Nat.le_of_not_gt hfar
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left hdist hrate
    _ = Real.exp (rate * (range : ℝ)) *
          ∑ source : ι, ‖T (singleFinitePiLp source v) target‖ := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (rate * (range : ℝ)) * (A * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hsum target v) (Real.exp_pos _).le
    _ = (Real.exp (rate * (range : ℝ)) * A) * ‖v‖ := by ring

/-- Scalar multiplication preserves the printed fixed-output orientation. -/
theorem finitePiLpTypedFixedOutputWeightedKernelBound_smul
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (c : ℝ) {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {dist : κ → ι → ℕ} {A rate : ℝ}
    (hT : FinitePiLpTypedFixedOutputWeightedKernelBound T dist A rate) :
    FinitePiLpTypedFixedOutputWeightedKernelBound
      (c • T) dist (|c| * A) rate := by
  refine ⟨mul_nonneg (abs_nonneg c) hT.1, hT.2.1, ?_⟩
  intro target v
  calc
    (∑ source : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖(c • T) (singleFinitePiLp source v) target‖) =
        |c| * ∑ source : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T (singleFinitePiLp source v) target‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source _
      simp only [ContinuousLinearMap.smul_apply, PiLp.smul_apply, norm_smul,
        Real.norm_eq_abs]
      ring
    _ ≤ |c| * (A * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hT.2.2 target v) (abs_nonneg c)
    _ = (|c| * A) * ‖v‖ := by ring

/-- Two fixed-output bounds at one rate add with their literal amplitudes. -/
theorem finitePiLpTypedFixedOutputWeightedKernelBound_add
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {S T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {dist : κ → ι → ℕ} {A B rate : ℝ}
    (hS : FinitePiLpTypedFixedOutputWeightedKernelBound S dist A rate)
    (hT : FinitePiLpTypedFixedOutputWeightedKernelBound T dist B rate) :
    FinitePiLpTypedFixedOutputWeightedKernelBound
      (S + T) dist (A + B) rate := by
  refine ⟨add_nonneg hS.1 hT.1, hS.2.1, ?_⟩
  intro target v
  calc
    (∑ source : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖(S + T) (singleFinitePiLp source v) target‖) ≤
        ∑ source : ι,
          (Real.exp (rate * (dist target source : ℝ)) *
              ‖S (singleFinitePiLp source v) target‖ +
            Real.exp (rate * (dist target source : ℝ)) *
              ‖T (singleFinitePiLp source v) target‖) := by
      apply Finset.sum_le_sum
      intro source _
      rw [ContinuousLinearMap.add_apply, PiLp.add_apply]
      simpa only [mul_add] using
        (mul_le_mul_of_nonneg_left
          (norm_add_le
            (S (singleFinitePiLp source v) target)
            (T (singleFinitePiLp source v) target))
          (Real.exp_pos (rate * (dist target source : ℝ))).le)
    _ = (∑ source : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖S (singleFinitePiLp source v) target‖) +
        ∑ source : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T (singleFinitePiLp source v) target‖ := by
      rw [Finset.sum_add_distrib]
    _ ≤ A * ‖v‖ + B * ‖v‖ :=
      add_le_add (hS.2.2 target v) (hT.2.2 target v)
    _ = (A + B) * ‖v‖ := by ring

end

end YangMills.RG

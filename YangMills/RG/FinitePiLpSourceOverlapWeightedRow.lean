/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedWeightedRowKernel

/-!
# Source-overlap sums of weighted rows

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

The rightmost cutoff in the regional CMP99 defect kills every inactive cell
before the row sum is taken.  Thus a family with source overlap `N` pays `N`,
not the total number of cells and not a second analytic overlap constant.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- A source-supported family of weighted-row kernels sums with its literal
source-overlap bound. -/
theorem finitePiLpTypedWeightedRowKernelBound_sum_of_sourceOverlap
    {ι g n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (term : n → FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (active : n → ι → Prop) [DecidableRel active]
    (dist : ι → ι → ℕ)
    {N : ℕ} {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 ≤ rate)
    (hoverlap : ∀ source,
      (Finset.univ.filter fun i => active i source).card ≤ N)
    (hsupport : ∀ i source (v : g), ¬ active i source →
      term i (singleFinitePiLp source v) = 0)
    (hterm : ∀ i,
      FinitePiLpTypedWeightedRowKernelBound (term i) dist A rate) :
    FinitePiLpTypedWeightedRowKernelBound
      (∑ i, term i) dist ((N : ℝ) * A) rate := by
  classical
  refine ⟨mul_nonneg (Nat.cast_nonneg N) hA, hrate, ?_⟩
  intro source v
  let supported : Finset n := Finset.univ.filter fun i => active i source
  have hcolumn :
      (∑ i, term i) (singleFinitePiLp source v) =
        ∑ i ∈ supported, term i (singleFinitePiLp source v) := by
    rw [ContinuousLinearMap.sum_apply]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    rw [hsupport i source v]
    simpa [supported] using hnot
  rw [hcolumn]
  calc
    ∑ target : ι,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖(∑ i ∈ supported,
              term i (singleFinitePiLp source v)) target‖
        ≤ ∑ target : ι,
            ∑ i ∈ supported,
              Real.exp (rate * (dist target source : ℝ)) *
                ‖term i (singleFinitePiLp source v) target‖ := by
          apply Finset.sum_le_sum
          intro target _
          rw [WithLp.ofLp_sum, Finset.sum_apply]
          calc
            Real.exp (rate * (dist target source : ℝ)) *
                ‖∑ i ∈ supported,
                  term i (singleFinitePiLp source v) target‖
              ≤ Real.exp (rate * (dist target source : ℝ)) *
                  ∑ i ∈ supported,
                    ‖term i (singleFinitePiLp source v) target‖ :=
                mul_le_mul_of_nonneg_left (norm_sum_le _ _)
                  (Real.exp_pos _).le
            _ = ∑ i ∈ supported,
                  Real.exp (rate * (dist target source : ℝ)) *
                    ‖term i (singleFinitePiLp source v) target‖ := by
                rw [Finset.mul_sum]
    _ = ∑ i ∈ supported,
          ∑ target : ι,
            Real.exp (rate * (dist target source : ℝ)) *
              ‖term i (singleFinitePiLp source v) target‖ := by
        rw [Finset.sum_comm]
    _ ≤ ∑ _i ∈ supported, A * ‖v‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact (hterm i).2.2 source v
    _ = (supported.card : ℝ) * (A * ‖v‖) := by
        simp
    _ ≤ (N : ℝ) * (A * ‖v‖) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hoverlap source
        · exact mul_nonneg hA (norm_nonneg v)
    _ = ((N : ℝ) * A) * ‖v‖ := by ring

end

end YangMills.RG

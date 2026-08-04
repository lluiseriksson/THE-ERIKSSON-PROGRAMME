/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedKernel

/-!
# Source-overlap bounds for finite families of kernels

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

A family of localized operators must not pay for the total number of charts.
The theorem below records the weaker hypothesis needed by the CMP99 regional
defect: for every source coordinate, at most `N` family members act on a
one-site probe at that source.  A common exponential kernel bound then sums
with the factor `N`, independently of the ambient volume.

The active predicate and its cardinality bound belong to the same family;
there is no second overlap constant hidden in the analytic estimate.
-/

namespace YangMills.RG

noncomputable section

/-- A source-supported finite family with overlap at most `N` inherits a
uniform exponential kernel bound with amplitude `N * A`.

The support premise is an exact vanishing statement on one-site probes.  In
the CMP99 specialization it is produced by the rightmost multiplier `h_Pi`,
so the family sum is restricted before either Schur direction is estimated.
-/
theorem finitePiLpExponentialKernelBound_sum_of_sourceOverlap
    {ι g n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (term : n →
      (FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g))
    (active : n → ι → Prop) [DecidableRel active]
    (dist : ι → ι → ℕ) {N : ℕ} {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 < rate)
    (hoverlap : ∀ source,
      (Finset.univ.filter fun i => active i source).card ≤ N)
    (hsupport : ∀ i source (v : g), ¬ active i source →
      term i (singleFinitePiLp source v) = 0)
    (hterm : ∀ i,
      FinitePiLpExponentialKernelBound (term i) dist A rate) :
    FinitePiLpExponentialKernelBound
      (∑ i, term i) dist ((N : ℝ) * A) rate := by
  classical
  refine ⟨mul_nonneg (by positivity) hA, hrate, ?_⟩
  intro source target v
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
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  calc
    ‖∑ i ∈ supported,
        term i (singleFinitePiLp source v) target‖ ≤
        ∑ i ∈ supported,
          ‖term i (singleFinitePiLp source v) target‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ supported,
        A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hterm i).2.2 source target v
    _ = (supported.card : ℝ) *
        (A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖) := by
      simp
    _ ≤ (N : ℝ) *
        (A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hoverlap source
      · exact mul_nonneg
          (mul_nonneg hA (Real.exp_pos _).le) (norm_nonneg v)
    _ = ((N : ℝ) * A) *
        Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ := by
      ring

end

end YangMills.RG

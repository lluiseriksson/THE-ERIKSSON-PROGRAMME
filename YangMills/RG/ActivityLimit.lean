/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Uniform activity bounds pass to pointwise limits

This tiny bridge packages a common decoupling/regularisation pattern: if a
family of activities has a profile bound uniformly in the regulator and
converges pointwise, then the limiting activity obeys the same profile.

It is intentionally abstract.  It does not prove any supersymmetric
decoupling, heavy-fermion expansion, or Yang--Mills activity estimate; it only
records the topological consumer once those estimates are supplied.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

/-- A pointwise limit of uniformly profile-bounded complex activities obeys the
same profile bound. -/
theorem activity_profile_bound_of_tendsto
    {ι : Type*} (z : ℕ → ι → ℂ) (zLim : ι → ℂ) (profile : ι → ℝ)
    (hbound : ∀ n X, ‖z n X‖ ≤ profile X)
    (hlim : ∀ X, Filter.Tendsto (fun n : ℕ => z n X) Filter.atTop (nhds (zLim X))) :
    ∀ X, ‖zLim X‖ ≤ profile X := by
  intro X
  exact le_of_tendsto' ((hlim X).norm) (fun n => hbound n X)

/-- Finite telescopic profile bound.  If the initial activity is bounded by
`amp * profile` and each regulator step is bounded by `B n * profile`, then the
`N`-th activity is bounded by `(amp + ∑_{n<N} B n) * profile`. -/
theorem activity_profile_bound_of_finite_telescope
    {ι : Type*} (z : ℕ → ι → ℂ) (profile : ι → ℝ) (amp : ℝ) (B : ℕ → ℝ)
    (hbase : ∀ X, ‖z 0 X‖ ≤ amp * profile X)
    (hstep : ∀ n X, ‖z (n + 1) X - z n X‖ ≤ B n * profile X) :
    ∀ N X, ‖z N X‖ ≤ (amp + ∑ n ∈ Finset.range N, B n) * profile X := by
  intro N
  induction N with
  | zero =>
      intro X
      simpa using hbase X
  | succ N ih =>
      intro X
      calc
        ‖z (N + 1) X‖
            = ‖z N X + (z (N + 1) X - z N X)‖ := by
                congr 1
                abel
        _ ≤ ‖z N X‖ + ‖z (N + 1) X - z N X‖ := norm_add_le _ _
        _ ≤ (amp + ∑ n ∈ Finset.range N, B n) * profile X + B N * profile X :=
            add_le_add (ih X) (hstep N X)
        _ = (amp + ∑ n ∈ Finset.range (N + 1), B n) * profile X := by
            rw [Finset.sum_range_succ]
            ring

/-- A telescopic regulator limit obeys the initial profile plus the summable
step-defect budget.  This is the abstract consumer for regulator-removal or
decoupling arguments: once the pointwise increments are profile-bounded by a
summable sequence, the limiting activity has amplitude `amp + S`. -/
theorem activity_profile_bound_of_tendsto_telescope
    {ι : Type*} (z : ℕ → ι → ℂ) (zLim : ι → ℂ) (profile : ι → ℝ)
    (amp S : ℝ) (B : ℕ → ℝ)
    (hprofile : ∀ X, 0 ≤ profile X)
    (hbase : ∀ X, ‖z 0 X‖ ≤ amp * profile X)
    (hstep : ∀ n X, ‖z (n + 1) X - z n X‖ ≤ B n * profile X)
    (hB : ∀ n, 0 ≤ B n)
    (hBsum : Summable B)
    (hS : (∑' n, B n) ≤ S)
    (hlim : ∀ X, Filter.Tendsto (fun n : ℕ => z n X) Filter.atTop (nhds (zLim X))) :
    ∀ X, ‖zLim X‖ ≤ (amp + S) * profile X := by
  intro X
  refine le_of_tendsto' ((hlim X).norm) ?_
  intro N
  have hfinite :=
    activity_profile_bound_of_finite_telescope z profile amp B hbase hstep N X
  have hpartial : ∑ n ∈ Finset.range N, B n ≤ S :=
    (hBsum.sum_le_tsum (Finset.range N) (fun n _ => hB n)).trans hS
  exact hfinite.trans
    (mul_le_mul_of_nonneg_right (add_le_add_right hpartial amp) (hprofile X))

end YangMills.RG

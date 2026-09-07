/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalWeightedRowKernel

/-!
# Infinite sums of fixed-rate weighted-row kernels

An absolutely summable nonnegative amplitude majorant passes through a
summable operator series.  The proof first evaluates the operator `tsum`,
then uses absolute convergence supplied by the row majorant itself.  No
cardinality of the ambient bond space enters the resulting amplitude.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- A summable family of operators with a summable common-rate row majorant
has the `tsum` of those amplitudes as a weighted-row bound. -/
theorem physicalCovarianceWeightedRowKernelBound_tsum
    {d N Nc : ℕ} [NeZero N]
    (T : ℕ → PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (A : ℕ → ℝ) {rate : ℝ}
    (hT : Summable T)
    (hA : Summable A)
    (hAn : ∀ n, 0 ≤ A n)
    (hrate : 0 ≤ rate)
    (hbound : ∀ n,
      PhysicalCovarianceWeightedRowKernelBound (T n) dist (A n) rate) :
    PhysicalCovarianceWeightedRowKernelBound
      (∑' n, T n) dist (∑' n, A n) rate := by
  refine ⟨tsum_nonneg hAn, hrate, ?_⟩
  intro source v
  let delta := singlePhysicalBondCochain
    (d := d) (N := N) (Nc := Nc) source v
  let E := PhysicalGaugeOneCochain d N Nc
  let siteEval (target : PhysicalBond d N) : E →L[ℝ] SUNLieCoord Nc :=
    (ContinuousLinearMap.proj target).comp
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : PhysicalBond d N => SUNLieCoord Nc)).toContinuousLinearMap
  let evalCLM (target : PhysicalBond d N) :
      PhysicalEndomorphism d N Nc →L[ℝ] SUNLieCoord Nc :=
    (siteEval target).comp (ContinuousLinearMap.apply ℝ E delta)
  have heval (target : PhysicalBond d N)
      (S : PhysicalEndomorphism d N Nc) :
      evalCLM target S = S delta target := by
    rfl
  have hrewrite (target : PhysicalBond d N) :
      (∑' n, T n) delta target = ∑' n, T n delta target := by
    simpa only [heval] using (evalCLM target).map_tsum hT
  have hmajor : Summable (fun n => A n * ‖v‖) :=
    hA.mul_right ‖v‖
  have hterm_le (n : ℕ) (target : PhysicalBond d N) :
      ‖T n delta target‖ ≤ A n * ‖v‖ := by
    have hrow :
        (∑ q : PhysicalBond d N,
          Real.exp (rate * (dist q source : ℝ)) *
            ‖T n delta q‖) ≤ A n * ‖v‖ := by
      simpa only [delta] using (hbound n).2.2 source v
    have hself :
        ‖T n delta target‖ ≤
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T n delta target‖ := by
      apply le_mul_of_one_le_left (norm_nonneg _)
      exact Real.one_le_exp
        (mul_nonneg hrate (Nat.cast_nonneg _))
    exact hself.trans <|
      (Finset.single_le_sum
        (fun q _ => mul_nonneg
          (Real.exp_pos (rate * (dist q source : ℝ))).le
          (norm_nonneg (T n delta q)))
        (Finset.mem_univ target)).trans hrow
  have hnormSummable (target : PhysicalBond d N) :
      Summable (fun n => ‖T n delta target‖) :=
    Summable.of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => hterm_le n target) hmajor
  have hweightedSummable (target : PhysicalBond d N) :
      Summable (fun n =>
        Real.exp (rate * (dist target source : ℝ)) *
          ‖T n delta target‖) :=
    (hnormSummable target).mul_left
      (Real.exp (rate * (dist target source : ℝ)))
  have hweightedFinsetSummable
      (targets : Finset (PhysicalBond d N)) :
      Summable (fun n =>
        ∑ target ∈ targets,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T n delta target‖) := by
    classical
    induction targets using Finset.induction_on with
    | empty => simp
    | @insert target targets hnot ih =>
        simpa only [Finset.sum_insert hnot] using
          (hweightedSummable target).add ih
  have hrowSummable :
      Summable (fun n =>
        ∑ target : PhysicalBond d N,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T n delta target‖) := by
    refine Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ?_ hmajor
    intro n
    exact (hbound n).2.2 source v
  calc
    ∑ target : PhysicalBond d N,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖(∑' n, T n) delta target‖
        ≤ ∑ target : PhysicalBond d N,
            Real.exp (rate * (dist target source : ℝ)) *
              ∑' n, ‖T n delta target‖ := by
          apply Finset.sum_le_sum
          intro target _
          rw [hrewrite target]
          exact mul_le_mul_of_nonneg_left
            (norm_tsum_le_tsum_norm
              (hnormSummable target))
            (Real.exp_pos _).le
    _ = ∑ target : PhysicalBond d N,
          ∑' n, Real.exp (rate * (dist target source : ℝ)) *
            ‖T n delta target‖ := by
        apply Finset.sum_congr rfl
        intro target _
        rw [tsum_mul_left]
    _ = ∑' n, ∑ target : PhysicalBond d N,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T n delta target‖ := by
        classical
        induction (Finset.univ : Finset (PhysicalBond d N)) using Finset.induction_on with
        | empty => simp
        | @insert target targets hnot ih =>
            rw [Finset.sum_insert hnot, ih,
              ← (hweightedSummable target).tsum_add
                (hweightedFinsetSummable targets)]
            apply tsum_congr
            intro n
            rw [Finset.sum_insert hnot]
    _ ≤ ∑' n, A n * ‖v‖ :=
      hrowSummable.tsum_le_tsum
        (fun n => (hbound n).2.2 source v) hmajor
    _ = (∑' n, A n) * ‖v‖ := tsum_mul_right

end

end YangMills.RG

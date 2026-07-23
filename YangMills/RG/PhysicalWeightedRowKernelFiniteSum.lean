/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalWeightedRowKernel

/-!
# Finite sums in the physical weighted-row norm

The weighted-row amplitude of a finite operator sum is bounded by the sum of
the individual amplitudes.  A uniform amplitude therefore costs exactly the
cardinality of the finite index family.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Enlarge the weighted-row amplitude without changing the spatial rate. -/
theorem physicalCovarianceWeightedRowKernelBound_mono_amplitude
    {d N Nc : ℕ} [NeZero N]
    {T : PhysicalEndomorphism d N Nc}
    {dist : PhysicalBond d N → PhysicalBond d N → ℕ}
    {A B rate : ℝ}
    (hT : PhysicalCovarianceWeightedRowKernelBound T dist A rate)
    (hAB : A ≤ B) :
    PhysicalCovarianceWeightedRowKernelBound T dist B rate := by
  refine ⟨hT.1.trans hAB, hT.2.1, ?_⟩
  intro source v
  exact (hT.2.2 source v).trans
    (mul_le_mul_of_nonneg_right hAB (norm_nonneg v))

/-- A finite sum of operators with common weighted-row amplitude `A` has
amplitude `s.card * A`. -/
theorem physicalCovarianceWeightedRowKernelBound_finset_sum
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (s : Finset ι) (term : ι → PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A rate : ℝ} (hA : 0 ≤ A) (hrate : 0 ≤ rate)
    (hterm : ∀ i, i ∈ s →
      PhysicalCovarianceWeightedRowKernelBound (term i) dist A rate) :
    PhysicalCovarianceWeightedRowKernelBound
      (∑ i ∈ s, term i) dist ((s.card : ℝ) * A) rate := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hA, hrate, ?_⟩
  intro source v
  let delta := singlePhysicalBondCochain
    (d := d) (N := N) (Nc := Nc) source v
  calc
    ∑ target : PhysicalBond d N,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖(∑ i ∈ s, term i) delta target‖
      ≤ ∑ target : PhysicalBond d N,
          ∑ i ∈ s,
            Real.exp (rate * (dist target source : ℝ)) *
              ‖term i delta target‖ := by
        apply Finset.sum_le_sum
        intro target _
        calc
          Real.exp (rate * (dist target source : ℝ)) *
              ‖(∑ i ∈ s, term i) delta target‖
            ≤ Real.exp (rate * (dist target source : ℝ)) *
                (∑ i ∈ s, ‖term i delta target‖) := by
                  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
                  simp only [ContinuousLinearMap.sum_apply]
                  rw [WithLp.ofLp_sum, Finset.sum_apply]
                  exact norm_sum_le _ _
          _ = ∑ i ∈ s,
                Real.exp (rate * (dist target source : ℝ)) *
                  ‖term i delta target‖ := by
              rw [Finset.mul_sum]
    _ = ∑ i ∈ s,
          ∑ target : PhysicalBond d N,
            Real.exp (rate * (dist target source : ℝ)) *
              ‖term i delta target‖ := by
        rw [Finset.sum_comm]
    _ ≤ ∑ _i ∈ s, A * ‖v‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hterm i hi).2.2 source v
    _ = ((s.card : ℝ) * A) * ‖v‖ := by
        simp
        ring

end

end YangMills.RG

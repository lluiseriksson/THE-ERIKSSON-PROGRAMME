/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedKernel

/-!
# Fixed-rate weighted rows for rectangular finite kernels

CMP99 Section C composes operators whose source, intermediate and target
regional carriers need not coincide.  This file gives the rectangular form of
the weighted-row norm.  Unlike repeated pointwise convolution, its spatial
rate is unchanged by composition; only the amplitudes multiply.

The sum fixes the source and runs over targets.  This orientation is essential
for decomposing the image of a source delta through the intermediate carrier.
-/

namespace YangMills.RG

noncomputable section

/-- A source-fixed weighted-row estimate for a rectangular `PiLp` kernel. -/
def FinitePiLpTypedWeightedRowKernelBound
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) (A rate : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ rate ∧
    ∀ source (v : g),
      ∑ target : κ,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T (singleFinitePiLp source v) target‖ ≤
        A * ‖v‖

/-- Pointwise exponential decay gives a rectangular weighted-row bound at any
lower rate once the corresponding target sum is controlled uniformly. -/
theorem finitePiLpTypedWeightedRowKernelBound_of_exponential
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) {A rate weight S : ℝ}
    (hweight : 0 ≤ weight) (hS : 0 ≤ S)
    (hT : FinitePiLpTypedExponentialKernelBound T dist A rate)
    (hsum : ∀ source,
      ∑ target : κ,
        Real.exp (-((rate - weight) * (dist target source : ℝ))) ≤ S) :
    FinitePiLpTypedWeightedRowKernelBound T dist (A * S) weight := by
  refine ⟨mul_nonneg hT.1 hS, hweight, ?_⟩
  intro source v
  calc
    ∑ target : κ,
          Real.exp (weight * (dist target source : ℝ)) *
            ‖T (singleFinitePiLp source v) target‖
        ≤ ∑ target : κ,
            A * Real.exp (-((rate - weight) *
              (dist target source : ℝ))) * ‖v‖ := by
          apply Finset.sum_le_sum
          intro target _
          calc
            Real.exp (weight * (dist target source : ℝ)) *
                ‖T (singleFinitePiLp source v) target‖
              ≤ Real.exp (weight * (dist target source : ℝ)) *
                  (A * Real.exp (-(rate *
                    (dist target source : ℝ))) * ‖v‖) :=
                mul_le_mul_of_nonneg_left
                  (hT.2.2 source target v) (Real.exp_pos _).le
            _ = A * Real.exp (-((rate - weight) *
                  (dist target source : ℝ))) * ‖v‖ := by
                have hexp :
                    Real.exp (weight * (dist target source : ℝ)) *
                        Real.exp (-(rate * (dist target source : ℝ))) =
                      Real.exp (-((rate - weight) *
                        (dist target source : ℝ))) := by
                  rw [← Real.exp_add]
                  congr 1
                  ring
                calc
                  Real.exp (weight * (dist target source : ℝ)) *
                      (A * Real.exp (-(rate *
                        (dist target source : ℝ))) * ‖v‖) =
                    A * (Real.exp (weight * (dist target source : ℝ)) *
                      Real.exp (-(rate *
                        (dist target source : ℝ)))) * ‖v‖ := by ring
                  _ = A * Real.exp (-((rate - weight) *
                        (dist target source : ℝ))) * ‖v‖ := by rw [hexp]
    _ = (A * ‖v‖) * ∑ target : κ,
          Real.exp (-((rate - weight) *
            (dist target source : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro target _
        ring
    _ ≤ (A * ‖v‖) * S :=
      mul_le_mul_of_nonneg_left (hsum source)
        (mul_nonneg hT.1 (norm_nonneg v))
    _ = (A * S) * ‖v‖ := by ring

/-- Rectangular weighted-row amplitudes multiply under typed composition,
without loss of spatial rate. -/
theorem finitePiLpTypedWeightedRowKernelBound_comp
    {ι κ ν g : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (distLK : ν → κ → ℕ) (distKI : κ → ι → ℕ)
    (distLI : ν → ι → ℕ)
    (htri : ∀ target middle source,
      distLI target source ≤ distLK target middle + distKI middle source)
    {Left : FinitePiLpField κ g →L[ℝ] FinitePiLpField ν g}
    {Right : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {A B rate : ℝ}
    (hLeft : FinitePiLpTypedWeightedRowKernelBound Left distLK A rate)
    (hRight : FinitePiLpTypedWeightedRowKernelBound Right distKI B rate) :
    FinitePiLpTypedWeightedRowKernelBound
      (Left.comp Right) distLI (A * B) rate := by
  classical
  refine ⟨mul_nonneg hLeft.1 hRight.1, hLeft.2.1, ?_⟩
  intro source v
  let probe := singleFinitePiLp source v
  have hdecomp : Right probe =
      ∑ middle : κ, singleFinitePiLp middle (Right probe middle) :=
    (sum_singleFinitePiLp_eq (Right probe)).symm
  have happ : ∀ target,
      (Left.comp Right) probe target =
        ∑ middle : κ,
          Left (singleFinitePiLp middle (Right probe middle)) target := by
    intro target
    calc
      (Left.comp Right) probe target = Left (Right probe) target := rfl
      _ = Left (∑ middle : κ,
          singleFinitePiLp middle (Right probe middle)) target :=
        congrArg (fun w => Left w target) hdecomp
      _ = ∑ middle : κ,
          Left (singleFinitePiLp middle (Right probe middle)) target := by
        rw [map_sum]
        exact finitePiLp_sum_apply _ _ _
  have hweight : ∀ target middle,
      Real.exp (rate * (distLI target source : ℝ)) ≤
        Real.exp (rate * (distLK target middle : ℝ)) *
          Real.exp (rate * (distKI middle source : ℝ)) := by
    intro target middle
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htri' : (distLI target source : ℝ) ≤
        (distLK target middle : ℝ) + (distKI middle source : ℝ) := by
      exact_mod_cast htri target middle source
    calc
      rate * (distLI target source : ℝ) ≤
          rate * ((distLK target middle : ℝ) +
            (distKI middle source : ℝ)) :=
        mul_le_mul_of_nonneg_left htri' hLeft.2.1
      _ = rate * (distLK target middle : ℝ) +
          rate * (distKI middle source : ℝ) := by ring
  calc
    ∑ target : ν,
          Real.exp (rate * (distLI target source : ℝ)) *
            ‖(Left.comp Right) probe target‖
        ≤ ∑ target : ν,
            Real.exp (rate * (distLI target source : ℝ)) *
              ∑ middle : κ,
                ‖Left (singleFinitePiLp middle
                  (Right probe middle)) target‖ := by
          apply Finset.sum_le_sum
          intro target _
          rw [happ target]
          exact mul_le_mul_of_nonneg_left
            (norm_sum_le _ _) (Real.exp_pos _).le
    _ ≤ ∑ target : ν, ∑ middle : κ,
          (Real.exp (rate * (distLK target middle : ℝ)) *
            ‖Left (singleFinitePiLp middle
              (Right probe middle)) target‖) *
            Real.exp (rate * (distKI middle source : ℝ)) := by
        apply Finset.sum_le_sum
        intro target _
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro middle _
        calc
          Real.exp (rate * (distLI target source : ℝ)) *
              ‖Left (singleFinitePiLp middle
                (Right probe middle)) target‖
            ≤ (Real.exp (rate * (distLK target middle : ℝ)) *
                Real.exp (rate * (distKI middle source : ℝ))) *
                ‖Left (singleFinitePiLp middle
                  (Right probe middle)) target‖ :=
              mul_le_mul_of_nonneg_right (hweight target middle)
                (norm_nonneg _)
          _ = (Real.exp (rate * (distLK target middle : ℝ)) *
                ‖Left (singleFinitePiLp middle
                  (Right probe middle)) target‖) *
                Real.exp (rate * (distKI middle source : ℝ)) := by ring
    _ = ∑ middle : κ,
          (∑ target : ν,
            Real.exp (rate * (distLK target middle : ℝ)) *
              ‖Left (singleFinitePiLp middle
                (Right probe middle)) target‖) *
            Real.exp (rate * (distKI middle source : ℝ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro middle _
        rw [Finset.sum_mul]
    _ ≤ ∑ middle : κ,
          (A * ‖Right probe middle‖) *
            Real.exp (rate * (distKI middle source : ℝ)) := by
        apply Finset.sum_le_sum
        intro middle _
        exact mul_le_mul_of_nonneg_right
          (hLeft.2.2 middle (Right probe middle)) (Real.exp_pos _).le
    _ = A * ∑ middle : κ,
          Real.exp (rate * (distKI middle source : ℝ)) *
            ‖Right probe middle‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro middle _
        ring
    _ ≤ A * (B * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hRight.2.2 source v) hLeft.1
    _ = (A * B) * ‖v‖ := by ring

/-- A rectangular weighted-row estimate contains every target term and hence
recovers the pointwise exponential kernel estimate at the same rate. -/
theorem finitePiLpTypedExponentialKernelBound_of_weightedRow
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) {A rate : ℝ}
    (hrate : 0 < rate)
    (hT : FinitePiLpTypedWeightedRowKernelBound T dist A rate) :
    FinitePiLpTypedExponentialKernelBound T dist A rate := by
  classical
  refine ⟨hT.1, hrate, ?_⟩
  intro source target v
  have hterm :
      Real.exp (rate * (dist target source : ℝ)) *
          ‖T (singleFinitePiLp source v) target‖ ≤
        ∑ next : κ,
          Real.exp (rate * (dist next source : ℝ)) *
            ‖T (singleFinitePiLp source v) next‖ := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset κ))
      (f := fun next : κ =>
        Real.exp (rate * (dist next source : ℝ)) *
          ‖T (singleFinitePiLp source v) next‖)
      (fun next _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (Finset.mem_univ target)
  have hmul :
      Real.exp (rate * (dist target source : ℝ)) *
          ‖T (singleFinitePiLp source v) target‖ ≤ A * ‖v‖ :=
    hterm.trans (hT.2.2 source v)
  have hpos := Real.exp_pos (rate * (dist target source : ℝ))
  calc
    ‖T (singleFinitePiLp source v) target‖
        ≤ (A * ‖v‖) /
            Real.exp (rate * (dist target source : ℝ)) :=
      (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hmul)
    _ = A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring

end

end YangMills.RG

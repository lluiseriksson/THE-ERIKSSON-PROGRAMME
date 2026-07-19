/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalSectionCCutFactor
import YangMills.RG.FinitePiLpTypedWeightedRowKernel

/-!
# Fixed-rate row control for the cut CMP99 Section C factor

This file turns the pointwise bound for the literal cut factor (3.97) into a
source-fixed weighted-row estimate.  The target carrier is the smaller source
region and the source carrier is the preceding larger region.  Injecting the
small target representatives into the large fine region gives a row-sum
constant independent of volume and of the cardinalities of either carrier.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- Source-fixed exponential sum over the smaller target carrier. -/
theorem cmp99OmegaCoarseTransitionDist_target_exp_sum_le
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (source : CMP99OmegaTransitionLargeCoarseSite (M := M) Seq r)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∑ target : CMP99OmegaTransitionSmallCoarseSite (M := M) Seq r,
      Real.exp (-(sigma *
        (cmp99OmegaCoarseTransitionDist (M := M) Seq r target source : ℝ))) ≤
      cmp99OmegaSiteExpSumBound sigma := by
  classical
  let largeIndex := cmp99OmegaTransitionIndex r
  let smallIndex := cmp99OmegaTransitionNextIndex r
  let embed := cmp99OmegaCoarseTransitionRepresentativeLarge (M := M) Seq r
  let center := cmp99OmegaCoarseRepresentativeSite (M := M) Seq largeIndex source
  let f : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq largeIndex) → ℝ := fun target =>
    Real.exp (-(sigma *
      (cmp99OmegaSiteDist Seq largeIndex center target : ℝ)))
  have hinj : Function.Injective embed := by
    intro x y hxy
    apply cmp99OmegaCoarseRepresentativeSite_injective
      (M := M) Seq smallIndex
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    simpa [embed, cmp99OmegaCoarseTransitionRepresentativeLarge,
      cmp99OmegaCoarseRepresentativeSite] using hval
  calc
    ∑ target : CMP99OmegaTransitionSmallCoarseSite (M := M) Seq r,
        Real.exp (-(sigma *
          (cmp99OmegaCoarseTransitionDist (M := M) Seq r target source : ℝ))) =
      ∑ target, f (embed target) := by
        apply Finset.sum_congr rfl
        intro target _
        simp only [f, embed, center, cmp99OmegaSiteDist,
          cmp99OmegaCoarseTransitionDist,
          cmp99OmegaCoarseTransitionRepresentativeLarge,
          cmp99OmegaCoarseRepresentativeSite]
        rw [finBoxDist_comm]
    _ = ∑ target ∈ Finset.univ.image embed, f target := by
      rw [Finset.sum_image hinj.injOn]
    _ ≤ ∑ target, f target := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
        (fun _ _ _ => (Real.exp_pos _).le)
    _ ≤ cmp99OmegaSiteExpSumBound sigma :=
      cmp99OmegaSiteDist_exp_sum_le Seq largeIndex center hsigma

/-- Half of the pointwise decay rate is retained as the fixed weighted-row
rate; the other half pays the uniform target sum. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate
    (M : ℕ) (spacing a : ℝ) : ℝ :=
  cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayRate M spacing a / 2

/-- Explicit, volume-independent weighted-row amplitude of the cut factor. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowAmplitude
    (M : ℕ) (spacing a : ℝ) : ℝ :=
  cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayAmplitude M spacing a *
    cmp99OmegaSiteExpSumBound
      (cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate M spacing a)

/-- The fixed weighted-row rate is strictly positive under the physical
positivity assumptions. -/
theorem cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate_pos
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    0 < cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate M spacing a := by
  have hmu :=
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceDecayRate_pos
      (M := M) hspacing ha
  have htheta :=
    cmp99OmegaSourcePhysicalOneStepCombesThomasRate_pos
      (M := M) hspacing ha
  unfold cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate
    cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayRate
  positivity

set_option maxHeartbeats 2400000 in
/-- The literal cut factor (3.97) has a fixed-rate rectangular weighted-row
bound with no ambient-volume factor. -/
theorem cmp99OmegaSourcePhysicalOneStepSectionCCutFactor_weightedRowKernelBound
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (Cuts : CMP99SourceSectionCTransitionCutData (M := M) Seq r)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    let F := cmp99OmegaSourcePhysicalOneStepSectionCCutFactor
      Seq r Cuts rho U hspacing ha
    FinitePiLpTypedWeightedRowKernelBound
      F
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      (cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowAmplitude M spacing a)
      (cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate M spacing a) := by
  dsimp only
  let rate :=
    cmp99OmegaSourcePhysicalOneStepCoarseRightFactorDecayRate M spacing a
  let weight :=
    cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate M spacing a
  have hweight : 0 < weight :=
    cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate_pos
      (M := M) hspacing ha
  have hrate : rate = 2 * weight := by
    simp [rate, weight,
      cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowRate]
    ring_nf
  have hsum : ∀ source,
      ∑ target : CMP99OmegaTransitionSmallCoarseSite (M := M) Seq r,
        Real.exp (-((rate - weight) *
          (cmp99OmegaCoarseTransitionDist (M := M) Seq r target source : ℝ))) ≤
        cmp99OmegaSiteExpSumBound weight := by
    intro source
    rw [hrate]
    convert cmp99OmegaCoarseTransitionDist_target_exp_sum_le
      (M := M) Seq r source hweight using 1 <;> ring
  simpa [cmp99OmegaSourcePhysicalOneStepSectionCWeightedRowAmplitude,
    rate, weight] using
    finitePiLpTypedWeightedRowKernelBound_of_exponential
      (cmp99OmegaSourcePhysicalOneStepSectionCCutFactor
        Seq r Cuts rho U hspacing ha)
      (cmp99OmegaCoarseTransitionDist (M := M) Seq r)
      hweight.le
      (by
        dsimp [cmp99OmegaSiteExpSumBound]
        exact tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _)
          (Real.exp_pos _).le)
      (cmp99OmegaSourcePhysicalOneStepSectionCCutFactor_exponentialKernelBound
        Seq r Cuts rho U hspacing ha)
      hsum

end

end YangMills.RG

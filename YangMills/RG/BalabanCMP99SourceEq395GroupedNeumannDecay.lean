/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GroupedCorrectionDecay
import YangMills.RG.DependentFinitePiLpWeightedRowWalk

/-!
# Fixed-rate Neumann decay from the grouped CMP99 correction

The grouped pointwise correction estimate is converted once to a weighted
row at half its rate.  Every noncommutative power then preserves that rate,
and the actual operator-valued Neumann sum has a closed geometric amplitude.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- Fixed rate retained by every grouped Neumann layer. -/
noncomputable def cmp99Eq395PhysicalGroupedNeumannDecayRate
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99Eq395PhysicalGroupedRAtomDecayRate M depth spacing epsilon / 2

/-- Weighted-row ratio of the grouped physical correction. -/
noncomputable def cmp99Eq395PhysicalGroupedNeumannRatio
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99Eq395PhysicalGroupedRAtomDecayAmplitude M depth spacing epsilon *
    cmp99OmegaSiteExpSumBound
      (cmp99Eq395PhysicalGroupedNeumannDecayRate M depth spacing epsilon)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2500000 in
/-- The grouped correction has a fixed-rate weighted row obtained directly
from its physical exponential kernel bound. -/
theorem cmp99Eq395PhysicalCorrection_grouped_weightedRow
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedWeightedRowKernelBound
      (cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
        budget fineSmall hsmall : CMP99Eq395AmbientOperator Q Nc)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395PhysicalGroupedNeumannRatio M depth spacing epsilon)
      (cmp99Eq395PhysicalGroupedNeumannDecayRate M depth spacing epsilon) := by
  let r0 := cmp99Eq395PhysicalGroupedRAtomDecayRate M depth spacing epsilon
  let rate := cmp99Eq395PhysicalGroupedNeumannDecayRate M depth spacing epsilon
  let S := cmp99OmegaSiteExpSumBound rate
  have hkernel := cmp99Eq395PhysicalCorrection_grouped_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall
  have hr0 : 0 < r0 := hkernel.2.1
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395PhysicalGroupedNeumannDecayRate]
    linarith
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hsum : ∀ source : FinBox 4 (2 * Q),
      ∑ target : FinBox 4 (2 * Q),
        Real.exp (-((r0 - rate) * (finBoxDist target source : ℝ))) ≤ S := by
    intro source
    have hEq : r0 - rate = rate := by
      dsimp [r0, rate, cmp99Eq395PhysicalGroupedNeumannDecayRate]
      ring
    rw [hEq]
    exact finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound source hrate
  simpa [r0, rate, S, cmp99Eq395PhysicalGroupedNeumannRatio] using
    (finitePiLpTypedWeightedRowKernelBound_of_exponential
      (cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
        budget fineSmall hsmall : CMP99Eq395AmbientOperator Q Nc)
      finBoxDist hrate.le hS hkernel hsum)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The same grouped ratio also bounds the operator norm, so one scalar
smallness condition controls both Banach inversion and fixed-rate decay. -/
theorem norm_cmp99Eq395PhysicalCorrection_le_groupedNeumannRatio
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
      budget fineSmall hsmall‖ ≤
      cmp99Eq395PhysicalGroupedNeumannRatio M depth spacing epsilon := by
  let R := cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing
    background budget fineSmall hsmall
  let rate := cmp99Eq395PhysicalGroupedNeumannDecayRate M depth spacing epsilon
  let S := cmp99OmegaSiteExpSumBound rate
  have hkernel0 := cmp99Eq395PhysicalCorrection_grouped_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395PhysicalGroupedNeumannDecayRate]
    linarith [hkernel0.2.1]
  have hkernel := finitePiLpTypedExponentialKernelBound_mono_rate
    hrate (by
      dsimp [rate, cmp99Eq395PhysicalGroupedNeumannDecayRate]
      linarith [hkernel0.2.1]) hkernel0
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hsum : ∀ source : FinBox 4 (2 * Q),
      ∑ target : FinBox 4 (2 * Q),
        Real.exp (-(rate * (finBoxDist source target : ℝ))) ≤ S := by
    intro source
    simpa [finBoxDist_comm] using
      (finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound source hrate)
  simpa [R, rate, S, cmp99Eq395PhysicalGroupedNeumannRatio] using
    (finitePiLpOpNorm_le_of_exponentialKernelBound R finBoxDist
      (fun x y ↦ finBoxDist_comm x y) hS hkernel hsum)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 3500000 in
/-- Every power of the physical correction retains the same grouped
Neumann rate and has the exact geometric ratio to that power. -/
theorem cmp99Eq395PhysicalCorrection_pow_grouped_weightedRow
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) (n : ℕ) :
    FinitePiLpTypedWeightedRowKernelBound
      ((cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
        budget fineSmall hsmall : CMP99Eq395AmbientOperator Q Nc) ^ n)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      ((cmp99Eq395PhysicalGroupedNeumannRatio M depth spacing epsilon) ^ n)
      (cmp99Eq395PhysicalGroupedNeumannDecayRate M depth spacing epsilon) := by
  let R := cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing
    background budget fineSmall hsmall
  let A := cmp99Eq395PhysicalGroupedNeumannRatio M depth spacing epsilon
  let rate := cmp99Eq395PhysicalGroupedNeumannDecayRate M depth spacing epsilon
  have hR := cmp99Eq395PhysicalCorrection_grouped_weightedRow
    D hpi5 P hM depth hspacing background budget fineSmall hsmall
  induction n with
  | zero =>
      simpa [R, A, rate] using
        (finitePiLpTypedWeightedRowKernelBound_id
          (g := SUNLieCoord Nc) finBoxDist hR.2.1
          (fun x ↦ finBoxDist_self x))
  | succ n ih =>
      simpa [R, A, rate, pow_succ] using
        (finitePiLpTypedWeightedRowKernelBound_comp finBoxDist finBoxDist
          finBoxDist
          (fun target middle source ↦ finBoxDist_triangle target middle source)
          ih hR)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The actual operator-valued grouped Neumann sum preserves the fixed rate
and has closed geometric amplitude `(1-ratio)⁻¹`. -/
theorem cmp99Eq395PhysicalCorrection_tsum_pow_grouped_exponentialKernelBound
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (hcontract : cmp99Eq395PhysicalGroupedNeumannRatio
      M depth spacing epsilon < 1) :
    FinitePiLpExponentialKernelBound
      (∑' n : ℕ,
        (cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
          budget fineSmall hsmall : CMP99Eq395AmbientOperator Q Nc) ^ n)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      ((1 - cmp99Eq395PhysicalGroupedNeumannRatio
        M depth spacing epsilon)⁻¹)
      (cmp99Eq395PhysicalGroupedNeumannDecayRate M depth spacing epsilon) := by
  let R := cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing
    background budget fineSmall hsmall
  let A := cmp99Eq395PhysicalGroupedNeumannRatio M depth spacing epsilon
  let rate := cmp99Eq395PhysicalGroupedNeumannDecayRate M depth spacing epsilon
  have hrow := cmp99Eq395PhysicalCorrection_grouped_weightedRow
    D hpi5 P hM depth hspacing background budget fineSmall hsmall
  have hA0 : 0 ≤ A := hrow.1
  have hkernel0 := cmp99Eq395PhysicalCorrection_grouped_exponentialKernelBound
    D hpi5 P hM depth hspacing background budget fineSmall hsmall
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395PhysicalGroupedNeumannDecayRate]
    linarith [hkernel0.2.1]
  have hRnorm : ‖(R : CMP99Eq395AmbientOperator Q Nc)‖ < 1 :=
    (norm_cmp99Eq395PhysicalCorrection_le_groupedNeumannRatio
      D hpi5 P hM depth hspacing background budget fineSmall hsmall).trans_lt
        hcontract
  have hRsum : Summable fun n : ℕ =>
      (R : CMP99Eq395AmbientOperator Q Nc) ^ n :=
    summable_geometric_of_norm_lt_one hRnorm
  refine ⟨inv_nonneg.mpr (sub_nonneg.mpr hcontract.le), hrate, ?_⟩
  intro source target v
  let delta := singleFinitePiLp source v
  let E := GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc)
  let siteEval : E →L[ℝ] SUNLieCoord Nc :=
    (ContinuousLinearMap.proj target).comp
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : FinBox 4 (2 * Q) => SUNLieCoord Nc)).toContinuousLinearMap
  let evalCLM : (E →L[ℝ] E) →L[ℝ] SUNLieCoord Nc :=
    siteEval.comp (ContinuousLinearMap.apply ℝ E delta)
  have heval (T : E →L[ℝ] E) : evalCLM T = T delta target := by rfl
  have hmap := evalCLM.map_tsum hRsum
  have hrewrite :
      ((∑' n : ℕ, (R : CMP99Eq395AmbientOperator Q Nc) ^ n) delta) target =
        ∑' n : ℕ, ((R : CMP99Eq395AmbientOperator Q Nc) ^ n) delta target := by
    simpa only [heval] using hmap
  rw [hrewrite]
  have hpoint : ∀ n : ℕ,
      ‖((R : CMP99Eq395AmbientOperator Q Nc) ^ n) delta target‖ ≤
        A ^ n *
          (Real.exp (-(rate * (finBoxDist target source : ℝ))) * ‖v‖) := by
    intro n
    have hp := cmp99Eq395PhysicalCorrection_pow_grouped_weightedRow
      D hpi5 P hM depth hspacing background budget fineSmall hsmall n
    have hk := finitePiLpTypedExponentialKernelBound_of_weightedRow
      ((R : CMP99Eq395AmbientOperator Q Nc) ^ n) finBoxDist hrate hp
    simpa [R, A, rate, delta, mul_assoc] using hk.2.2 source target v
  have hsum : Summable fun n : ℕ =>
      ((R : CMP99Eq395AmbientOperator Q Nc) ^ n) delta target := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hA0 hcontract).mul_right
        (Real.exp (-(rate * (finBoxDist target source : ℝ))) * ‖v‖))
    exact hpoint
  calc
    ‖∑' n : ℕ, ((R : CMP99Eq395AmbientOperator Q Nc) ^ n) delta target‖
        ≤ ∑' n : ℕ,
          ‖((R : CMP99Eq395AmbientOperator Q Nc) ^ n) delta target‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, A ^ n *
          (Real.exp (-(rate * (finBoxDist target source : ℝ))) * ‖v‖) :=
      hsum.norm.tsum_le_tsum hpoint
        ((summable_geometric_of_lt_one hA0 hcontract).mul_right _)
    _ = (1 - A)⁻¹ *
          Real.exp (-(rate * (finBoxDist target source : ℝ))) * ‖v‖ := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one hA0 hcontract]
      ring
    _ = (1 - cmp99Eq395PhysicalGroupedNeumannRatio
          M depth spacing epsilon)⁻¹ *
        Real.exp (-(cmp99Eq395PhysicalGroupedNeumannDecayRate
          M depth spacing epsilon * (finBoxDist target source : ℝ))) * ‖v‖ := by
      rfl

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG

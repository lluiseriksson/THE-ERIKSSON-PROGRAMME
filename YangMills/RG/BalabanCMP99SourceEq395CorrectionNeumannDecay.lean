/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395CorrectionPowers

/-!
# Fixed-rate Neumann-kernel decay for CMP99 equation (3.95)

Under the explicit volume-independent smallness of the complete correction's
weighted-row amplitude, every point-source/target Neumann series is summable.
Its sum retains the same spatial rate and has the closed geometric amplitude
`(1 - A)⁻¹`.

This is deliberately a kernel statement.  It does not replace the separate
operator-norm contraction used by the Banach-algebra inverse theorem.
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

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- At fixed source and target, the literal Neumann layers of the physical
correction form an absolutely summable Lie-coordinate series. -/
theorem summable_cmp99Eq395PhysicalCorrection_pow_apply_single
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
    (hcontract : cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
      M depth spacing epsilon < 1)
    (source target : FinBox 4 (2 * Q)) (v : SUNLieCoord Nc) :
    Summable (fun n : ℕ =>
      ((cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
        budget fineSmall hsmall : CMP99Eq395AmbientOperator Q Nc) ^ n)
        (singleFinitePiLp source v) target) := by
  let R := cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
    budget fineSmall hsmall
  let A := cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
    M depth spacing epsilon
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  let E := Real.exp (-(rate * (finBoxDist target source : ℝ)))
  have hR := cmp99Eq395PhysicalCorrection_sharp_weightedRow D hpi5 P hM depth
    hspacing background budget fineSmall hsmall
  have hA0 : 0 ≤ A := hR.1
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395FirstAtomDecayRate]
    have := cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
    positivity
  have hmajor : Summable (fun n : ℕ => A ^ n * (E * ‖v‖)) :=
    (summable_geometric_of_lt_one hA0 hcontract).mul_right _
  apply Summable.of_norm_bounded hmajor
  intro n
  have hpow := cmp99Eq395PhysicalCorrection_pow_weightedRow D hpi5 P hM
    depth hspacing background budget fineSmall hsmall n
  have hpoint := finitePiLpTypedExponentialKernelBound_of_weightedRow
    (R ^ n : CMP99Eq395AmbientOperator Q Nc) finBoxDist hrate hpow
  simpa [R, A, rate, E, mul_assoc] using hpoint.2.2 source target v

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- The pointwise Neumann kernel has the closed volume-independent bound
`(1-A)⁻¹ exp(-rate distance)`. -/
theorem norm_tsum_cmp99Eq395PhysicalCorrection_pow_apply_single_le
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
    (hcontract : cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
      M depth spacing epsilon < 1)
    (source target : FinBox 4 (2 * Q)) (v : SUNLieCoord Nc) :
    ‖∑' n : ℕ,
      ((cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
        budget fineSmall hsmall : CMP99Eq395AmbientOperator Q Nc) ^ n)
        (singleFinitePiLp source v) target‖ ≤
      (1 - cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
        M depth spacing epsilon)⁻¹ *
        Real.exp (-(cmp99Eq395FirstAtomDecayRate M depth spacing epsilon *
          (finBoxDist target source : ℝ))) * ‖v‖ := by
  let R := cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
    budget fineSmall hsmall
  let A := cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
    M depth spacing epsilon
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  let E := Real.exp (-(rate * (finBoxDist target source : ℝ)))
  have hR := cmp99Eq395PhysicalCorrection_sharp_weightedRow D hpi5 P hM depth
    hspacing background budget fineSmall hsmall
  have hA0 : 0 ≤ A := hR.1
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395FirstAtomDecayRate]
    have := cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
    positivity
  have hsum : Summable (fun n : ℕ =>
      (R ^ n : CMP99Eq395AmbientOperator Q Nc)
        (singleFinitePiLp source v) target) := by
    exact summable_cmp99Eq395PhysicalCorrection_pow_apply_single D hpi5 P hM
      depth hspacing background budget fineSmall hsmall hcontract source target v
  have hmajor : Summable (fun n : ℕ => A ^ n * (E * ‖v‖)) :=
    (summable_geometric_of_lt_one hA0 hcontract).mul_right _
  have hpoint : ∀ n : ℕ,
      ‖(R ^ n : CMP99Eq395AmbientOperator Q Nc)
          (singleFinitePiLp source v) target‖ ≤ A ^ n * (E * ‖v‖) := by
    intro n
    have hpow := cmp99Eq395PhysicalCorrection_pow_weightedRow D hpi5 P hM
      depth hspacing background budget fineSmall hsmall n
    have hexp := finitePiLpTypedExponentialKernelBound_of_weightedRow
      (R ^ n : CMP99Eq395AmbientOperator Q Nc) finBoxDist hrate hpow
    simpa [R, A, rate, E, mul_assoc] using hexp.2.2 source target v
  calc
    ‖∑' n : ℕ, (R ^ n : CMP99Eq395AmbientOperator Q Nc)
          (singleFinitePiLp source v) target‖
        ≤ ∑' n : ℕ, ‖(R ^ n : CMP99Eq395AmbientOperator Q Nc)
          (singleFinitePiLp source v) target‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, A ^ n * (E * ‖v‖) :=
      hsum.norm.tsum_le_tsum hpoint hmajor
    _ = (1 - A)⁻¹ * E * ‖v‖ := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one hA0 hcontract]
      ring
    _ = (1 - cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
          M depth spacing epsilon)⁻¹ *
        Real.exp (-(cmp99Eq395FirstAtomDecayRate M depth spacing epsilon *
          (finBoxDist target source : ℝ))) * ‖v‖ := by
      rfl

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG

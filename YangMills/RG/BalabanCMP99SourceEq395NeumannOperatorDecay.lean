/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395CorrectionOperatorNorm

/-!
# Operator realization of the fixed-rate CMP99 Neumann kernel

The explicit Schur smallness simultaneously supplies Banach-algebra
summability of the operator powers and pointwise fixed-rate summability.  The
two sums are identified by continuous evaluation, yielding an exponential
kernel estimate for the actual operator-valued Neumann sum in (3.95).
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
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The actual operator-valued Neumann sum of the physical correction has
the same fixed spatial rate as every homogeneous layer. -/
theorem cmp99Eq395PhysicalCorrection_tsum_pow_exponentialKernelBound_of_schurSmall
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
    (hschur : cmp99Eq395PhysicalCorrectionSchurAmplitude
      M depth spacing epsilon < 1) :
    FinitePiLpExponentialKernelBound
      (∑' n : ℕ,
        (cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
          budget fineSmall hsmall : CMP99Eq395AmbientOperator Q Nc) ^ n)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      ((1 - cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
        M depth spacing epsilon)⁻¹)
      (cmp99Eq395FirstAtomDecayRate M depth spacing epsilon) := by
  let R := cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
    budget fineSmall hsmall
  let A := cmp99Eq395PhysicalCorrectionSharpWeightedRowAmplitude
    M depth spacing epsilon
  let rate := cmp99Eq395FirstAtomDecayRate M depth spacing epsilon
  have hA : A < 1 := by
    exact cmp99Eq395PhysicalCorrectionWeightedRowAmplitude_lt_one_of_schurSmall
      depth hspacing hsmall hschur
  have hrate : 0 < rate := by
    dsimp [rate, cmp99Eq395FirstAtomDecayRate]
    have := cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
    positivity
  have hRnorm : ‖(R : CMP99Eq395AmbientOperator Q Nc)‖ < 1 :=
    (norm_cmp99Eq395PhysicalCorrection_le_schurAmplitude D hpi5 P hM
      depth hspacing background budget fineSmall hsmall).trans_lt hschur
  have hRsum : Summable fun n : ℕ =>
      (R : CMP99Eq395AmbientOperator Q Nc) ^ n :=
    summable_geometric_of_norm_lt_one hRnorm
  refine ⟨inv_nonneg.mpr (sub_nonneg.mpr hA.le), hrate, ?_⟩
  intro source target v
  let delta := singleFinitePiLp source v
  let E := GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc)
  let siteEval : E →L[ℝ] SUNLieCoord Nc :=
    (ContinuousLinearMap.proj target).comp
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : FinBox 4 (2 * Q) => SUNLieCoord Nc)).toContinuousLinearMap
  let evalCLM : (E →L[ℝ] E) →L[ℝ] SUNLieCoord Nc :=
    siteEval.comp (ContinuousLinearMap.apply ℝ E delta)
  have heval (T : E →L[ℝ] E) : evalCLM T = T delta target := by
    rfl
  have hmap := evalCLM.map_tsum hRsum
  have hrewrite :
      ((∑' n : ℕ, (R : CMP99Eq395AmbientOperator Q Nc) ^ n) delta) target =
        ∑' n : ℕ, ((R : CMP99Eq395AmbientOperator Q Nc) ^ n) delta target := by
    simpa only [heval] using hmap
  rw [hrewrite]
  simpa [R, A, rate, delta] using
    (norm_tsum_cmp99Eq395PhysicalCorrection_pow_apply_single_le D hpi5 P hM
      depth hspacing background budget fineSmall hsmall hA source target v)

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG

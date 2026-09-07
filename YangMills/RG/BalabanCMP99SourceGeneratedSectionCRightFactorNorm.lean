/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCRightFactor
import YangMills.RG.BalabanCMP99SourceGeneratedCoarseCovarianceTransitionNorm

/-!
# Norm of the generated CMP99 Section C right factor

The complete covariance transition cannot be multiplied at every source
scale.  This file instead bounds the literal one-sided right factor from its
coarse-middle defect and the larger covariance.  The only scale cost is the
counting-norm size of the source-weighted synthesis; no ambient-volume
cardinality occurs.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- Counting-norm cost of the complete source-weighted synthesis in four
dimensions. -/
noncomputable def cmp99SourceGeneratedWeightedAdjointNormBound
    (M depth : ℕ) : ℝ :=
  (M : ℝ) ^ (2 * (depth + 1))

/-- Explicit volume-independent norm budget for the one-sided right factor. -/
noncomputable def cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  let W := cmp99SourceGeneratedWeightedAdjointNormBound M depth
  let L := (((cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon) ^ 2)⁻¹)⁻¹
  2 * (1 / c) ^ 2 * W * L

/-- Explicit norm budget for the rectangular coarse-middle defect before the
larger covariance is attached. -/
noncomputable def cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  2 * (1 / c) ^ 2 *
    cmp99SourceGeneratedWeightedAdjointNormBound M depth

/-- Explicit norm budget for one generated coarse covariance. -/
noncomputable def cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  (((cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon) ^ 2)⁻¹)⁻¹

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

/-- The generated source-weighted synthesis has its exact four-dimensional
counting-norm scale cost. -/
theorem norm_generatedWeightedAdjoint_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      (D.operatorCoarseRegion hpi5 s) (depth + 1)
    let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    ‖T.weightedAdjoint‖ ≤
      cmp99SourceGeneratedWeightedAdjointNormBound M depth := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    (D.operatorCoarseRegion hpi5 s) (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    unfold cmp99SourceGeneratedWeightedAdjointNormBound
    positivity)
  intro eta
  have hterminal : T.terminalSpacing =
      (M : ℝ) ^ (depth + 1) * spacing :=
    regions.weightedQprimeTower_terminalSpacing (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
  have hsq := T.weightedAdjoint_spacingNormSq eta
  rw [hterminal] at hsq
  have hspacing4 : 0 < spacing ^ 4 := pow_pos hspacing _
  have heq : ‖T.weightedAdjoint eta‖ ^ 2 =
      ((M : ℝ) ^ (2 * (depth + 1)) * ‖eta‖) ^ 2 := by
    have hpow : ((M : ℝ) ^ (depth + 1) * spacing) ^ 4 =
        spacing ^ 4 * ((M : ℝ) ^ (2 * (depth + 1))) ^ 2 := by ring
    rw [hpow] at hsq
    nlinarith
  apply le_of_sq_le_sq
  · exact heq.le
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg M) _)
      (norm_nonneg eta)

/-- Every generated coarse middle operator has an explicit norm bound. -/
theorem norm_generatedPhysicalCoarseCovarianceMiddle_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
        (show 2 ≤ 4 by norm_num) hM (D.operatorCoarseRegion hpi5 s) depth
        hspacing background budget fineSmall hsmall‖ ≤
      (1 / cmp99SourceGeneratedCoercivity 4 M (depth + 1)
          spacing epsilon) ^ 2 *
        cmp99SourceGeneratedWeightedAdjointNormBound M depth := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    (D.operatorCoarseRegion hpi5 s) (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 s) depth hspacing background budget
    fineSmall hsmall
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  have hc : 0 < c := cmp99SourceGeneratedCoercivity_pos 4 M depth hspacing hsmall
  have hQ : ‖T.Qprime‖ ≤ 1 :=
    regions.norm_weightedQprimeTower_Qprime_le_one
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) hspacing
      background budget.toRadiusChain fineSmall
  have hW : ‖T.weightedAdjoint‖ ≤
      cmp99SourceGeneratedWeightedAdjointNormBound M depth :=
    D.norm_generatedWeightedAdjoint_le hpi5 s hM depth hspacing background
      budget fineSmall
  have hG : ‖G‖ ≤ 1 / c := by
    simpa [G, c] using norm_covarianceOfIsCoerciveCLM_le
      (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
        (D.operatorCoarseRegion hpi5 s) depth spacing epsilon background
        budget fineSmall)
      hc
      (isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision
        (show 2 ≤ 4 by norm_num) hM (D.operatorCoarseRegion hpi5 s) depth
        hspacing background budget fineSmall hsmall)
  rw [D.generatedPhysicalCoarseCovarianceMiddle_eq_Qprime_green_sq hpi5 s
    hM depth hspacing background budget fineSmall hsmall]
  have hGW : ‖G.comp T.weightedAdjoint‖ ≤
      (1 / c) * cmp99SourceGeneratedWeightedAdjointNormBound M depth :=
    (ContinuousLinearMap.opNorm_comp_le G T.weightedAdjoint).trans
      (mul_le_mul hG hW (norm_nonneg T.weightedAdjoint)
        (by positivity))
  have hGGW : ‖G.comp (G.comp T.weightedAdjoint)‖ ≤
      (1 / c) * ((1 / c) *
        cmp99SourceGeneratedWeightedAdjointNormBound M depth) :=
    (ContinuousLinearMap.opNorm_comp_le G (G.comp T.weightedAdjoint)).trans
      (mul_le_mul hG hGW (norm_nonneg (G.comp T.weightedAdjoint))
        (by positivity))
  calc
    ‖T.Qprime.comp (G.comp (G.comp T.weightedAdjoint))‖ ≤
        ‖T.Qprime‖ * ‖G.comp (G.comp T.weightedAdjoint)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ((1 / c) * ((1 / c) *
        cmp99SourceGeneratedWeightedAdjointNormBound M depth)) := by
      exact mul_le_mul hQ hGGW (norm_nonneg _) zero_le_one
    _ = (1 / c) ^ 2 *
        cmp99SourceGeneratedWeightedAdjointNormBound M depth := by ring

/-- Uniform norm of the literal generated one-sided Section C right factor. -/
theorem norm_generatedPhysicalCoarseRightFactor_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedPhysicalCoarseRightFactor hpi5 r hM depth hspacing
      background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
        M depth spacing epsilon := by
  let Mlarge := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
    hspacing background budget fineSmall hsmall
  let Msmall := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
    hspacing background budget fineSmall hsmall
  let R := D.generatedTerminalRestriction hpi5 r hM depth spacing epsilon
    background budget fineSmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
    hspacing background budget fineSmall hsmall
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  let W := cmp99SourceGeneratedWeightedAdjointNormBound M depth
  let L := (((cmp99SourceGeneratedPhysicalPrecisionUpperBound
    4 M (depth + 1) spacing epsilon) ^ 2)⁻¹)⁻¹
  have hc : 0 < c := cmp99SourceGeneratedCoercivity_pos 4 M depth hspacing hsmall
  have hMlarge : ‖Mlarge‖ ≤ (1 / c) ^ 2 * W :=
    D.norm_generatedPhysicalCoarseCovarianceMiddle_le hpi5
      (cmp99OmegaTransitionIndex r) hM depth hspacing background budget
      fineSmall hsmall
  have hMsmall : ‖Msmall‖ ≤ (1 / c) ^ 2 * W :=
    D.norm_generatedPhysicalCoarseCovarianceMiddle_le hpi5
      (cmp99OmegaTransitionNextIndex r) hM depth hspacing background budget
      fineSmall hsmall
  have hR : ‖R‖ ≤ 1 :=
    D.norm_generatedTerminalRestriction_le_one hpi5 r hM depth spacing
      epsilon background budget fineSmall
  have hC : ‖C‖ ≤ L :=
    norm_cmp99SourceGeneratedPhysicalCoarseCovariance_le
      (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
      hspacing background budget fineSmall hsmall
  have hW0 : 0 ≤ W := by
    dsimp [W, cmp99SourceGeneratedWeightedAdjointNormBound]
    positivity
  have hcore : ‖R.comp Mlarge - Msmall.comp R‖ ≤
      2 * (1 / c) ^ 2 * W := by
    calc
      ‖R.comp Mlarge - Msmall.comp R‖ ≤
          ‖R.comp Mlarge‖ + ‖Msmall.comp R‖ := norm_sub_le _ _
      _ ≤ ‖R‖ * ‖Mlarge‖ + ‖Msmall‖ * ‖R‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ 1 * ((1 / c) ^ 2 * W) + ((1 / c) ^ 2 * W) * 1 := by
        exact add_le_add
          (mul_le_mul hR hMlarge (norm_nonneg Mlarge) zero_le_one)
          (mul_le_mul hMsmall hR (norm_nonneg R)
            (mul_nonneg (sq_nonneg _) hW0))
      _ = 2 * (1 / c) ^ 2 * W := by ring
  unfold generatedPhysicalCoarseRightFactor
    generatedPhysicalCoarseMiddleTransitionDefect
    cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
  change ‖(R.comp Mlarge - Msmall.comp R).comp C‖ ≤
    2 * (1 / c) ^ 2 * W * L
  calc
    ‖(R.comp Mlarge - Msmall.comp R).comp C‖ ≤
        ‖R.comp Mlarge - Msmall.comp R‖ * ‖C‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (2 * (1 / c) ^ 2 * W) * L := by gcongr

/-- Uniform norm of the generated rectangular middle defect itself. -/
theorem norm_generatedPhysicalCoarseMiddleTransitionDefect_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedPhysicalCoarseMiddleTransitionDefect hpi5 r hM depth
      hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound
        M depth spacing epsilon := by
  let Mlarge := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
    hspacing background budget fineSmall hsmall
  let Msmall := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
    hspacing background budget fineSmall hsmall
  let R := D.generatedTerminalRestriction hpi5 r hM depth spacing epsilon
    background budget fineSmall
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  let W := cmp99SourceGeneratedWeightedAdjointNormBound M depth
  have hMlarge : ‖Mlarge‖ ≤ (1 / c) ^ 2 * W :=
    D.norm_generatedPhysicalCoarseCovarianceMiddle_le hpi5
      (cmp99OmegaTransitionIndex r) hM depth hspacing background budget
      fineSmall hsmall
  have hMsmall : ‖Msmall‖ ≤ (1 / c) ^ 2 * W :=
    D.norm_generatedPhysicalCoarseCovarianceMiddle_le hpi5
      (cmp99OmegaTransitionNextIndex r) hM depth hspacing background budget
      fineSmall hsmall
  have hR : ‖R‖ ≤ 1 :=
    D.norm_generatedTerminalRestriction_le_one hpi5 r hM depth spacing
      epsilon background budget fineSmall
  have hW0 : 0 ≤ W := by
    dsimp [W, cmp99SourceGeneratedWeightedAdjointNormBound]
    positivity
  unfold generatedPhysicalCoarseMiddleTransitionDefect cmp99TypedPrecisionDefect
    cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound
  change ‖R.comp Mlarge - Msmall.comp R‖ ≤ 2 * (1 / c) ^ 2 * W
  calc
    ‖R.comp Mlarge - Msmall.comp R‖ ≤
        ‖R.comp Mlarge‖ + ‖Msmall.comp R‖ := norm_sub_le _ _
    _ ≤ ‖R‖ * ‖Mlarge‖ + ‖Msmall‖ * ‖R‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ 1 * ((1 / c) ^ 2 * W) + ((1 / c) ^ 2 * W) * 1 := by
      exact add_le_add
        (mul_le_mul hR hMlarge (norm_nonneg Mlarge) zero_le_one)
        (mul_le_mul hMsmall hR (norm_nonneg R)
          (mul_nonneg (sq_nonneg _) hW0))
    _ = 2 * (1 / c) ^ 2 * W := by ring

/-- Transporting the right factor to literal physical coordinates preserves
its norm budget. -/
theorem norm_generatedPhysicalCoarseRightFactorCoordinates_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedPhysicalCoarseRightFactorCoordinates hpi5 r hM depth
      hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
        M depth spacing epsilon := by
  let F := D.generatedPhysicalCoarseRightFactor hpi5 r hM depth hspacing
    background budget fineSmall hsmall
  let hlarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) (depth + 1)
    spacing epsilon background budget.toRadiusChain fineSmall
  let hsmallSpace :=
    cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  change ‖cmp99SourceTerminalCLMTransport hlarge hsmallSpace F‖ ≤ _
  rw [norm_cmp99SourceTerminalCLMTransport]
  exact D.norm_generatedPhysicalCoarseRightFactor_le hpi5 r hM depth
    hspacing background budget fineSmall hsmall

/-- Transporting the rectangular middle defect to physical coordinates
preserves its norm budget. -/
theorem norm_generatedPhysicalCoarseMiddleTransitionDefectCoordinates_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedPhysicalCoarseMiddleTransitionDefectCoordinates hpi5 r hM
      depth hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound
        M depth spacing epsilon := by
  let F := D.generatedPhysicalCoarseMiddleTransitionDefect hpi5 r hM depth
    hspacing background budget fineSmall hsmall
  let hlarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) (depth + 1)
    spacing epsilon background budget.toRadiusChain fineSmall
  let hsmallSpace :=
    cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  change ‖cmp99SourceTerminalCLMTransport hlarge hsmallSpace F‖ ≤ _
  rw [norm_cmp99SourceTerminalCLMTransport]
  exact D.norm_generatedPhysicalCoarseMiddleTransitionDefect_le hpi5 r hM
    depth hspacing background budget fineSmall hsmall

/-- Transporting one generated coarse covariance to its literal physical
terminal coordinates preserves the inverse-coercivity norm budget. -/
theorem norm_generatedPhysicalCoarseCovarianceCoordinates_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
      hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
        M depth spacing epsilon := by
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM (D.operatorCoarseRegion hpi5 s) depth
    hspacing background budget fineSmall hsmall
  let hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 s) (depth + 1) spacing epsilon background
    budget.toRadiusChain fineSmall
  change ‖cmp99SourceTerminalCLMTransport hs hs C‖ ≤ _
  rw [norm_cmp99SourceTerminalCLMTransport]
  simpa [C, cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound] using
    norm_cmp99SourceGeneratedPhysicalCoarseCovariance_le
      (show 2 ≤ 4 by norm_num) hM (D.operatorCoarseRegion hpi5 s) depth
      hspacing background budget fineSmall hsmall

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG

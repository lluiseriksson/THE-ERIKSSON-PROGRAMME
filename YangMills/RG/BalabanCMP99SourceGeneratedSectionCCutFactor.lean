/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCRightFactorNorm
import YangMills.RG.FinitePiLpTypedCutoff

/-!
# Generated source-specific cut factor in CMP99 Section C

The factor printed in CMP99 (3.97) does not cut the completed covariance
difference.  Its ordering is

`tildeChi * middleDefect * h_Pi * coarseCovariance * h_Pi`.

This file realizes that ordering on the literal terminal coordinate carriers
of the generated regional tower.  Pointwise contractivity of the two source
cutoffs is enough to retain the volume-independent norm of the uncut
one-sided factor.
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

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 3000000

/-- The two contractive cutoffs occurring in the generated physical version
of CMP99 (3.97). -/
structure GeneratedSectionCTransitionCutData
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) where
  exterior : ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) → ℝ
  partition : ActiveGaugeRegion.Site
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) → ℝ
  exterior_norm_le_one : ∀ x, ‖exterior x‖ ≤ 1
  partition_norm_le_one : ∀ x, ‖partition x‖ ≤ 1

/-- Literal generated cut factor in the operator order of CMP99 (3.97). -/
noncomputable def generatedPhysicalCoarseSectionCCutFactorCoordinates
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1))
    (Cuts : D.GeneratedSectionCTransitionCutData hpi5 r)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  let Hsmall := finitePiLpScalarMultiplier
    (g := SUNLieCoord Nc) Cuts.exterior
  let Hlarge := finitePiLpScalarMultiplier
    (g := SUNLieCoord Nc) Cuts.partition
  let Dcoord := D.generatedPhysicalCoarseMiddleTransitionDefectCoordinates
    hpi5 r hM depth hspacing background budget fineSmall hsmall
  let Ccoord := D.generatedPhysicalCoarseCovarianceCoordinates hpi5
    (cmp99OmegaTransitionIndex r) hM depth hspacing background budget
    fineSmall hsmall
  Hsmall.comp (Dcoord.comp (Hlarge.comp (Ccoord.comp Hlarge)))

/-- The literal source cutoffs add no cost to the volume-independent norm of
the generated one-sided factor. -/
theorem norm_generatedPhysicalCoarseSectionCCutFactorCoordinates_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1))
    (Cuts : D.GeneratedSectionCTransitionCutData hpi5 r)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedPhysicalCoarseSectionCCutFactorCoordinates hpi5 r Cuts hM
      depth hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
        M depth spacing epsilon := by
  let Hsmall := finitePiLpScalarMultiplier
    (g := SUNLieCoord Nc) Cuts.exterior
  let Hlarge := finitePiLpScalarMultiplier
    (g := SUNLieCoord Nc) Cuts.partition
  let Dcoord := D.generatedPhysicalCoarseMiddleTransitionDefectCoordinates
    hpi5 r hM depth hspacing background budget fineSmall hsmall
  let Ccoord := D.generatedPhysicalCoarseCovarianceCoordinates hpi5
    (cmp99OmegaTransitionIndex r) hM depth hspacing background budget
    fineSmall hsmall
  let AD := cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound
    M depth spacing epsilon
  let AC := cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
    M depth spacing epsilon
  have hHs : ‖Hsmall‖ ≤ 1 :=
    norm_finitePiLpScalarMultiplier_le_one Cuts.exterior
      Cuts.exterior_norm_le_one
  have hHl : ‖Hlarge‖ ≤ 1 :=
    norm_finitePiLpScalarMultiplier_le_one Cuts.partition
      Cuts.partition_norm_le_one
  have hD : ‖Dcoord‖ ≤ AD :=
    D.norm_generatedPhysicalCoarseMiddleTransitionDefectCoordinates_le
      hpi5 r hM depth hspacing background budget fineSmall hsmall
  have hC : ‖Ccoord‖ ≤ AC :=
    D.norm_generatedPhysicalCoarseCovarianceCoordinates_le hpi5
      (cmp99OmegaTransitionIndex r) hM depth hspacing background budget
      fineSmall hsmall
  have hAD : 0 ≤ AD := by
    dsimp [AD, cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound,
      cmp99SourceGeneratedWeightedAdjointNormBound]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (pow_nonneg (Nat.cast_nonneg M) _)
  have hCH : ‖Ccoord.comp Hlarge‖ ≤ AC := by
    calc
      ‖Ccoord.comp Hlarge‖ ≤ ‖Ccoord‖ * ‖Hlarge‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ AC * 1 :=
        mul_le_mul hC hHl (norm_nonneg Hlarge) (by
          dsimp [AC, cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound]
          positivity)
      _ = AC := mul_one _
  have hHCH : ‖Hlarge.comp (Ccoord.comp Hlarge)‖ ≤ AC := by
    calc
      ‖Hlarge.comp (Ccoord.comp Hlarge)‖ ≤
          ‖Hlarge‖ * ‖Ccoord.comp Hlarge‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * AC :=
        mul_le_mul hHl hCH (norm_nonneg _) zero_le_one
      _ = AC := one_mul _
  have hDHCH : ‖Dcoord.comp (Hlarge.comp (Ccoord.comp Hlarge))‖ ≤ AD * AC := by
    calc
      ‖Dcoord.comp (Hlarge.comp (Ccoord.comp Hlarge))‖ ≤
          ‖Dcoord‖ * ‖Hlarge.comp (Ccoord.comp Hlarge)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ AD * AC :=
        mul_le_mul hD hHCH (norm_nonneg _) hAD
  change ‖Hsmall.comp (Dcoord.comp (Hlarge.comp (Ccoord.comp Hlarge)))‖ ≤ _
  calc
    ‖Hsmall.comp (Dcoord.comp (Hlarge.comp (Ccoord.comp Hlarge)))‖ ≤
        ‖Hsmall‖ * ‖Dcoord.comp (Hlarge.comp (Ccoord.comp Hlarge))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (AD * AC) :=
      mul_le_mul hHs hDHCH (norm_nonneg _) zero_le_one
    _ = cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound
        M depth spacing epsilon := by
      simp only [one_mul]
      dsimp [AD, AC,
        cmp99SourceGeneratedPhysicalCoarseMiddleDefectNormBound,
        cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound,
        cmp99SourceGeneratedPhysicalCoarseRightFactorNormBound]

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCoarseCovarianceTransitionCoordinates

/-!
# Generated CMP99 Section C right factor

The printed regional covariance difference is not itself multiplied at every
scale.  It first factors by the second-resolvent identity into the smaller
covariance and a one-sided right factor.  This module realizes that exact
factorization on the literal physical terminal carriers of the generated
source tower.  Exterior Section C cutoffs are deliberately left to the next
source-facing layer.
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
set_option maxHeartbeats 2000000

/-- One complete generated coarse covariance in the physical terminal
coordinates of its source region. -/
noncomputable def generatedPhysicalCoarseCovarianceCoordinates
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
    FinitePiLpField
        (ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
        (SUNLieCoord Nc) →L[ℝ]
      FinitePiLpField
        (ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 s))
        (SUNLieCoord Nc) := by
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM (D.operatorCoarseRegion hpi5 s) depth
    hspacing background budget fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 s) (depth + 1) spacing epsilon background
    budget.toRadiusChain fineSmall
  exact cmp99SourceTerminalCLMTransport hs hs C

/-- The generated one-sided right factor before exterior Section C cutoffs:
the rectangular middle defect followed by the larger covariance. -/
noncomputable def generatedPhysicalCoarseRightFactor
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
      spacing epsilon < 1) :=
  (D.generatedPhysicalCoarseMiddleTransitionDefect hpi5 r hM depth hspacing
    background budget fineSmall hsmall).comp
      (cmp99SourceGeneratedPhysicalCoarseCovariance
        (show 2 ≤ 4 by norm_num) hM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
        hspacing background budget fineSmall hsmall)

/-- The rectangular generated middle defect in the original physical
coordinates of the two consecutive source regions. -/
noncomputable def generatedPhysicalCoarseMiddleTransitionDefectCoordinates
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
    FinitePiLpField
        (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)))
        (SUNLieCoord Nc) →L[ℝ]
      FinitePiLpField
        (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)))
        (SUNLieCoord Nc) := by
  let F := D.generatedPhysicalCoarseMiddleTransitionDefect hpi5 r hM depth
    hspacing background budget fineSmall hsmall
  have hlarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) (depth + 1)
    spacing epsilon background budget.toRadiusChain fineSmall
  have hsmallSpace :=
    cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  exact cmp99SourceTerminalCLMTransport hlarge hsmallSpace F

/-- The one-sided factor in the original physical coordinates of the two
consecutive source regions. -/
noncomputable def generatedPhysicalCoarseRightFactorCoordinates
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
    FinitePiLpField
        (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)))
        (SUNLieCoord Nc) →L[ℝ]
      FinitePiLpField
        (ActiveGaugeRegion.Site
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)))
        (SUNLieCoord Nc) := by
  let F := D.generatedPhysicalCoarseRightFactor hpi5 r hM depth hspacing
    background budget fineSmall hsmall
  have hlarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) (depth + 1)
    spacing epsilon background budget.toRadiusChain fineSmall
  have hsmallSpace :=
    cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  exact cmp99SourceTerminalCLMTransport hlarge hsmallSpace F

/-- The transported right factor is literally the transported middle defect
followed by the transported larger covariance. -/
theorem generatedPhysicalCoarseRightFactorCoordinates_eq_defect_comp_covariance
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
    D.generatedPhysicalCoarseRightFactorCoordinates hpi5 r hM depth hspacing
        background budget fineSmall hsmall =
      (D.generatedPhysicalCoarseMiddleTransitionDefectCoordinates hpi5 r hM
        depth hspacing background budget fineSmall hsmall).comp
      (D.generatedPhysicalCoarseCovarianceCoordinates hpi5
        (cmp99OmegaTransitionIndex r) hM depth hspacing background budget
        fineSmall hsmall) := by
  let F := D.generatedPhysicalCoarseMiddleTransitionDefect hpi5 r hM depth
    hspacing background budget fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
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
  change cmp99SourceTerminalCLMTransport hlarge hsmallSpace (F.comp C) =
    (cmp99SourceTerminalCLMTransport hlarge hsmallSpace F).comp
      (cmp99SourceTerminalCLMTransport hlarge hlarge C)
  exact (cmp99SourceTerminalCLMTransport_comp hlarge hlarge hsmallSpace F C).symm

/-- Exact source-facing second-resolvent factorization in physical terminal
coordinates. -/
theorem generatedPhysicalCoarseCovarianceTransitionCoordinates_eq_comp_rightFactor
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
    D.generatedPhysicalCoarseCovarianceTransitionCoordinates hpi5 r hM depth
        hspacing background budget fineSmall hsmall =
      (D.generatedPhysicalCoarseCovarianceCoordinates hpi5
        (cmp99OmegaTransitionNextIndex r) hM depth hspacing background budget
        fineSmall hsmall).comp
      (D.generatedPhysicalCoarseRightFactorCoordinates hpi5 r hM depth
        hspacing background budget fineSmall hsmall) := by
  let T := D.generatedPhysicalCoarseCovarianceTransition hpi5 r hM depth
    hspacing background budget fineSmall hsmall
  let Csmall := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
    hspacing background budget fineSmall hsmall
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
  change cmp99SourceTerminalCLMTransport hlarge hsmallSpace T =
    (cmp99SourceTerminalCLMTransport hsmallSpace hsmallSpace Csmall).comp
      (cmp99SourceTerminalCLMTransport hlarge hsmallSpace F)
  have hres := D.generatedPhysicalCoarseCovariance_transition_resolvent hpi5
    r hM depth hspacing background budget fineSmall hsmall
  change T = Csmall.comp F at hres
  rw [hres]
  exact (cmp99SourceTerminalCLMTransport_comp hlarge hsmallSpace hsmallSpace
    Csmall F).symm

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG

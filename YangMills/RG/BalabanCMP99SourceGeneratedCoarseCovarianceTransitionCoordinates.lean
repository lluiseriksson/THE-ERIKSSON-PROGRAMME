/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedTerminalCoordinates
import YangMills.RG.BalabanCMP99SourceGeneratedCoarseCovarianceTransitionNorm

/-!
# Physical coordinates of the generated coarse-covariance transition

The complete terminal Hilbert-bundle equality realizes the literal
rectangular covariance transition on the two original source regions.  The
transport is isometric, so the existing volume-independent operator bound is
preserved exactly.
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
set_option maxHeartbeats 1000000

/-- The literal generated coarse-covariance transition in the physical
terminal coordinates of the two consecutive source regions. -/
noncomputable def generatedPhysicalCoarseCovarianceTransitionCoordinates
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
  let C := D.generatedPhysicalCoarseCovarianceTransition hpi5 r hM depth
    hspacing background budget fineSmall hsmall
  have hlarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) (depth + 1)
    spacing epsilon background budget.toRadiusChain fineSmall
  have hsmallCarrier :=
    cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  exact cmp99SourceTerminalCLMTransport hlarge hsmallCarrier C

/-- The physical coordinate realization preserves the already established
volume-independent operator-norm estimate. -/
theorem norm_generatedPhysicalCoarseCovarianceTransitionCoordinates_le
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
    ‖D.generatedPhysicalCoarseCovarianceTransitionCoordinates hpi5 r hM
      depth hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalCoarseCovarianceTransitionNormBound
        4 M depth spacing epsilon := by
  let C := D.generatedPhysicalCoarseCovarianceTransition hpi5 r hM depth
    hspacing background budget fineSmall hsmall
  let hlarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) (depth + 1)
    spacing epsilon background budget.toRadiusChain fineSmall
  let hsmallCarrier :=
    cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  change ‖cmp99SourceTerminalCLMTransport hlarge hsmallCarrier C‖ ≤ _
  rw [norm_cmp99SourceTerminalCLMTransport]
  exact D.norm_generatedPhysicalCoarseCovarianceTransition_le hpi5 r hM
    depth hspacing background budget fineSmall hsmall

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG

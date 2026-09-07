/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedQprimeTransition
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalCoarseCovariance
import YangMills.RG.BalabanCMP99SourceRegionalCoarseCovarianceTransition

/-!
# Generated CMP99 coarse-covariance transition

This file transports the exact generated fine-space Green mismatch through
the complete physical `Q'` tower.  Both the fine and terminal carriers change
at a consecutive `Omega` transition, so all defects remain rectangular.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {Q M Nc j : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- Transparent form of one generated middle operator.  Keeping this
unfolding in a separate endpoint prevents the rectangular comparison from
normalizing two complete dependent towers simultaneously. -/
theorem generatedPhysicalCoarseCovarianceMiddle_eq_Qprime_green_sq
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
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      (D.operatorCoarseRegion hpi5 s) (depth + 1)
    let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 s) depth hspacing background budget
      fineSmall hsmall
    cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
        (show 2 ≤ 4 by norm_num) hM (D.operatorCoarseRegion hpi5 s) depth
        hspacing background budget fineSmall hsmall =
      T.Qprime.comp (G.comp (G.comp T.weightedAdjoint)) := by
  rfl

/-- Rectangular defect of the two complete generated middle operators
`Q' G'^2 Q'^dagger`. -/
noncomputable def generatedPhysicalCoarseMiddleTransitionDefect
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
  cmp99TypedPrecisionDefect
    (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
      (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
      hspacing background budget fineSmall hsmall)
    (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
      (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
      hspacing background budget fineSmall hsmall)
    (D.generatedTerminalRestriction hpi5 r hM depth spacing epsilon
      background budget fineSmall)

/-- The complete `Q'` transport of the generated fine Green mismatch. -/
noncomputable def generatedPhysicalCoarseMiddleGreenTransport
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
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
    (depth + 1)
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
    (depth + 1)
  let Tsmall := regionsSmall.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Tlarge := regionsLarge.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Gsmall := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
    hspacing background budget fineSmall hsmall
  let Glarge := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
    hspacing background budget fineSmall hsmall
  let H : ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
          (depth + 1)) (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
          (depth + 1)) (SUNLieCoord Nc) := by
    change ActiveGaugeZeroCochain
        (D.operatorRegion hpi5 (cmp99OmegaTransitionIndex r) (depth + 1))
          (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (D.operatorRegion hpi5 (cmp99OmegaTransitionNextIndex r) (depth + 1))
          (SUNLieCoord Nc)
    exact D.generatedPhysicalGreenTransition (M := M) hpi5 r hM depth
      hspacing background budget fineSmall hsmall
  show Tlarge.TerminalSpace.carrier →L[ℝ] Tsmall.TerminalSpace.carrier from
    -(Tsmall.Qprime.comp ((Gsmall.comp H + H.comp Glarge).comp
      Tlarge.weightedAdjoint))

/- The generated coarse-middle defect is exactly the complete `Q'`
transport of the generated fine Green mismatch. -/
set_option maxHeartbeats 2000000 in
theorem generatedPhysicalCoarseMiddleTransitionDefect_eq_greenMismatch
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
    D.generatedPhysicalCoarseMiddleTransitionDefect hpi5 r hM depth hspacing
        background budget fineSmall hsmall =
      D.generatedPhysicalCoarseMiddleGreenTransport hpi5 r hM depth hspacing
        background budget fineSmall hsmall := by
  unfold generatedPhysicalCoarseMiddleTransitionDefect
  unfold generatedPhysicalCoarseMiddleGreenTransport
  rw [D.generatedPhysicalCoarseCovarianceMiddle_eq_Qprime_green_sq hpi5
      (cmp99OmegaTransitionIndex r) hM depth hspacing background budget
      fineSmall hsmall,
    D.generatedPhysicalCoarseCovarianceMiddle_eq_Qprime_green_sq hpi5
      (cmp99OmegaTransitionNextIndex r) hM depth hspacing background budget
      fineSmall hsmall]
  apply typedCoarseMiddleDefect_eq_greenMismatch
  · exact D.generatedQprime_transition hpi5 r hM depth spacing epsilon
      background budget fineSmall
  · exact D.generatedWeightedAdjoint_transition hpi5 r hM depth spacing epsilon
      background budget fineSmall

/-- Literal rectangular mismatch of the two generated physical coarse
covariances. -/
noncomputable def generatedPhysicalCoarseCovarianceTransition
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
  (cmp99SourceGeneratedPhysicalCoarseCovariance (show 2 ≤ 4 by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
    hspacing background budget fineSmall hsmall).comp
      (D.generatedTerminalRestriction hpi5 r hM depth spacing epsilon
        background budget fineSmall) -
  (D.generatedTerminalRestriction hpi5 r hM depth spacing epsilon
    background budget fineSmall).comp
      (cmp99SourceGeneratedPhysicalCoarseCovariance (show 2 ≤ 4 by norm_num) hM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
        hspacing background budget fineSmall hsmall)

/- Exact rectangular resolvent identity for the generated physical coarse
covariance. -/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem generatedPhysicalCoarseCovariance_transition_resolvent
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
    D.generatedPhysicalCoarseCovarianceTransition hpi5 r hM depth hspacing
        background budget fineSmall hsmall =
      (cmp99SourceGeneratedPhysicalCoarseCovariance (show 2 ≤ 4 by norm_num) hM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
        hspacing background budget fineSmall hsmall).comp
        ((D.generatedPhysicalCoarseMiddleTransitionDefect hpi5 r hM depth
          hspacing background budget fineSmall hsmall).comp
          (cmp99SourceGeneratedPhysicalCoarseCovariance (show 2 ≤ 4 by norm_num) hM
            (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
            hspacing background budget fineSmall hsmall)) := by
  unfold generatedPhysicalCoarseCovarianceTransition
  exact typedGreen_transition_resolvent
    (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
      hspacing background budget fineSmall hsmall)
    (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
      hspacing background budget fineSmall hsmall)
    (cmp99SourceGeneratedPhysicalCoarseCovariance (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
      hspacing background budget fineSmall hsmall)
    (cmp99SourceGeneratedPhysicalCoarseCovariance (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
      hspacing background budget fineSmall hsmall)
    (D.generatedTerminalRestriction hpi5 r hM depth spacing epsilon background
      budget fineSmall)
    (cmp99SourceGeneratedPhysicalCoarseCovariance_middle_comp
      (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r)) depth
      hspacing background budget fineSmall hsmall)
    (cmp99SourceGeneratedPhysicalCoarseCovariance_comp_middle
      (show 2 ≤ 4 by norm_num) hM
      (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r)) depth
      hspacing background budget fineSmall hsmall)

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG

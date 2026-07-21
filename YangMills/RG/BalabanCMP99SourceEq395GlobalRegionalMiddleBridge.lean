/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395PhysicalFamily
import YangMills.RG.BalabanCMP99SourceGeneratedArbitraryGreenTransitionDecay

/-!
# The exact global--regional middle bridge in CMP99 equation (3.95)

The second grouped correction in (3.95) compares the generated middle on
the full coarse torus with the one on the physical `Pi^4` region.  This file
instantiates the arbitrary nested-region transition with those two literal
regions.  The result removes the former mismatch between the global object
and the consecutive-only transition API.

The remaining analytic obligation is the decay of the displayed rectangular
Green mismatch; it is not replaced by an assumption here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

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

/-- The physical regional coarse carrier `Omega_j = tilde Pi^4` is a
subregion of the literal full coarse torus. -/
theorem cmp99Eq395PhysicalRegion_subset_full
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5) :
    (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)).sites ⊆
      (cmp99Eq395FullCoarseRegion (Q := Q)).sites := by
  intro x hx
  simp [cmp99Eq395FullCoarseRegion]

/-- Literal typed global--regional middle defect for one source cell. -/
noncomputable def cmp99Eq395PhysicalGlobalRegionalMiddleDefect
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  cmp99SourceGeneratedNestedCoarseMiddleDefect
    (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))
    (cmp99Eq395FullCoarseRegion (Q := Q))
    (D.cmp99Eq395PhysicalRegion_subset_full hpi5)
    hM depth hspacing background budget fineSmall hsmall

/-- The corresponding complete `Q'` transport of the full-to-`Pi^4` Green
mismatch. -/
noncomputable def cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransport
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  cmp99SourceGeneratedNestedCoarseMiddleGreenTransport
    (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))
    (cmp99Eq395FullCoarseRegion (Q := Q))
    hM depth hspacing background budget fineSmall hsmall

/- The exact source-specific bridge for the middle comparison in (3.95). -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefect_eq_greenMismatch
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
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
    D.cmp99Eq395PhysicalGlobalRegionalMiddleDefect hpi5 hM depth hspacing
        background budget fineSmall hsmall =
      D.cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransport hpi5 hM depth
        hspacing background budget fineSmall hsmall := by
  exact cmp99SourceGeneratedNestedCoarseMiddleDefect_eq_greenMismatch
    (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))
    (cmp99Eq395FullCoarseRegion (Q := Q))
    (D.cmp99Eq395PhysicalRegion_subset_full hpi5)
    hM depth hspacing background budget fineSmall hsmall

/- The full-to-`Pi^4` Green mismatch has the same volume-independent
Combes--Thomas decay as a consecutive regional transition. -/
theorem cmp99Eq395PhysicalGlobalRegionalGreenTransition_exponentialKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
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
    FinitePiLpTypedExponentialKernelBound
      (cmp99SourceGeneratedNestedPhysicalGreenTransition
        (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))
        (cmp99Eq395FullCoarseRegion (Q := Q))
        hM depth hspacing background budget fineSmall hsmall)
      (fun target source => finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalGreenTransitionDecayAmplitude
        M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 3) := by
  exact cmp99SourceGeneratedNestedPhysicalGreenTransition_exponentialKernelBound
    (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))
    (cmp99Eq395FullCoarseRegion (Q := Q))
    (D.cmp99Eq395PhysicalRegion_subset_full hpi5)
    hM depth hspacing background budget fineSmall hsmall

/-- The global--regional middle defect in the literal physical terminal
coordinates of the full torus and `Pi^4`. -/
noncomputable def cmp99Eq395PhysicalGlobalRegionalMiddleDefectCoordinates
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
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
    ActiveGaugeZeroCochain (cmp99Eq395FullCoarseRegion (Q := Q))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))
        (SUNLieCoord Nc) := by
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let C := D.cmp99Eq395PhysicalGlobalRegionalMiddleDefect hpi5 hM depth
    hspacing background budget fineSmall hsmall
  have hlarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    OmegaLarge (depth + 1) spacing epsilon background budget.toRadiusChain
    fineSmall
  have hsmallCarrier :=
    cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      OmegaSmall (depth + 1) spacing epsilon background budget.toRadiusChain
      fineSmall
  exact cmp99SourceTerminalCLMTransport hlarge hsmallCarrier C

/-- Physical-coordinate realization of the complete `Q'` transport of the
full-to-`Pi^4` Green mismatch. -/
noncomputable def cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportCoordinates
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
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
    ActiveGaugeZeroCochain (cmp99Eq395FullCoarseRegion (Q := Q))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))
        (SUNLieCoord Nc) := by
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let C := D.cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransport hpi5 hM
    depth hspacing background budget fineSmall hsmall
  have hlarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    OmegaLarge (depth + 1) spacing epsilon background budget.toRadiusChain
    fineSmall
  have hsmallCarrier :=
    cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      OmegaSmall (depth + 1) spacing epsilon background budget.toRadiusChain
      fineSmall
  exact cmp99SourceTerminalCLMTransport hlarge hsmallCarrier C

/- The exact Green-mismatch identity survives isometric realization in the
literal physical coarse coordinates. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefectCoordinates_eq_greenMismatch
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
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
    D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectCoordinates hpi5 hM depth
        hspacing background budget fineSmall hsmall =
      D.cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportCoordinates hpi5
        hM depth hspacing background budget fineSmall hsmall := by
  unfold cmp99Eq395PhysicalGlobalRegionalMiddleDefectCoordinates
  unfold cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportCoordinates
  exact congrArg
    (cmp99SourceTerminalCLMTransport
      (cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
        (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
        (cmp99Eq395FullCoarseRegion (Q := Q)) (depth + 1) spacing epsilon
        background budget.toRadiusChain fineSmall)
      (cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
        (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
        (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)) (depth + 1)
        spacing epsilon background budget.toRadiusChain fineSmall))
    (D.cmp99Eq395PhysicalGlobalRegionalMiddleDefect_eq_greenMismatch hpi5 hM
      depth hspacing background budget fineSmall hsmall)

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG

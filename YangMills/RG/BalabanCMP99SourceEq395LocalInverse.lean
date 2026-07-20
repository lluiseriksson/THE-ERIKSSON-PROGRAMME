/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395Partition
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCRightFactor

/-!
# The physical local inverse in CMP99 equation (3.95)

For one generated source region this file transports the literal middle
operator `Q' (G')² Q'^*` to its coarse coordinates and proves that its
generated covariance is an exact right inverse there.  This is the
`A_D C_D = I` ingredient in (3.95), not an abstract inverse certificate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

/-- Transporting an identity operator along one equality of terminal Hilbert
bundles is again the identity operator. -/
theorem cmp99SourceTerminalCLMTransport_id
    {E E' : CMP99SourceWeightedTowerHilbertSpace} (hE : E = E') :
    cmp99SourceTerminalCLMTransport hE hE
        (ContinuousLinearMap.id ℝ E.carrier) =
      ContinuousLinearMap.id ℝ E'.carrier := by
  cases hE
  rfl

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

/-- The literal regional middle `Q' (G')² Q'^*`, expressed on the same
finite coarse coordinate field as its generated inverse covariance. -/
noncomputable def generatedPhysicalCoarseCovarianceMiddleCoordinates
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
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM (D.operatorCoarseRegion hpi5 s) depth
    hspacing background budget fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    (D.operatorCoarseRegion hpi5 s) (depth + 1) spacing epsilon background
    budget.toRadiusChain fineSmall
  exact cmp99SourceTerminalCLMTransport hs hs Middle

/-- Exact physical local inverse identity `A_D C_D = I` in the common
coarse coordinates used by the Section C factors. -/
theorem generatedPhysicalCoarseCovarianceMiddleCoordinates_comp_covariance
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
    (D.generatedPhysicalCoarseCovarianceMiddleCoordinates hpi5 s hM depth
      hspacing background budget fineSmall hsmall).comp
      (D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
        hspacing background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ _ := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    Omega (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  have hinverse : Middle.comp C = ContinuousLinearMap.id ℝ _ :=
    cmp99SourceGeneratedPhysicalCoarseCovariance_middle_comp
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
  change (cmp99SourceTerminalCLMTransport hs hs Middle).comp
      (cmp99SourceTerminalCLMTransport hs hs C) = _
  rw [cmp99SourceTerminalCLMTransport_comp, hinverse]
  exact cmp99SourceTerminalCLMTransport_id hs

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG

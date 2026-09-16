/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GlobalRegionalMiddleBridge
import YangMills.RG.BalabanCMP99SourceEq395GlobalMiddleTransport

/-!
# Fixed-rate decay of the CMP99 global--regional middle defect

This module exposes the full-to-`Pi^4` middle defect in literal terminal
coordinates.  The generated analysis is the scaled adjoint of the physical
weighted synthesis, so both external legs have their already proved exact
terminal-block support.
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

/-- Bundle transport of a rectangular sandwich with two different physical
middle spaces. -/
theorem cmp99SourceTerminalCLMTransport_rectangularSandwich
    {Elarge Elarge' Esmall Esmall' Flarge Fsmall :
      CMP99SourceWeightedTowerHilbertSpace}
    (hlarge : Elarge = Elarge') (hsmall : Esmall = Esmall')
    (Q : Fsmall.carrier →L[ℝ] Esmall.carrier)
    (H : Flarge.carrier →L[ℝ] Fsmall.carrier)
    (W : Elarge.carrier →L[ℝ] Flarge.carrier) :
    cmp99SourceTerminalCLMTransport hlarge hsmall (Q.comp (H.comp W)) =
      (cmp99SourceTerminalCLMTransport rfl hsmall Q).comp
        (H.comp (cmp99SourceTerminalCLMTransport hlarge rfl W)) := by
  subst Elarge'
  subst Esmall'
  rfl

namespace CMP99SourceDependentOmegaGeometry

/-- Source-faithful coordinate formula for the complete middle transport:
the fine Green mismatch is sandwiched between the physical generated
synthesis on the full region and the scaled adjoint synthesis on `Pi^4`. -/
noncomputable def cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportPhysical
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
      spacing epsilon < 1) := by
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaSmall (depth + 1)
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaLarge (depth + 1)
  let Wsmall := regionsSmall.physicalWeightedAdjoint
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  let Wlarge := regionsLarge.physicalWeightedAdjoint
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  let Gsmall := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaSmall depth hspacing background budget fineSmall hsmall
  let Glarge := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaLarge depth hspacing background budget fineSmall hsmall
  let H := cmp99SourceGeneratedNestedPhysicalGreenTransition OmegaSmall
    OmegaLarge hM depth hspacing background budget fineSmall hsmall
  let Inner := Gsmall.comp H + H.comp Glarge
  exact -((cmp99Eq395GeneratedQprimeScale M depth spacing • Wsmall.adjoint).comp
    (Inner.comp Wlarge))

set_option maxRecDepth 5000
set_option synthInstance.maxHeartbeats 3000000 in
set_option maxHeartbeats 8000000 in
/- The dependent-tower transport constructed by the global--regional bridge
is exactly the source-faithful physical formula above. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportCoordinates_eq_physical
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
    let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
    let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
    let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      OmegaSmall (depth + 1)
    let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      OmegaLarge (depth + 1)
    let Tsmall := regionsSmall.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    let Tlarge := regionsLarge.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    let hTsmall := regionsSmall.weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
    let hTlarge := regionsLarge.weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
    let hsSmall := hTsmall.trans
      (regionsSmall.terminalHilbertSpace_eq_coordinate (Nc := Nc))
    let hsLarge := hTlarge.trans
      (regionsLarge.terminalHilbertSpace_eq_coordinate (Nc := Nc))
    cmp99SourceTerminalCLMTransport hsLarge hsSmall
        (D.cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransport hpi5 hM
          depth hspacing background budget fineSmall hsmall) =
      D.cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportPhysical hpi5 hM
        depth hspacing background budget fineSmall hsmall := by
  dsimp only
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let Psmall := cmp99SourcePhysicalTerminalHilbertSpace Nc
    (cmp99IteratedLiftActiveRegion (M := M) OmegaSmall (depth + 1))
  let Plarge := cmp99SourcePhysicalTerminalHilbertSpace Nc
    (cmp99IteratedLiftActiveRegion (M := M) OmegaLarge (depth + 1))
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaSmall (depth + 1)
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaLarge (depth + 1)
  let Tsmall := regionsSmall.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Tlarge := regionsLarge.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Wsmall := regionsSmall.physicalWeightedAdjoint
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  let Wlarge := regionsLarge.physicalWeightedAdjoint
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  let Gsmall := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaSmall depth hspacing background budget fineSmall hsmall
  let Glarge := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaLarge depth hspacing background budget fineSmall hsmall
  let H := cmp99SourceGeneratedNestedPhysicalGreenTransition OmegaSmall
    OmegaLarge hM depth hspacing background budget fineSmall hsmall
  let Inner := Gsmall.comp H + H.comp Glarge
  let hTsmall : Tsmall.TerminalSpace = regionsSmall.terminalHilbertSpace Nc :=
    regionsSmall.weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
  let hTlarge : Tlarge.TerminalSpace = regionsLarge.terminalHilbertSpace Nc :=
    regionsLarge.weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
  let Esmall' := regionsSmall.terminalCoordinateHilbertSpace (Nc := Nc)
  let Elarge' := regionsLarge.terminalCoordinateHilbertSpace (Nc := Nc)
  let hsSmall := hTsmall.trans
    (regionsSmall.terminalHilbertSpace_eq_coordinate (Nc := Nc))
  let hsLarge := hTlarge.trans
    (regionsLarge.terminalHilbertSpace_eq_coordinate (Nc := Nc))
  let Qt := cmp99SourceTerminalCLMTransport
    (E := Psmall) (F := Tsmall.TerminalSpace)
    (E' := Psmall) (F' := Esmall') rfl hsSmall Tsmall.Qprime
  let Wt := cmp99SourceTerminalCLMTransport
    (E := Tlarge.TerminalSpace) (F := Plarge)
    (E' := Elarge') (F' := Plarge) hsLarge rfl Tlarge.weightedAdjoint
  have hterminalEq : Tsmall.terminalSpacing =
      (M : ℝ) ^ (depth + 1) * spacing :=
    regionsSmall.weightedQprimeTower_terminalSpacing
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
      background budget.toRadiusChain fineSmall
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by omega)
  have hterminal : 0 < Tsmall.terminalSpacing := by
    rw [hterminalEq]
    exact mul_pos (pow_pos hMpos _) hspacing
  have hQ := Tsmall.Qprime_eq_smul_weightedAdjoint_adjoint hterminal
  have hWsmall := regionsSmall.physicalWeightedAdjoint_eq_transported
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  have hWlarge := regionsLarge.physicalWeightedAdjoint_eq_transported
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  have hWt : Wt = Wlarge := by
    change regionsLarge.transportedWeightedAdjoint
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
      background budget.toRadiusChain fineSmall = Wlarge
    exact hWlarge.symm
  have hQt : Qt =
      cmp99Eq395GeneratedQprimeScale M depth spacing • Wsmall.adjoint := by
    let a := spacing ^ 4 / Tsmall.terminalSpacing ^ 4
    have hQ' : Qt = cmp99SourceTerminalCLMTransport rfl hsSmall
        (a • Tsmall.weightedAdjoint.adjoint) :=
      congrArg (cmp99SourceTerminalCLMTransport
        (E := Psmall) (F := Tsmall.TerminalSpace)
        (E' := Psmall) (F' := Esmall') rfl hsSmall) hQ
    have hsmul := cmp99SourceTerminalCLMTransport_smul
      (E := Psmall) (F := Tsmall.TerminalSpace)
      (E' := Psmall) (F' := Esmall') rfl hsSmall a
      Tsmall.weightedAdjoint.adjoint
    have hadj := cmp99SourceTerminalCLMTransport_adjoint
      (E := Tsmall.TerminalSpace) (F := Psmall)
      (E' := Esmall') (F' := Psmall) hsSmall rfl
      Tsmall.weightedAdjoint
    have hWtSmall : cmp99SourceTerminalCLMTransport
        (E := Tsmall.TerminalSpace) (F := Psmall)
        (E' := Esmall') (F' := Psmall) hsSmall rfl
        Tsmall.weightedAdjoint = Wsmall := by
      change regionsSmall.transportedWeightedAdjoint
        (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
        background budget.toRadiusChain fineSmall = Wsmall
      exact hWsmall.symm
    calc
      Qt = cmp99SourceTerminalCLMTransport rfl hsSmall
          (a • Tsmall.weightedAdjoint.adjoint) := hQ'
      _ = a • cmp99SourceTerminalCLMTransport rfl hsSmall
          Tsmall.weightedAdjoint.adjoint := hsmul
      _ = a • (cmp99SourceTerminalCLMTransport hsSmall rfl
          Tsmall.weightedAdjoint).adjoint := congrArg (fun C => a • C) hadj
      _ = a • Wsmall.adjoint := by rw [hWtSmall]; rfl
      _ = cmp99Eq395GeneratedQprimeScale M depth spacing • Wsmall.adjoint := by
        dsimp [cmp99Eq395GeneratedQprimeScale, a]
        rw [hterminalEq]
  unfold cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransport
  unfold cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportPhysical
  dsimp only
  change cmp99SourceTerminalCLMTransport hsLarge hsSmall
      (-(Tsmall.Qprime.comp (Inner.comp Tlarge.weightedAdjoint))) =
    -((cmp99Eq395GeneratedQprimeScale M depth spacing • Wsmall.adjoint).comp
      (Inner.comp Wlarge))
  have hsand := cmp99SourceTerminalCLMTransport_rectangularSandwich
    (Elarge := Tlarge.TerminalSpace) (Elarge' := Elarge')
    (Esmall := Tsmall.TerminalSpace) (Esmall' := Esmall')
    (Flarge := Plarge) (Fsmall := Psmall)
    hsLarge hsSmall Tsmall.Qprime Inner Tlarge.weightedAdjoint
  calc
    cmp99SourceTerminalCLMTransport hsLarge hsSmall
        (-(Tsmall.Qprime.comp (Inner.comp Tlarge.weightedAdjoint))) =
      -(cmp99SourceTerminalCLMTransport hsLarge hsSmall
        (Tsmall.Qprime.comp (Inner.comp Tlarge.weightedAdjoint))) := by
          rw [show -(Tsmall.Qprime.comp (Inner.comp Tlarge.weightedAdjoint)) =
            (-1 : ℝ) • (Tsmall.Qprime.comp
              (Inner.comp Tlarge.weightedAdjoint)) by simp]
          rw [cmp99SourceTerminalCLMTransport_smul]
          exact neg_one_smul ℝ _
    _ = -(Qt.comp (Inner.comp Wt)) := congrArg Neg.neg hsand
    _ = -((cmp99Eq395GeneratedQprimeScale M depth spacing • Wsmall.adjoint).comp
        (Inner.comp Wlarge)) := by rw [hQt, hWt]; rfl

/-- The original full-to-`Pi^4` middle defect, transported only to the literal
terminal coordinates of its two generated towers. -/
noncomputable def cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates
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
      spacing epsilon < 1) := by
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaSmall (depth + 1)
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaLarge (depth + 1)
  let Tsmall := regionsSmall.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Tlarge := regionsLarge.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let hsSmall := (regionsSmall.weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall).trans
      (regionsSmall.terminalHilbertSpace_eq_coordinate (Nc := Nc))
  let hsLarge := (regionsLarge.weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall).trans
      (regionsLarge.terminalHilbertSpace_eq_coordinate (Nc := Nc))
  exact cmp99SourceTerminalCLMTransport hsLarge hsSmall
    (D.cmp99Eq395PhysicalGlobalRegionalMiddleDefect hpi5 hM depth hspacing
      background budget fineSmall hsmall)

set_option maxRecDepth 5000
set_option synthInstance.maxHeartbeats 3000000 in
set_option maxHeartbeats 8000000 in
/- The terminal-coordinate defect is literally the source-faithful physical
Green-mismatch sandwich. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates_eq_physical
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
    D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates hpi5 hM
        depth hspacing background budget fineSmall hsmall =
      D.cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportPhysical hpi5 hM
        depth hspacing background budget fineSmall hsmall := by
  unfold cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates
  rw [D.cmp99Eq395PhysicalGlobalRegionalMiddleDefect_eq_greenMismatch]
  exact D.cmp99Eq395PhysicalGlobalRegionalMiddleGreenTransportCoordinates_eq_physical
    hpi5 hM depth hspacing background budget fineSmall hsmall

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GlobalRegionalMiddleSourceAdjointDecay
import YangMills.RG.BalabanCMP99SourceEq395AmbientMiddleDecay
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalTerminalRestriction
import YangMills.RG.BalabanCMP99SourceGeneratedMiddleSymmetry

/-!
# Ambient realization of the CMP99 global--regional middle defect

This module identifies the explicit isometric reindexing used by the
source-coordinate decay theorem with transport of the same rectangular
operator between the two physical terminal Hilbert bundles.  It is the
coordinate bridge needed before the adjoint rectangular defect can be
inserted into the ambient atom of equation (3.95).
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

/-- Extending first to a larger active region and then to the ambient field
agrees with direct extension from the smaller nested region. -/
theorem extendZero_comp_nestedActiveRegionExtension
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites) :
    (extendZeroZeroCLM (𝔤 := g) OmegaLarge).comp
        (cmp99NestedActiveRegionExtension OmegaSmall OmegaLarge) =
      extendZeroZeroCLM OmegaSmall := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  by_cases hx : x ∈ OmegaSmall.sites
  · have hxLarge : x ∈ OmegaLarge.sites := hsub hx
    simp [cmp99NestedActiveRegionExtension, restrictZeroCLM,
      extendZeroZeroCLM, hx, hxLarge]
  · simp [cmp99NestedActiveRegionExtension, restrictZeroCLM,
      extendZeroZeroCLM, hx]

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 5000 in
set_option maxHeartbeats 10000000 in
/-- Reindexing the rectangular defect by the two canonical terminal-site
casts is exactly transport between the corresponding physical Hilbert
bundles. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource_eq_transport
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
    let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) OmegaSmall (depth + 1)
    let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) OmegaLarge (depth + 1)
    let hCoordSmall := regionsSmall.terminalHilbertSpace_eq_coordinate (Nc := Nc)
    let hCoordLarge := regionsLarge.terminalHilbertSpace_eq_coordinate (Nc := Nc)
    let hPhysSmall :=
      cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
        (Nc := Nc) (M := M) OmegaSmall (depth + 1)
    let hPhysLarge :=
      cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
        (Nc := Nc) (M := M) OmegaLarge (depth + 1)
    let hsSmall := hCoordSmall.symm.trans hPhysSmall
    let hsLarge := hCoordLarge.symm.trans hPhysLarge
    D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource hpi5 hM depth
        hspacing background budget fineSmall hsmall =
      cmp99SourceTerminalCLMTransport hsLarge hsSmall
        (D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates
          hpi5 hM depth hspacing background budget fineSmall hsmall) := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro f
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) OmegaSmall (depth + 1)
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) OmegaLarge (depth + 1)
  let hsiteSmall := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) OmegaSmall (depth + 1)
  let hsiteLarge := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) OmegaLarge (depth + 1)
  let hCoordSmall := regionsSmall.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hCoordLarge := regionsLarge.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hPhysSmall :=
    cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
      (Nc := Nc) (M := M) OmegaSmall (depth + 1)
  let hPhysLarge :=
    cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
      (Nc := Nc) (M := M) OmegaLarge (depth + 1)
  let hsSmall := hCoordSmall.symm.trans hPhysSmall
  let hsLarge := hCoordLarge.symm.trans hPhysLarge
  let C :=
    D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates hpi5 hM
      depth hspacing background budget fineSmall hsmall
  let sourceBack :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
      (Equiv.cast hsiteLarge).symm).toContinuousLinearEquiv
  let targetMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
      (Equiv.cast hsiteSmall)).toContinuousLinearEquiv
  change targetMap (C (sourceBack f)) =
    cmp99SourceTerminalCLMTransport hsLarge hsSmall C f
  have hback : HEq (sourceBack f) f := by
    simpa only [sourceBack, Equiv.cast_symm] using
      (finitePiLpCongrLeft_cast_heq hsiteLarge.symm f)
  have hC : HEq (C (sourceBack f))
      (cmp99SourceTerminalCLMTransport hsLarge hsSmall C f) :=
    cmp99SourceTerminalCLMTransport_apply_heq hsLarge hsSmall C hback
  have hforward : HEq (targetMap (C (sourceBack f)))
      (C (sourceBack f)) := by
    exact finitePiLpCongrLeft_cast_heq hsiteSmall (C (sourceBack f))
  exact eq_of_heq (hforward.trans hC)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 10000000 in
/-- After composing the coordinate and physical bundle identifications, the
source-coordinate defect is directly the original typed defect transported
to the two physical source regions. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource_eq_directTransport
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
    let hsSmall := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) OmegaSmall
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
    let hsLarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) OmegaLarge
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
    D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource hpi5 hM depth
        hspacing background budget fineSmall hsmall =
      cmp99SourceTerminalCLMTransport hsLarge hsSmall
        (D.cmp99Eq395PhysicalGlobalRegionalMiddleDefect hpi5 hM depth
          hspacing background budget fineSmall hsmall) := by
  dsimp only
  rw [D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource_eq_transport]
  unfold cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates
  dsimp only
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) OmegaSmall (depth + 1)
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) OmegaLarge (depth + 1)
  let hTsmall := regionsSmall.weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  let hTlarge := regionsLarge.weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  let hCoordSmall := regionsSmall.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hCoordLarge := regionsLarge.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hPhysSmall :=
    cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
      (Nc := Nc) (M := M) OmegaSmall (depth + 1)
  let hPhysLarge :=
    cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
      (Nc := Nc) (M := M) OmegaLarge (depth + 1)
  let C := D.cmp99Eq395PhysicalGlobalRegionalMiddleDefect hpi5 hM depth
    hspacing background budget fineSmall hsmall
  have htrans := cmp99SourceTerminalCLMTransport_trans
    (hTlarge.trans hCoordLarge) (hTsmall.trans hCoordSmall)
    (hCoordLarge.symm.trans hPhysLarge) (hCoordSmall.symm.trans hPhysSmall) C
  simpa using htrans

set_option maxRecDepth 5000 in
set_option maxHeartbeats 10000000 in
/-- In the original source coordinates the rectangular defect is literally
`R A - A_D R`, with `R` the physical restriction from the full coarse torus
to `Pi^4`.  No generated terminal map remains. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource_eq_physicalDifference
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
    let Ksmall := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
      (show 2 ≤ 4 by norm_num) hM OmegaSmall depth hspacing background budget
      fineSmall hsmall
    let Klarge := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
      (show 2 ≤ 4 by norm_num) hM OmegaLarge depth hspacing background budget
      fineSmall hsmall
    let hsSmall := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) OmegaSmall
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
    let hsLarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) OmegaLarge
      (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
    let KsmallPhysical : ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) := by
      exact cmp99SourceTerminalCLMTransport hsSmall hsSmall Ksmall
    let KlargePhysical : ActiveGaugeZeroCochain OmegaLarge (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain OmegaLarge (SUNLieCoord Nc) := by
      exact cmp99SourceTerminalCLMTransport hsLarge hsLarge Klarge
    let R := cmp99NestedActiveRegionRestriction
      (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
    D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource hpi5 hM depth
        hspacing background budget fineSmall hsmall =
      R.comp KlargePhysical - KsmallPhysical.comp R := by
  dsimp only
  rw [D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource_eq_directTransport]
  unfold cmp99Eq395PhysicalGlobalRegionalMiddleDefect
  unfold cmp99SourceGeneratedNestedCoarseMiddleDefect
  unfold cmp99TypedPrecisionDefect
  dsimp only
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let Ksmall := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM OmegaSmall depth hspacing background budget
    fineSmall hsmall
  let Klarge := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM OmegaLarge depth hspacing background budget
    fineSmall hsmall
  let Rterminal := cmp99SourceIteratedLiftTerminalRestriction
    (D.cmp99Eq395PhysicalRegion_subset_full hpi5)
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) (depth + 1)
    spacing epsilon background budget.toRadiusChain fineSmall
  let hsSmall := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) OmegaSmall
    (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  let hsLarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) OmegaLarge
    (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  let R := cmp99NestedActiveRegionRestriction
    (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
  let KsmallPhysical : ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) := by
    exact cmp99SourceTerminalCLMTransport hsSmall hsSmall Ksmall
  let KlargePhysical : ActiveGaugeZeroCochain OmegaLarge (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain OmegaLarge (SUNLieCoord Nc) := by
    exact cmp99SourceTerminalCLMTransport hsLarge hsLarge Klarge
  have hR : cmp99SourceTerminalCLMTransport hsLarge hsSmall Rterminal = R :=
    cmp99SourceIteratedLiftTerminalRestriction_transport_eq_physical
      (D.cmp99Eq395PhysicalRegion_subset_full hpi5)
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) (depth + 1)
      spacing epsilon background budget.toRadiusChain fineSmall
  calc
    cmp99SourceTerminalCLMTransport hsLarge hsSmall
        (Rterminal.comp Klarge - Ksmall.comp Rterminal) =
      cmp99SourceTerminalCLMTransport hsLarge hsSmall
          (Rterminal.comp Klarge) -
        cmp99SourceTerminalCLMTransport hsLarge hsSmall
          (Ksmall.comp Rterminal) :=
        cmp99SourceTerminalCLMTransport_sub _ _ _ _
    _ = (cmp99SourceTerminalCLMTransport hsLarge hsSmall Rterminal).comp
          (cmp99SourceTerminalCLMTransport hsLarge hsLarge Klarge) -
        (cmp99SourceTerminalCLMTransport hsSmall hsSmall Ksmall).comp
          (cmp99SourceTerminalCLMTransport hsLarge hsSmall Rterminal) := by
      rw [cmp99SourceTerminalCLMTransport_comp,
        cmp99SourceTerminalCLMTransport_comp]
    _ = R.comp KlargePhysical - KsmallPhysical.comp R := by
      rw [hR]
      rfl

set_option maxRecDepth 6000 in
set_option maxHeartbeats 12000000 in
/-- The adjoint rectangular defect, extended back to the ambient coarse
field, is exactly the global middle followed by the `Pi^4` projector minus
the regional middle.  This is the ambient orientation occurring in (3.95).
-/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefect_adjoint_ambient
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
    let C := D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource hpi5 hM
      depth hspacing background budget fineSmall hsmall
    let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
      budget fineSmall hsmall
    let AD := D.generatedPhysicalCoarseCovarianceMiddleAmbient hpi5
      (cmp99OmegaPi4Index j) hM depth hspacing background budget fineSmall
      hsmall
    let proj := (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) OmegaSmall).comp
      (restrictZeroCLM OmegaSmall)
    (extendZeroZeroCLM OmegaLarge).comp
        (C.adjoint.comp (restrictZeroCLM OmegaSmall)) =
      A.comp proj - AD := by
  dsimp only
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let Ksmall := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM OmegaSmall depth hspacing background budget
    fineSmall hsmall
  let Klarge := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM OmegaLarge depth hspacing background budget
    fineSmall hsmall
  let hsSmall := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) OmegaSmall
    (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  let hsLarge := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) OmegaLarge
    (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  let KsmallPhysical : ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) := by
    exact cmp99SourceTerminalCLMTransport hsSmall hsSmall Ksmall
  let KlargePhysical : ActiveGaugeZeroCochain OmegaLarge (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain OmegaLarge (SUNLieCoord Nc) := by
    exact cmp99SourceTerminalCLMTransport hsLarge hsLarge Klarge
  let R := cmp99NestedActiveRegionRestriction
    (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
  let C := D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource hpi5 hM
    depth hspacing background budget fineSmall hsmall
  have hKsmall : KsmallPhysical.adjoint = KsmallPhysical :=
    cmp99SourceTerminalCLMTransport_adjoint_eq_self hsSmall Ksmall
      (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_adjoint_eq
        (show 2 ≤ 4 by norm_num) hM OmegaSmall depth hspacing background budget
        fineSmall hsmall)
  have hKlarge : KlargePhysical.adjoint = KlargePhysical :=
    cmp99SourceTerminalCLMTransport_adjoint_eq_self hsLarge Klarge
      (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_adjoint_eq
        (show 2 ≤ 4 by norm_num) hM OmegaLarge depth hspacing background budget
        fineSmall hsmall)
  have hC := D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource_eq_physicalDifference
    hpi5 hM depth hspacing background budget fineSmall hsmall
  have hC' : C = R.comp KlargePhysical - KsmallPhysical.comp R := by
    simpa [C, R, KsmallPhysical, KlargePhysical, OmegaSmall, OmegaLarge,
      Ksmall, Klarge, hsSmall, hsLarge] using hC
  have hCadj : C.adjoint =
      KlargePhysical.comp R.adjoint - R.adjoint.comp KsmallPhysical := by
    rw [hC']
    rw [ContinuousLinearMap.adjoint.map_sub]
    simp only [ContinuousLinearMap.adjoint_comp, hKsmall, hKlarge]
  have hRadj : R.adjoint =
      cmp99NestedActiveRegionExtension
        (g := SUNLieCoord Nc) OmegaSmall OmegaLarge :=
    cmp99NestedActiveRegionRestriction_adjoint_eq_extension _ _
  have hExt := extendZero_comp_nestedActiveRegionExtension
    (g := SUNLieCoord Nc) OmegaSmall OmegaLarge
    (D.cmp99Eq395PhysicalRegion_subset_full hpi5)
  have hA : cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
        fineSmall hsmall =
      (extendZeroZeroCLM OmegaLarge).comp
        (KlargePhysical.comp (restrictZeroCLM OmegaLarge)) := by
    unfold cmp99Eq395PhysicalGlobalMiddle
    rfl
  have hAD : D.generatedPhysicalCoarseCovarianceMiddleAmbient hpi5
        (cmp99OmegaPi4Index j) hM depth hspacing background budget fineSmall
        hsmall =
      (extendZeroZeroCLM OmegaSmall).comp
        (KsmallPhysical.comp (restrictZeroCLM OmegaSmall)) := by
    unfold generatedPhysicalCoarseCovarianceMiddleAmbient
    rfl
  rw [hCadj, hRadj]
  rw [hA, hAD]
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    map_sub]
  have hExtApply := congrArg
    (fun T : ActiveGaugeZeroCochain OmegaSmall (SUNLieCoord Nc) →L[ℝ]
        GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc) =>
      T (KsmallPhysical (restrictZeroCLM OmegaSmall f))) hExt
  rw [show extendZeroZeroCLM OmegaLarge
      (cmp99NestedActiveRegionExtension OmegaSmall OmegaLarge
        (KsmallPhysical (restrictZeroCLM OmegaSmall f))) =
      extendZeroZeroCLM OmegaSmall
        (KsmallPhysical (restrictZeroCLM OmegaSmall f)) by
          simpa using hExtApply]
  rfl

/-- The literal `Pi^4` projector also acts as the identity on the physical
smooth cutoff when it is placed on the left.  The source theorem originally
supplies the opposite order; the two orders agree because both operators are
pointwise scalar multipliers. -/
theorem cmp99Eq395PhysicalPi4Projector_comp_smoothMultiplier
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile) :
    ((extendZeroZeroCLM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))).comp
      (restrictZeroCLM
        (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)))).comp
        (cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell) =
      cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell := by
  have hforward :=
    D.cmp95SourcePeriodicCoarseSquarePartition_multiplier_comp_pi4RegionProjector
      hpi5 (Nc := Nc) P
  have hcomm :
      ((extendZeroZeroCLM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))).comp
        (restrictZeroCLM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)))).comp
          (cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell) =
        (cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell).comp
          ((extendZeroZeroCLM
              (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))).comp
            (restrictZeroCLM
              (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)))) := by
    rw [activeGaugeRegion_extendZero_comp_restrict_eq_multiplier]
    unfold cmp99Eq395PhysicalSmoothMultiplier
    rw [finitePiLpScalarMultiplier_comp, finitePiLpScalarMultiplier_comp]
    congr 1
    funext block
    exact mul_comm _ _
  rw [hcomm]
  simpa [cmp99Eq395PhysicalSmoothMultiplier] using hforward

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG

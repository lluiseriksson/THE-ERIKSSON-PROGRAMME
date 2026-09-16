import YangMills.RG.BalabanCMP99SourceEq395PhysicalDistanceDecay

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open YangMills.RG

#check YangMills.RG.cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_transport_eq
#check YangMills.RG.cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
#check YangMills.RG.extendZeroZeroCLM_apply_of_mem
#check YangMills.RG.singleFinitePiLp
#check YangMills.RG.restrictZeroCLM
#check YangMills.RG.CMP99SourceDependentOmegaGeometry.cmp99Eq395PhysicalGlobalMiddle
#check YangMills.RG.CMP99SourceDependentOmegaGeometry.cmp99Eq395FullCoarseRegion

namespace YangMills.RG.CMP99SourceDependentOmegaGeometry

noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000 in
theorem test_global_eq
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
    cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
        fineSmall hsmall =
      cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
        fineSmall hsmall := rfl

theorem test_transport_trans
    {E F E' F' E'' F'' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F') (hE' : E' = E'') (hF' : F' = F'')
    (C : E.carrier →L[ℝ] F.carrier) :
    cmp99SourceTerminalCLMTransport hE' hF'
        (cmp99SourceTerminalCLMTransport hE hF C) =
      cmp99SourceTerminalCLMTransport (hE.trans hE') (hF.trans hF') C := by
  subst E'
  subst F'
  subst E''
  subst F''
  rfl

noncomputable def test_onOmega
    (Omega : ActiveGaugeRegion 4 (2 * Q))
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
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let hCoord := regions.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hPhys := cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
    (Nc := Nc) (M := M) Omega (depth + 1)
  let h := hCoord.symm.trans hPhys
  exact cmp99SourceTerminalCLMTransport h h
    (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
      budget fineSmall hsmall)

set_option maxHeartbeats 4000000 in
theorem test_global_eq2
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
    cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
        fineSmall hsmall =
      let Omega := cmp99Eq395FullCoarseRegion (Q := Q)
      (extendZeroZeroCLM Omega).comp
        ((test_onOmega Omega hM depth hspacing background budget fineSmall
          hsmall).comp (restrictZeroCLM Omega)) := by
  dsimp only
  unfold cmp99Eq395PhysicalGlobalMiddle test_onOmega
  dsimp only
  let Omega := cmp99Eq395FullCoarseRegion (Q := Q)
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  let hT := regions.weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let hCoord := regions.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hPhys := cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
    (Nc := Nc) (M := M) Omega (depth + 1)
  let hs := hT.trans hPhys
  have hgen := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_transport_eq
    Omega hM depth hspacing background budget fineSmall hsmall
  have htrans := test_transport_trans (hT.trans hCoord) (hT.trans hCoord)
    (hCoord.symm.trans hPhys) (hCoord.symm.trans hPhys) Middle
  rw [hgen] at htrans
  rw [htrans]
  congr

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem test_onOmega_bound
    (Omega : ActiveGaugeRegion 4 (2 * Q))
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
      (test_onOmega Omega hM depth hspacing background budget fineSmall hsmall)
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1)
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4) := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  have hG := cmp99Eq395GeneratedPhysicalMiddle_physicalDist_exponentialKernelBound
    Omega hM depth hspacing background budget fineSmall hsmall
  have hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega (depth + 1)
  cases hsite
  simpa [test_onOmega, cmp99SourceIteratedLiftPhysicalTerminalDist] using hG


end
end YangMills.RG.CMP99SourceDependentOmegaGeometry

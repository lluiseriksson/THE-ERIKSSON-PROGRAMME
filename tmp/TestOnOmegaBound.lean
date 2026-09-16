import YangMills.RG.BalabanCMP99SourceEq395PhysicalDistanceDecay

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

noncomputable def testOnOmega
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

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem testOnOmega_bound
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
      (testOnOmega Omega hM depth hspacing background budget fineSmall hsmall)
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1)
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4) := by
  have hG := cmp99Eq395GeneratedPhysicalMiddle_physicalDist_exponentialKernelBound
    Omega hM depth hspacing background budget fineSmall hsmall
  have hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega (depth + 1)
  cases hsite
  simpa [testOnOmega, cmp99SourceIteratedLiftPhysicalTerminalDist] using hG

end
end YangMills.RG

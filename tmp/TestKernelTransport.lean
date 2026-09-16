import YangMills.RG.BalabanCMP99SourceEq395PhysicalDistanceDecay

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe u v w

noncomputable def testKernelTransport
    {ι ι' : Type u} {κ κ' : Type v} {g : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (hsource : ι = ι') (htarget : κ = κ')
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g) :
    FinitePiLpField ι' g →L[ℝ] FinitePiLpField κ' g := by
  subst ι'
  subst κ'
  exact T

theorem testKernelTransport_exponential
    {ι ι' : Type u} {κ κ' : Type v} {g : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (hsource : ι = ι') (htarget : κ = κ')
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) {A rate : ℝ}
    (hT : FinitePiLpTypedExponentialKernelBound T dist A rate) :
    FinitePiLpTypedExponentialKernelBound
      (testKernelTransport hsource htarget T)
      (fun target source =>
        dist (htarget.symm ▸ target) (hsource.symm ▸ source)) A rate := by
  subst ι'
  subst κ'
  simpa [testKernelTransport] using hT

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

set_option maxHeartbeats 4000000 in
noncomputable def testOnOmegaExplicit
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
  let hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega (depth + 1)
  exact testKernelTransport hsite hsite
    (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
      budget fineSmall hsmall)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem testOnOmegaExplicit_bound
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
      (testOnOmegaExplicit Omega hM depth hspacing background budget fineSmall
        hsmall)
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1)
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4) := by
  let hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega (depth + 1)
  have hG := cmp99Eq395GeneratedPhysicalMiddle_physicalDist_exponentialKernelBound
    Omega hM depth hspacing background budget fineSmall hsmall
  have htransport := testKernelTransport_exponential hsite hsite
    (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
      budget fineSmall hsmall)
    (cmp99SourceIteratedLiftPhysicalTerminalDist
      (M := M) Omega (depth + 1)) hG
  simpa [testOnOmegaExplicit, cmp99SourceIteratedLiftPhysicalTerminalDist,
    hsite] using htransport

end
end YangMills.RG

import YangMills.RG.BalabanCMP99SourceGeneratedTerminalRepresentativeDistance

/-!
# Physical-distance decay of the CMP99 equation (3.95) global middle

The generated Combes--Thomas estimate is initially expressed using the fine
representatives of terminal sites.  Their exact metric scaling now converts
that theorem into a bound in the original physical coarse metric, with no
metric-renaming hypothesis and no volume-dependent comparison constant.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

/-- The coordinate-exposed generated middle, now metrized by the original
physical coarse sites rather than their fine terminal representatives. -/
noncomputable def cmp99Eq395GeneratedPhysicalMiddlePhysicalDistKernelData
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) : CMP99Eq395TypedKernelData Nc := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  exact {
    source := regions.terminalSite
    target := regions.terminalSite
    operator := cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing
      background budget fineSmall hsmall
    dist := cmp99SourceIteratedLiftPhysicalTerminalDist
      (M := M) Omega (depth + 1)
  }

set_option maxHeartbeats 4000000 in
/-- The global middle has the generated fixed-rate decay in the literal
physical coarse metric.  The fine distance is larger by the exact positive
factor `M ^ (depth + 1)`, so weakening to the physical metric costs nothing
in amplitude or rate. -/
theorem cmp99Eq395GeneratedPhysicalMiddle_physicalDist_exponentialKernelBound
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedExponentialKernelBound
      (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing
        background budget fineSmall hsmall)
      (cmp99SourceIteratedLiftPhysicalTerminalDist
        (M := M) Omega (depth + 1))
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 4) := by
  have hgenerated := cmp99Eq395GeneratedPhysicalMiddle_exponentialKernelBound
    Omega hM depth hspacing background budget fineSmall hsmall
  exact finitePiLpTypedExponentialKernelBound_mono_dist
    (cmp99SourceIteratedLiftPhysicalTerminalDist_le_representative
      (M := M) Omega (depth + 1)) hgenerated

end

end YangMills.RG

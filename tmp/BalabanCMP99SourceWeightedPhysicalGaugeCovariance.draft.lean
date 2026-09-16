import YangMills.RG.BalabanCMP99BlockContour
import YangMills.RG.BalabanCMP99RegionalGaugeIsometry
import YangMills.RG.BalabanCMP99SourceWeightedPhysicalTower

/-!
PRE-VALIDATION: source is present only in scratch; no `.olean` has been
materialized and the theorem below is not compiler-verified.

# Gauge covariance of the exact source-weighted CMP99 average

This is C6c.8c5.  It specializes the already sealed block-contour theorem to
the literal `M^{-d}` source coefficient and the exact physical transport used
by every retained-tower step.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Equation (3.32) for the exact one-step source operator.  Neither the
transport nor the intertwining equality is supplied by the caller. -/
theorem cmp99SourceTransportedBlockAverageCLM_weightedPhysicalTransport_gaugeAct
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d (M * N') (SUN Nc))
    (A : GaugeConfig d (M * N') (SUN Nc))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho
          (GaugeConfig.gaugeAct u A))
        (cmp99RegionalFineGaugeAct Omega rho u phi) =
      cmp99RegionalCoarseGaugeAct Omega rho u
        (cmp99SourceTransportedBlockAverageCLM Omega
          (cmp99SourceWeightedPhysicalTransport rho A) phi) := by
  change
    cmp99AdjointBlockAverageCLM Omega
        (cmp99SourceBlockAverageWeight M d) rho
        (cmp99ContourHolonomy
          (cmp99BlockContainedContourSystem (G := SUN Nc))
          (GaugeConfig.gaugeAct u A))
        (cmp99RegionalFineGaugeAct Omega rho u phi) =
      cmp99RegionalCoarseGaugeAct Omega rho u
        (cmp99AdjointBlockAverageCLM Omega
          (cmp99SourceBlockAverageWeight M d) rho
          (cmp99ContourHolonomy
            (cmp99BlockContainedContourSystem (G := SUN Nc)) A) phi)
  exact cmp99AdjointBlockAverageCLM_blockContainedContour_gaugeAct
    Omega (cmp99SourceBlockAverageWeight M d) rho u A phi

/-- Operator form of the exact one-step covariance, used by the private
retained-pair recursion. -/
theorem cmp99SourceTransportedBlockAverageCLM_weightedPhysicalTransport_comp_gaugeIsometry
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d (M * N') (SUN Nc))
    (A : GaugeConfig d (M * N') (SUN Nc)) :
    (cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho (gaugeAct u A))).comp
        (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u :
          ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
            ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) =
      (cmp99RegionalCoarseGaugeLinearIsometryEquiv Omega rho u :
        ActiveGaugeZeroCochain
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
            (SUNLieCoord Nc) →L[ℝ]
          ActiveGaugeZeroCochain
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
            (SUNLieCoord Nc)).comp
        (cmp99SourceTransportedBlockAverageCLM Omega
          (cmp99SourceWeightedPhysicalTransport rho A)) := by
  apply ContinuousLinearMap.ext
  intro phi
  exact
    cmp99SourceTransportedBlockAverageCLM_weightedPhysicalTransport_gaugeAct
      Omega rho u A phi

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80CouplingScaledSecondJet
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCEq143SourceMetric

/-!
# The coupling-scaled CMP102 producer budget for equation (1.43)

The literal CMP102 source-metric Hessian is estimated before the physical
substitution `B ↦ g_k C B`, whereas equation (1.43) is consumed afterwards.
The order-two chain rule costs the explicit volume-uniform factor

`(|g_k| * (1 + M^3))^2`.

This file installs that factor in the producer budget itself and proves the
corresponding scalar comparison with the printed equation-(1.43) majorant.
It neither assumes a pointwise (1.43) estimate nor hides the coupling cost in
an unnamed constant.
-/

namespace YangMills.RG

noncomputable section

private abbrev CoupledEq143CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev CoupledEq143FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoupledEq143RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CoupledEq143CoarseField Q Nc →L[ℝ] CoupledEq143FineField M Q Nc

/-- The exact order-two cost of the physical CMP109 substitution. -/
noncomputable def cmp102Eq80CouplingScaledEq143Cost
    (M : ℕ) (gk : ℝ) : ℝ :=
  (|gk| * (1 + (M : ℝ) ^ 3)) ^ 2

/-- Producer budget after paying the explicit quadratic coupling cost.  This
is the existing source-metric budget with an effective source-jet bound
`sourceJetBound * couplingCost`; no domain-dependent information is added. -/
def CMP102Eq80CouplingScaledEq143ProducerBudget
    {M Q Nc n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      CoupledEq143CoarseField Q Nc →L[ℝ]
        CoupledEq143CoarseField Q Nc)
    (sourceJetBound summationRatio : ℝ)
    (layerWord : Fin n → ℕ)
    (Δ Msource : ℕ) (gk kappa1 C3 epsilon1 C2 : ℝ) : Prop :=
  CMP102Eq80Eq143ProducerBudget
    (M := M) baseCoarseCovariance
    (sourceJetBound * cmp102Eq80CouplingScaledEq143Cost M gk)
    summationRatio layerWord Δ Msource kappa1 C3 epsilon1 C2

/-- The raw CMP102 source-metric majorant, multiplied by the exact physical
coupling cost, is bounded by the printed equation-(1.43) majorant. -/
theorem
    cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant_mul_couplingCost_le_eq143
    {M Q Nc n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      CoupledEq143CoarseField Q Nc →L[ℝ]
        CoupledEq143CoarseField Q Nc)
    (sourceJetBound summationRatio : ℝ)
    (layerWord : Fin n → ℕ)
    (Y : CMP116LocalizationDomain M (2 * Q))
    (Δ Msource : ℕ) (gk kappa1 C3 epsilon1 C2 : ℝ)
    (hbudget : CMP102Eq80CouplingScaledEq143ProducerBudget
      (M := M) baseCoarseCovariance sourceJetBound summationRatio
      layerWord Δ Msource gk kappa1 C3 epsilon1 C2) :
    cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant
        baseCoarseCovariance sourceJetBound
        (cmp102Eq80Eq143CardRate Msource kappa1)
        (cmp102Eq80Eq143MetricRate kappa1)
        summationRatio layerWord Y Δ *
      cmp102Eq80CouplingScaledEq143Cost M gk ≤
        cmp116Eq143QMajorant C3 epsilon1 Msource C2 kappa1
          (cmp116CubeEdgeTreeMetric Y : ℝ) Y.blocks.card := by
  have h :=
    cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant_le_eq143
      (M := M) baseCoarseCovariance
      (sourceJetBound * cmp102Eq80CouplingScaledEq143Cost M gk)
      summationRatio layerWord Y Δ Msource kappa1 C3 epsilon1 C2 hbudget
  convert h using 1
  unfold cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant
  ring

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Physical direct-sector producer for the Hessian premise of equation
(1.43).  The source Hessian bound is derived from the literal CMP102 jets and
walk ratios, transported through `g_k C`, and compared with the printed
majorant through the coupled producer budget. -/
theorem
    abs_cmp116FDerivHessian_cmp102Eq80CouplingScaledPhysicalDomainFTC_le_eq143
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : CoupledEq143FineField M Q Nc →L[ℝ]
      CoupledEq143FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoupledEq143CoarseField Q Nc →L[ℝ]
        CoupledEq143CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts : Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmallContour :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CoupledEq143FineField M Q Nc →
      CoupledEq143CoarseField Q Nc)
    (V₀ : CoupledEq143FineField M Q Nc → ℝ)
    (P T : CoupledEq143RectangularFieldMap M Q Nc)
    (Δπ : CoupledEq143FineField M Q Nc →L[ℝ]
      CoupledEq143FineField M Q Nc)
    (J : CoupledEq143FineField M Q Nc)
    (Y : CMP116LocalizationDomain M (2 * Q))
    (gk : ℝ) (B A A' : CoupledEq143FineField M Q Nc)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (C Rjet sourceJetBound : ℝ)
    (hsourceJetBound0 : 0 ≤ sourceJetBound)
    (hC : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ i, i ≤ 3 →
      ‖iteratedFDeriv ℝ i V₀
        (cmp102Eq80JointRemainderInner D
          (P + t • T,
            cmp109ConstrainedLinearFluctuation (L := M) gk B))‖ ≤ C)
    (hRjet : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ i,
      1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i
          (fun q : CoupledEq143RectangularFieldMap M Q Nc ×
              CoupledEq143FineField M Q Nc => q.2)
          (P + t • T,
            cmp109ConstrainedLinearFluctuation (L := M) gk B)‖ +
        cmp102Eq80JointEvaluationJetMajorant D i
          (P + t • T,
            cmp109ConstrainedLinearFluctuation (L := M) gk B) ≤
          Rjet ^ i)
    (hsourceJet : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J 3
          (P + t • T,
            cmp109ConstrainedLinearFluctuation (L := M) gk B)
          C Rjet ≤ sourceJetBound)
    {cardRatio metricRatio summationRatio : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (Msource : ℕ) (kappa1 C3 epsilon1 C2 : ℝ)
    (hcardRate : 0 ≤ cmp102Eq80Eq143CardRate Msource kappa1)
    (hmetricRate : 0 ≤ cmp102Eq80Eq143MetricRate kappa1)
    (hcardDecay :
      cardRatio ≤ Real.exp
        (-(cmp102Eq80Eq143CardRate Msource kappa1 * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp
        (-(cmp102Eq80Eq143MetricRate kappa1 * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (hbudget : CMP102Eq80CouplingScaledEq143ProducerBudget
      (M := M) baseCoarseCovariance sourceJetBound summationRatio
      layerWord Δ Msource gk kappa1 C3 epsilon1 C2) :
    |cmp116FDerivHessian
        (cmp102Eq80CouplingScaledPotential gk (fun X =>
          cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ V₀ P T Δπ J X Y.blocks))
        B A' A| ≤
      cmp116Eq143QMajorant C3 epsilon1 Msource C2 kappa1
        (cmp116CubeEdgeTreeMetric Y : ℝ) Y.blocks.card * ‖A‖ * ‖A'‖ := by
  let f : CoupledEq143FineField M Q Nc → ℝ := fun X =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ V₀ P T Δπ J X Y.blocks
  let L := cmp109ConstrainedLinearFluctuationCLM
    (M := M) (Q := Q) (Nc := Nc) gk
  let sourceMajorant :=
    cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant
      baseCoarseCovariance sourceJetBound
      (cmp102Eq80Eq143CardRate Msource kappa1)
      (cmp102Eq80Eq143MetricRate kappa1)
      summationRatio layerWord Y Δ
  have hf : ContDiff ℝ 2 f :=
    contDiff_two_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmallContour layerWord choice
      D D₃ V₀ P T Δπ J Y.blocks hD hD₃ hV₀
  have hsecond :=
    norm_cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative_le_sourceMetric
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap layerWord choice
      D D₃ V₀ P T Δπ J (L B) Y
      hD hD₃ hV₀ C Rjet sourceJetBound hsourceJetBound0
      hC hRjet hsourceJet
      hcardRatio0 hmetricRatio0 hsummation0 hcardRate hmetricRate
      hsplit hcardDecay hmetricDecay hsmall
  have hHessian : ‖cmp116FDerivHessian f (L B)‖ ≤ sourceMajorant := by
    rw [cmp116FDerivHessian_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmallContour layerWord choice
      D D₃ V₀ P T Δπ J (L B) Y.blocks hD hD₃ hV₀]
    simpa [sourceMajorant, L] using hsecond
  have hscaled :=
    abs_cmp116FDerivHessian_cmp102Eq80CouplingScaledPotential_le_explicit_of_hessian
      gk f hf B A A' sourceMajorant hHessian
  have hmajorant :=
    cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant_mul_couplingCost_le_eq143
      (M := M) baseCoarseCovariance sourceJetBound summationRatio
      layerWord Y Δ Msource gk kappa1 C3 epsilon1 C2 hbudget
  calc
    |cmp116FDerivHessian
        (cmp102Eq80CouplingScaledPotential gk f) B A' A| ≤
      sourceMajorant * cmp102Eq80CouplingScaledEq143Cost M gk * ‖A‖ * ‖A'‖ := by
        simpa [sourceMajorant, cmp102Eq80CouplingScaledEq143Cost] using hscaled
    _ ≤ cmp116Eq143QMajorant C3 epsilon1 Msource C2 kappa1
          (cmp116CubeEdgeTreeMetric Y : ℝ) Y.blocks.card * ‖A‖ * ‖A'‖ := by
      gcongr
    _ = _ := by rfl

end

end YangMills.RG

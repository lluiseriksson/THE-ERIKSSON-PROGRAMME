/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCThirdFieldDerivative
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainThirdFieldSourceMetricBound

/-!
# Source-metric third-jet bound for the literal CMP102 domain FTC potential

The coefficient-level source-metric estimate is transported through the
literal affine FTC integral. The resulting theorem bounds the third
derivative of the actual equation-(80) domain potential, not merely one
reconstructed coefficient.

The uniform source factor concerns only the explicit order-four component
jet along the affine propagator segment. Every dependence on the domain
`Y` remains in the physical random-walk source-metric prefactor.
-/

open MeasureTheory Set
open scoped Interval Matrix.Norms.Operator RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev MetricFineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev MetricCoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev MetricRectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  MetricCoarseField Q Nc →L[ℝ] MetricFineField M Q Nc

/-- Explicit majorant for the third derivative of the complete literal
domain FTC potential. The source factor is uniform on the affine segment;
the remaining factor is the exact source-metric decay in `Y`. -/
noncomputable def
    cmp102Eq80PhysicalDomainFTCThirdFieldSourceMetricMajorant
    {M Q Nc n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      MetricCoarseField Q Nc →L[ℝ] MetricCoarseField Q Nc)
    (sourceJetBound κcard κmetric summationRatio : ℝ)
    (layerWord : Fin n → ℕ)
    (Y : CMP116LocalizationDomain M (2 * Q))
    (Δ : ℕ) : ℝ :=
  sourceJetBound *
    (ContinuousLinearMap.opNorm (𝕜 := ℝ)
      (cmp99PhysicalRectangularOfComplexMatrixContinuousLinearMap
        (d := 4) (N₁ := 2 * Q) (N₂ := M * (2 * Q)) (Nc := Nc)) *
      (cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
          baseCoarseCovariance κcard κmetric summationRatio layerWord Y *
        (1 -
          ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio)⁻¹))

/-- The third derivative of the literal CMP102 domain FTC potential
inherits the coefficient source-metric decay without loss from the
unit-length FTC interval. -/
theorem
    norm_iteratedFDeriv_three_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_le_sourceMetric
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : MetricFineField M Q Nc →L[ℝ] MetricFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      MetricCoarseField Q Nc →L[ℝ] MetricCoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
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
    (D D₃ : MetricFineField M Q Nc → MetricCoarseField Q Nc)
    (V₀ : MetricFineField M Q Nc → ℝ)
    (P T : MetricRectangularFieldMap M Q Nc)
    (Δπ : MetricFineField M Q Nc →L[ℝ] MetricFineField M Q Nc)
    (J A : MetricFineField M Q Nc)
    (Y : CMP116LocalizationDomain M (2 * Q))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (C Rjet sourceJetBound : ℝ)
    (hC : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ i, i ≤ 4 →
      ‖iteratedFDeriv ℝ i V₀
        (cmp102Eq80JointRemainderInner D (P + t • T, A))‖ ≤ C)
    (hRjet : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ i,
      1 ≤ i → i ≤ 4 →
      ‖iteratedFDeriv ℝ i
          (fun q :
              MetricRectangularFieldMap M Q Nc ×
                MetricFineField M Q Nc => q.2)
          (P + t • T, A)‖ +
        cmp102Eq80JointEvaluationJetMajorant D i
          (P + t • T, A) ≤ Rjet ^ i)
    (hsourceJet : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      max
        (cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J 4 (P + t • T, A) C Rjet) 0 ≤
        sourceJetBound)
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 ≤ κcard)
    (hκmetric : 0 ≤ κmetric)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1) :
    ‖iteratedFDeriv ℝ 3
        (fun X =>
          cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ V₀ P T Δπ J X Y.blocks)
        A‖ ≤
      cmp102Eq80PhysicalDomainFTCThirdFieldSourceMetricMajorant
        baseCoarseCovariance sourceJetBound κcard κmetric
        summationRatio layerWord Y Δ := by
  let Φ :
      MetricRectangularFieldMap M Q Nc ×
        MetricFineField M Q Nc → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  let Kdomain :=
    cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y.blocks)
  let decayFactor : ℝ :=
    ContinuousLinearMap.opNorm (𝕜 := ℝ)
        (cmp99PhysicalRectangularOfComplexMatrixContinuousLinearMap
          (d := 4) (N₁ := 2 * Q)
          (N₂ := M * (2 * Q)) (Nc := Nc)) *
      (cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
          baseCoarseCovariance κcard κmetric summationRatio layerWord Y *
        (1 -
          ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio)⁻¹)
  have hΦ : ContDiff ℝ ⊤ Φ :=
    contDiff_cmp102Eq80JointPotential_rectangular
      D D₃ V₀ Δπ J hD hD₃ hV₀
  have hdecayFactor0 : 0 ≤ decayFactor := by
    have hprefactor :
        0 ≤ cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
          baseCoarseCovariance κcard κmetric
          summationRatio layerWord Y := by
      unfold
        cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
        cmp102Eq80PhysicalFineHeadTailEndpointMajorant
      positivity
    have hinv :
        0 ≤ (1 -
          ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio)⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr hsmall.le)
    exact mul_nonneg
      (ContinuousLinearMap.opNorm_nonneg _)
      (mul_nonneg hprefactor hinv)
  have hinterior : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 3
        (cmp102PartialPropagatorJet
          Φ 1 (P + t • T) (fun _ => Kdomain)) A‖ ≤
        sourceJetBound * decayFactor := by
    intro t ht
    have hcoefficient :=
      norm_iteratedFDeriv_three_cmp102Eq80PhysicalFineHeadTailDomainCoefficient_le_sourceMetric
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmallContour layerWord choice
        D D₃ V₀ (P + t • T) Δπ J A Y
        hD hD₃ hV₀ C Rjet (hC t ht) (hRjet t ht)
        hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
        hsplit hcardDecay hmetricDecay hsmall
    have hsource := hsourceJet t ht
    have hcoefficientFunction :
        cmp102PartialPropagatorJet
            Φ 1 (P + t • T) (fun _ => Kdomain) =
          fun X =>
            cmp102Eq80PhysicalFineHeadTailDomainCoefficient
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice D D₃ (P + t • T) Δπ J X
              (fderiv ℝ V₀ (X - (P + t • T) (D X))) Y.blocks := by
      funext X
      simpa [Φ, Kdomain] using
        (cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_partialPropagatorJet
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          sigma hRweak hcap hsmallContour layerWord choice
          D D₃ V₀ (P + t • T) Δπ J X Y.blocks
          hD hD₃ hV₀).symm
    calc
      ‖iteratedFDeriv ℝ 3
          (cmp102PartialPropagatorJet
            Φ 1 (P + t • T) (fun _ => Kdomain)) A‖ =
        ‖iteratedFDeriv ℝ 3
          (fun X =>
            cmp102Eq80PhysicalFineHeadTailDomainCoefficient
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice D D₃ (P + t • T) Δπ J X
              (fderiv ℝ V₀ (X - (P + t • T) (D X))) Y.blocks)
          A‖ := by rw [hcoefficientFunction]
      _ ≤
        cmp102Eq80PhysicalDomainThirdFieldSourceMetricMajorant
          D D₃ (P + t • T) Δπ J A C Rjet
          baseCoarseCovariance κcard κmetric
          summationRatio layerWord Y Δ := hcoefficient
      _ ≤ sourceJetBound * decayFactor := by
        exact mul_le_mul_of_nonneg_right hsource hdecayFactor0
  have hFTC :=
    norm_cmp102AffinePropagatorJetFTCThirdFieldDerivative_le
      Φ hΦ 1 P T (fun _ => Kdomain) A
      (sourceJetBound * decayFactor) hinterior
  have hnorm :
      ‖iteratedFDeriv ℝ 3
          (cmp102AffinePropagatorJetFTC
            Φ 1 P T (fun _ => Kdomain)) A‖ ≤
        sourceJetBound * decayFactor := by
    rw [
      norm_iteratedFDeriv_three_cmp102AffinePropagatorJetFTC_eq
        Φ hΦ 1 P T (fun _ => Kdomain) A]
    exact hFTC
  have hfun :
      (fun X =>
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J X Y.blocks) =
        cmp102AffinePropagatorJetFTC
          Φ 1 P T (fun _ => Kdomain) := by
    funext X
    simpa [Φ, Kdomain] using
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_eq_affinePropagatorJetFTC
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmallContour layerWord choice
        D D₃ V₀ P T Δπ J X Y.blocks hD hD₃ hV₀
  rw [hfun]
  simpa [
    cmp102Eq80PhysicalDomainFTCThirdFieldSourceMetricMajorant,
    decayFactor, mul_assoc] using hnorm

end

end YangMills.RG

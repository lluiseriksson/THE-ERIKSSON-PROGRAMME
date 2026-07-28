/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCEq143Frontier
import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailSourceMetricDecay

/-!
# Source-metric bound for the literal CMP102 domain Hessian

The literal domain Hessian is an interval integral of the second field
derivative of the reconstructed domain coefficient.  This module transports
the existing order-three source-jet estimate through that interval integral
and then consumes the existing cardinality/tree-metric decay of the domain
matrix coefficient.

The resulting majorant is explicit in the producer-side quantities.  No
equation-(1.43) estimate is assumed.  Matching this explicit expression to
the printed constants `C3`, `epsilon1`, `kappa1`, and `C2` remains a scalar
source-constant obligation.
-/

open MeasureTheory Set
open scoped Interval RealInnerProductSpace Matrix.Norms.Operator

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

/-- A uniform bound on the literal coefficient second derivative passes
through its affine FTC integral without loss, because the integration
interval has length one. -/
theorem norm_cmp102AffinePropagatorJetFTCSecondFieldDerivative_le
    {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (F : H × E → ℝ) (n : ℕ) (P T : H)
    (v : Fin n → H) (x : E) (C : ℝ)
    (hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖cmp102PartialPropagatorJetSecondFieldDerivative
          F n (P + t • T) v x‖ ≤ C) :
    ‖cmp102AffinePropagatorJetFTCSecondFieldDerivative
        F n P T v x‖ ≤ C := by
  unfold cmp102AffinePropagatorJetFTCSecondFieldDerivative
  have hconst :
      IntervalIntegrable (fun _t : ℝ => C) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hnorm :
      ‖∫ t in (0 : ℝ)..1,
          cmp102PartialPropagatorJetSecondFieldDerivative
            F n (P + t • T) v x‖ ≤
        ∫ _t in (0 : ℝ)..1, C := by
    apply intervalIntegral.norm_integral_le_of_norm_le
      (by norm_num : (0 : ℝ) ≤ 1)
      (Filter.Eventually.of_forall ?_) hconst
    intro t ht
    exact hbound t (by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)
  simpa using hnorm

/-- Explicit producer-side majorant for the complete literal domain
Hessian.  It is the uniform source-jet bound, the norm of the physical
rectangular reconstruction map, and the exact source-metric domain
coefficient majorant. -/
noncomputable def
    cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant
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
    ContinuousLinearMap.opNorm (𝕜 := ℝ)
      (cmp99PhysicalRectangularOfComplexMatrixContinuousLinearMap
        (d := 4) (N₁ := 2 * Q) (N₂ := M * (2 * Q)) (Nc := Nc)) *
    cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
      baseCoarseCovariance κcard κmetric summationRatio layerWord Y *
    (1 -
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio)⁻¹

/-- The full literal CMP102 domain Hessian is bounded by the explicit
source-jet/source-metric majorant.  The hypotheses concern only the
producer-side jets and the already reconstructed walk ratios. -/
theorem
    norm_cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative_le_sourceMetric
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
    (hsourceJetBound0 : 0 ≤ sourceJetBound)
    (hC : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ i, i ≤ 3 →
      ‖iteratedFDeriv ℝ i V₀
        (cmp102Eq80JointRemainderInner D (P + t • T, A))‖ ≤ C)
    (hRjet : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ i,
      1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i
          (fun q :
              MetricRectangularFieldMap M Q Nc × MetricFineField M Q Nc => q.2)
          (P + t • T, A)‖ +
        cmp102Eq80JointEvaluationJetMajorant D i (P + t • T, A) ≤
          Rjet ^ i)
    (hsourceJet : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J 3 (P + t • T, A) C Rjet ≤ sourceJetBound)
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
    ‖cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J A Y.blocks‖ ≤
      cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant
        baseCoarseCovariance sourceJetBound κcard κmetric
        summationRatio layerWord Y Δ := by
  let L :=
    cmp99PhysicalRectangularOfComplexMatrixContinuousLinearMap
      (d := 4) (N₁ := 2 * Q) (N₂ := M * (2 * Q)) (Nc := Nc)
  let matrixCoefficient :=
    cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice Y.blocks
  have hmatrix :
      ‖matrixCoefficient‖ ≤
        cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
            baseCoarseCovariance κcard κmetric summationRatio layerWord Y *
          (1 -
            ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
              summationRatio)⁻¹ := by
    simpa [matrixCoefficient] using
      norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient_le_sourceMetricDecay
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap layerWord choice Y
        hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
        hsplit hcardDecay hmetricDecay hsmall
  have hL0 : 0 ≤ ContinuousLinearMap.opNorm L :=
    ContinuousLinearMap.opNorm_nonneg L
  have hmatrixReconstruct :
      ‖cmp99PhysicalRectangularOfComplexMatrix matrixCoefficient‖ ≤
        ContinuousLinearMap.opNorm L *
          (cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
              baseCoarseCovariance κcard κmetric summationRatio layerWord Y *
            (1 -
              ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
                summationRatio)⁻¹) := by
    calc
      ‖cmp99PhysicalRectangularOfComplexMatrix matrixCoefficient‖ ≤
          ContinuousLinearMap.opNorm L * ‖matrixCoefficient‖ := by
        simpa [L] using L.le_opNorm matrixCoefficient
      _ ≤ ContinuousLinearMap.opNorm L *
          (cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
              baseCoarseCovariance κcard κmetric summationRatio layerWord Y *
            (1 -
              ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
                summationRatio)⁻¹) :=
        mul_le_mul_of_nonneg_left hmatrix hL0
  let Φ :
      MetricRectangularFieldMap M Q Nc × MetricFineField M Q Nc → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  have hinterior : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖cmp102PartialPropagatorJetSecondFieldDerivative
          Φ 1 (P + t • T)
          (fun _ => cmp99PhysicalRectangularOfComplexMatrix matrixCoefficient)
          A‖ ≤
        sourceJetBound *
          (ContinuousLinearMap.opNorm L *
            (cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
                baseCoarseCovariance κcard κmetric summationRatio layerWord Y *
              (1 -
                ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
                  summationRatio)⁻¹)) := by
    intro t ht
    have hcoefficient :=
      norm_cmp102Eq80PhysicalFineHeadTailDomainCoefficientSecondFieldDerivative_le_sourceJets
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ (P + t • T) Δπ J A Y.blocks
        hD hD₃ hV₀ C Rjet (hC t ht) (hRjet t ht)
    have hjet := hsourceJet t ht
    calc
      ‖cmp102PartialPropagatorJetSecondFieldDerivative
          Φ 1 (P + t • T)
          (fun _ => cmp99PhysicalRectangularOfComplexMatrix matrixCoefficient)
          A‖ =
        ‖cmp102Eq80PhysicalFineHeadTailDomainCoefficientSecondFieldDerivative
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ (P + t • T) Δπ J A
          Y.blocks‖ := by
            rfl
      _ ≤
        cmp102Eq80JointPotentialSourceJetMajorant
            D D₃ Δπ J 3 (P + t • T, A) C Rjet *
          ‖cmp99PhysicalRectangularOfComplexMatrix matrixCoefficient‖ :=
        hcoefficient
      _ ≤ sourceJetBound *
          ‖cmp99PhysicalRectangularOfComplexMatrix matrixCoefficient‖ :=
        mul_le_mul_of_nonneg_right hjet
          (norm_nonneg
            (cmp99PhysicalRectangularOfComplexMatrix matrixCoefficient))
      _ ≤ sourceJetBound *
          (ContinuousLinearMap.opNorm L *
            (cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
                baseCoarseCovariance κcard κmetric summationRatio layerWord Y *
              (1 -
                ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
                  summationRatio)⁻¹)) :=
        mul_le_mul_of_nonneg_left hmatrixReconstruct hsourceJetBound0
  have hFTC :=
    norm_cmp102AffinePropagatorJetFTCSecondFieldDerivative_le
      Φ 1 P T
      (fun _ => cmp99PhysicalRectangularOfComplexMatrix matrixCoefficient)
      A
      (sourceJetBound *
        (ContinuousLinearMap.opNorm L *
          (cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
              baseCoarseCovariance κcard κmetric summationRatio layerWord Y *
            (1 -
              ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
                summationRatio)⁻¹)))
      hinterior
  simpa [
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative,
    cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant,
    Φ, L, matrixCoefficient, mul_assoc] using hFTC

end

end YangMills.RG

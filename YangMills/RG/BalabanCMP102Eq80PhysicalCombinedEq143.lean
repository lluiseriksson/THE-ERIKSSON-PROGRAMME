/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalIndexedEq143
import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedQuadraticCore
import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedDomainDictionary

/-!
# Physical equation (1.43) on the combined direct/native ledger

The direct indexed equation-(80) core now has a source-derived physical
equation-(1.43) bound.  The existing combined compositor proves that the
native Lemma-1 core is identically zero.  This file joins those two results
using the canonical combined metric and cardinality dictionaries.

No native Hessian estimate and no free pointwise equation-(1.43) hypothesis
is accepted.
-/

namespace YangMills.RG

noncomputable section

private abbrev CombinedEq143FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CombinedEq143CoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev CombinedEq143RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CombinedEq143CoarseField Q Nc →L[ℝ]
    CombinedEq143FineField M Q Nc

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 180000 in
/-- Equation (1.43) for every index of the canonical direct/native ledger.
The direct branch is produced from the literal CMP102 jets and walks; the
native branch is discharged by exact cancellation in the quadratic core. -/
theorem abs_cmp116FDerivHessian_cmp116Eq80Lemma1CombinedPhysical_le_eq143
    {Index : Type*} {nDelta M Q Nc R Delta n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (nativeResidual : Fin (CMP109Lemma1NativeDomainCount E) →
      CombinedEq143FineField M Q Nc → ℝ)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (deltaRadius : Fin nDelta → ℝ)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hradiusCap : ∀ j, 1 + deltaRadius j ≤ radius)
    (K : CombinedEq143FineField M Q Nc →L[ℝ]
      CombinedEq143FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedEq143CoarseField Q Nc →L[ℝ]
        CombinedEq143CoarseField Q Nc)
    {Ahead rho rate : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts : Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (sigma : Fin nDelta → ℂ)
    (hsigma : CMP116Eq214ShiftedPolydisc nDelta deltaRadius sigma)
    (hsmallContour :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho (1 + radius)‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CombinedEq143FineField M Q Nc →
      CombinedEq143CoarseField Q Nc)
    (V₀ : CombinedEq143FineField M Q Nc → ℝ)
    (Pprop T : CombinedEq143RectangularFieldMap M Q Nc)
    (DeltaPi : CombinedEq143FineField M Q Nc →L[ℝ]
      CombinedEq143FineField M Q Nc)
    (J : CombinedEq143FineField M Q Nc)
    (gk : ℝ)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (C Rjet sourceJetBound : ℝ)
    (hsourceJetBound0 : 0 ≤ sourceJetBound)
    (hC : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j, j ≤ 3 →
      ‖iteratedFDeriv ℝ j V₀
        (cmp102Eq80JointRemainderInner D
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk (0 : CombinedEq143FineField M Q Nc)))‖ ≤ C)
    (hRjet : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j,
      1 ≤ j → j ≤ 3 →
      ‖iteratedFDeriv ℝ j
          (fun q : CombinedEq143RectangularFieldMap M Q Nc ×
              CombinedEq143FineField M Q Nc => q.2)
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk (0 : CombinedEq143FineField M Q Nc))‖ +
        cmp102Eq80JointEvaluationJetMajorant D j
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk (0 : CombinedEq143FineField M Q Nc)) ≤
          Rjet ^ j)
    (hsourceJet : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ DeltaPi J 3
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk (0 : CombinedEq143FineField M Q Nc))
          C Rjet ≤ sourceJetBound)
    {cardRatio metricRatio summationRatio : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate (1 + radius) ≤
        cardRatio * (metricRatio * summationRatio))
    (kappa1 C3 epsilon1 C2 : ℝ)
    (hamplitude : 0 ≤ C3 * epsilon1)
    (hcardRate : 0 ≤ cmp102Eq80Eq143CardRate M kappa1)
    (hmetricRate : 0 ≤ cmp102Eq80Eq143MetricRate kappa1)
    (hcardDecay :
      cardRatio ≤ Real.exp
        (-(cmp102Eq80Eq143CardRate M kappa1 * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp
        (-(cmp102Eq80Eq143MetricRate kappa1 * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Delta : ℕ) : ℝ) *
        summationRatio < 1)
    (hbudget : CMP102Eq80CouplingScaledEq143ProducerBudget
      (M := M) baseCoarseCovariance sourceJetBound summationRatio
      layerWord Delta M gk kappa1 C3 epsilon1 C2) :
    ∀ (y : Fin (CMP116Eq80Lemma1CombinedDomainCount anchor domains E))
      (B A A' : CombinedEq143FineField M Q Nc) (s : ℝ),
      |cmp116FDerivHessian
        (cmp116Eq142PhysicalQuadraticCore
          (cmp116Eq80Lemma1CombinedTotal
            (cmp102Eq80PhysicalIndexedContourTotal
              anchor domains contourCarrier e K hc hmass hK
              baseCoarseCovariance sigma layerWord choice
              D D₃ V₀ Pprop T DeltaPi J gk)
            nativeResidual)
          (cmp116Eq80Lemma1CombinedResidual
            (fun i =>
              cmp102Eq80PhysicalIndexedContourResidual
                anchor domains contourCarrier e i K hc hmass hK
                baseCoarseCovariance sigma layerWord choice
                D D₃ V₀ Pprop T DeltaPi J gk)
            nativeResidual) y)
        (s • B) A' A| ≤
          cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
            (cmp116Eq80Lemma1CombinedDomainMetric anchor domains E y : ℝ)
            (cmp116Eq80Lemma1CombinedDomainCard anchor domains E y) *
              ‖A‖ * ‖A'‖ := by
  apply abs_cmp116FDerivHessian_combined_le_eq143
    (cmp102Eq80PhysicalIndexedContourTotal
      anchor domains contourCarrier e K hc hmass hK
      baseCoarseCovariance sigma layerWord choice
      D D₃ V₀ Pprop T DeltaPi J gk)
    (fun i =>
      cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T DeltaPi J gk)
    nativeResidual
    (cmp116Eq80Lemma1CombinedDomainMetric anchor domains E)
    (cmp116Eq80Lemma1CombinedDomainCard anchor domains E)
    C3 epsilon1 C2 kappa1 M hamplitude
  intro i B A A' s
  simpa [cmp102Eq80SourcePi4IndexedDomainMetricNat,
    cmp102Eq80SourcePi4IndexedDomainCard] using
    (abs_cmp116FDerivHessian_cmp116Eq142PhysicalQuadraticCore_indexedContour_le_eq143
      anchor domains contourCarrier e deltaRadius radius hradius hradiusCap
      i K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hDelta hDelta1
      sigma hsigma hsmallContour layerWord choice D D₃ V₀ Pprop T DeltaPi J
      gk hD hD₃ hV₀ C Rjet sourceJetBound hsourceJetBound0
      hC hRjet hsourceJet hcardRatio0 hmetricRatio0 hsummation0 hsplit
      M kappa1 C3 epsilon1 C2 hamplitude hcardRate hmetricRate
      hcardDecay hmetricDecay hsmall hbudget B A A' s)

end

end YangMills.RG

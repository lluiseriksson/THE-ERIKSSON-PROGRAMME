/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalContourEq136Residual
import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedCutoffCarrier
import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedDomainDictionary
import YangMills.RG.BalabanCMP116Eq80Lemma1CombinedQuadraticCore

/-!
# Cutoff-supported physical equation (1.36) on the combined ledger

The direct equation-(80) residual already satisfies the printed estimate
(1.36).  The sole remaining analytic input is the source-pinned CMP109
Lemma-1 certificate.  This file installs both on the disjoint terminal
domain ledger.

The terminal small-field carrier is the complete bilateral interior of the
combined centered region.  This is essential: the native residual evaluates
the global correction `D(P_Z0 B)`, so it cannot be localized to a single
native domain.  It is also a stronger small-field restriction than the
individual-domain region printed in (1.34).  The result below is therefore
the exact cutoff-supported form consumed by the terminal record, not a claim
that the source estimate has been enlarged to every field in each individual
domain region.  Nonvanishing of the common cutoff restricts to the smaller
direct carrier for the equation-(80) producer.

The combined normalization is exactly `E0Direct + lemma1.E0`; no pointwise
equation-(1.36) premise and no arbitrary reindexing map is accepted.
-/

namespace YangMills.RG

noncomputable section

private abbrev CombinedEq136FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CombinedEq136CoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev CombinedEq136RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CombinedEq136CoarseField Q Nc →L[ℝ]
    CombinedEq136FineField M Q Nc

/-- Canonically indexed literal CMP109 Lemma-1 residual. -/
noncomputable def cmp109Lemma1IndexedSourceResidual
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] [NeZero Nc]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (gk : ℝ)
    (D : CombinedEq136FineField M Q Nc →
      CombinedEq136CoarseField Q Nc) :
    Fin (CMP109Lemma1NativeDomainCount E) →
      CombinedEq136FineField M Q Nc → ℝ :=
  fun i B =>
    cmp109Lemma1SourceResidual E V gk D
      (cmp109Lemma1NativeDomainAt E i) B

/-- The direct contour residual is unchanged by the terminal projection to
the larger combined centered region. -/
theorem cmp102Eq80PhysicalIndexedContourResidual_combinedCenteredRegion
    {Index : Type*} {nDelta M Q Nc R n L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (K : CombinedEq136FineField M Q Nc →L[ℝ]
      CombinedEq136FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedEq136CoarseField Q Nc →L[ℝ]
        CombinedEq136CoarseField Q Nc)
    (sigma : Fin nDelta → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CombinedEq136FineField M Q Nc →
      CombinedEq136CoarseField Q Nc)
    (V₀ : CombinedEq136FineField M Q Nc → ℝ)
    (Pprop T : CombinedEq136RectangularFieldMap M Q Nc)
    (DeltaPi : CombinedEq136FineField M Q Nc →L[ℝ]
      CombinedEq136FineField M Q Nc)
    (J : CombinedEq136FineField M Q Nc)
    (gk : ℝ) (B : CombinedEq136FineField M Q Nc) :
    let Z0 := cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P
    cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T DeltaPi J gk
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          B) =
      cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T DeltaPi J gk B := by
  dsimp only
  unfold cmp102Eq80PhysicalIndexedContourResidual
  simpa only using
    congrArg
      (fun X =>
        cmp102Eq80PhysicalIndexedCouplingScaledResidual
          anchor domains i K hc hmass hK baseCoarseCovariance
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
          layerWord choice D D₃ V₀ Pprop T DeltaPi J gk X)
      (physicalBondProjection_indexedSourceDomain_combinedCenteredRegion
        Dict anchor domains E P i B)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 240000 in
/-- The terminal cutoff-supported form of equation (1.36) for every domain in
the canonical direct/native ledger.  The direct bound is derived from the
literal equation-(80) third-jet chain; the native bound is exactly the single
source-pinned Lemma-1 certificate. -/
theorem abs_cmp116Eq80Lemma1CombinedPhysicalResidual_le_eq136
    {Index : Type*} {nDelta M Q Nc R Delta n L lieDim q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (deltaRadius : Fin nDelta → ℝ)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hradiusCap : ∀ j, 1 + deltaRadius j ≤ radius)
    (K : CombinedEq136FineField M Q Nc →L[ℝ]
      CombinedEq136FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedEq136CoarseField Q Nc →L[ℝ]
        CombinedEq136CoarseField Q Nc)
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
    (D D₃ : CombinedEq136FineField M Q Nc →
      CombinedEq136CoarseField Q Nc)
    (V₀ : CombinedEq136FineField M Q Nc → ℝ)
    (Pprop T : CombinedEq136RectangularFieldMap M Q Nc)
    (DeltaPi : CombinedEq136FineField M Q Nc →L[ℝ]
      CombinedEq136FineField M Q Nc)
    (J : CombinedEq136FineField M Q Nc)
    (gk epsilon1 C1 C2 kappa1 delta kappa : ℝ)
    (lemma1 : CMP109Lemma1Eq136SourceCertificate (q := q)
      E V gk D epsilon1 C1 C2 kappa1 delta kappa)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (C Rjet sourceJetBound : ℝ)
    (hsourceJetBound : 0 ≤ sourceJetBound)
    (hC : ∀ X, cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j, j ≤ 4 →
        ‖iteratedFDeriv ℝ j V₀
          (cmp102Eq80JointRemainderInner
            D (Pprop + t • T,
              cmp109ConstrainedLinearFluctuation (L := M) gk X))‖ ≤ C)
    (hRjet : ∀ X, cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j,
        1 ≤ j → j ≤ 4 →
        ‖iteratedFDeriv ℝ j
            (fun z : CombinedEq136RectangularFieldMap M Q Nc ×
                CombinedEq136FineField M Q Nc => z.2)
            (Pprop + t • T,
              cmp109ConstrainedLinearFluctuation (L := M) gk X)‖ +
          cmp102Eq80JointEvaluationJetMajorant D j
            (Pprop + t • T,
              cmp109ConstrainedLinearFluctuation (L := M) gk X) ≤
            Rjet ^ j)
    (hsourceJet : ∀ X, cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        max
          (cmp102Eq80JointPotentialSourceJetMajorant
            D D₃ DeltaPi J 4
              (Pprop + t • T,
                cmp109ConstrainedLinearFluctuation (L := M) gk X)
              C Rjet) 0 ≤ sourceJetBound)
    {cardRatio metricRatio summationRatio kappaCard : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hkappaCard : 0 < kappaCard)
    (E0Direct : ℝ) (hE0Direct : 0 ≤ E0Direct)
    (hepsilon1_one : epsilon1 ≤ 1)
    (hC1 : 0 ≤ C1)
    (hresidualRate0 :
      0 ≤ cmp102Eq80Eq136ResidualMetricRate delta kappa)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate (1 + radius) ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(kappaCard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp
        (-(cmp102Eq80Eq136ResidualMetricRate delta kappa * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Delta : ℕ) : ℝ) *
        summationRatio < 1)
    (hbudget : CMP102Eq80Eq136ThirdJetProducerBudget
      (M := M) baseCoarseCovariance sourceJetBound kappaCard
      delta kappa summationRatio layerWord Delta q E0Direct C1 C2 kappa1)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
              (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P))
            (epsilon1 / gk) (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P (epsilon1 / gk)
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0) :
    ∀ y : Fin (CMP116Eq80Lemma1CombinedDomainCount anchor domains E),
      |cmp116Eq80Lemma1CombinedResidual
          (fun i =>
            cmp102Eq80PhysicalIndexedContourResidual
              anchor domains contourCarrier e i K hc hmass hK
              baseCoarseCovariance sigma layerWord choice
              D D₃ V₀ Pprop T DeltaPi J gk)
          (cmp109Lemma1IndexedSourceResidual E V gk D) y
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
              (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P))
            (cmp116SourcePhysicalCoordinateCochain b))| ≤
        cmp116Eq136ResidualMajorant (E0Direct + lemma1.E0)
          epsilon1 C1 M q C2 kappa1 delta kappa
          (cmp116Eq80Lemma1CombinedDomainMetric anchor domains E y : ℝ) := by
  have hdirectCutoff :=
    cmp116DirectSignedCutoff_ne_zero_of_combinedInteriorCutoff
      anchor domains E P (epsilon1 / gk) b hcutoff
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · simp only [cmp116Eq80Lemma1CombinedResidual_direct,
      cmp116Eq80Lemma1CombinedDomainMetric_direct]
    rw [cmp102Eq80PhysicalIndexedContourResidual_combinedCenteredRegion
      Dict anchor domains E P contourCarrier e i K hc hmass hK
      baseCoarseCovariance sigma layerWord choice
      D D₃ V₀ Pprop T DeltaPi J gk
      (cmp116SourcePhysicalCoordinateCochain b)]
    have hdirect :=
      abs_cmp102Eq80PhysicalIndexedContourResidual_le_eq136
        anchor domains contourCarrier e deltaRadius radius hradius hradiusCap
        i P epsilon1 gk b lemma1.epsilon1_nonneg hepsilon1_one
        lemma1.gk_pos hdirectCutoff K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hDelta hDelta1
        sigma hsigma hsmallContour layerWord choice D D₃ V₀ Pprop T DeltaPi J
        hD hD₃ hV₀ C Rjet sourceJetBound hsourceJetBound hC hRjet hsourceJet
        hcardRatio0 hmetricRatio0 hsummation0 hkappaCard
        E0Direct C1 q C2 kappa1 delta kappa hresidualRate0
        hsplit hcardDecay hmetricDecay hsmall hbudget
    exact hdirect.trans
      (cmp116Eq136ResidualMajorant_mono_E0
        (le_add_of_nonneg_right (le_of_lt lemma1.E0_pos))
        lemma1.epsilon1_nonneg hC1)
  · simp only [cmp116Eq80Lemma1CombinedResidual_native,
      cmp109Lemma1IndexedSourceResidual,
      cmp116Eq80Lemma1CombinedDomainMetric_native]
    have hnativeSmall :=
      cmp109Lemma1SourceSmallField_combinedInteriorProjection_of_cutoff
        anchor domains E P epsilon1 gk lemma1.epsilon1_nonneg lemma1.gk_pos
        b hcutoff (cmp109Lemma1NativeDomainAt E i)
    exact (lemma1.bound
      (cmp109Lemma1NativeDomainAt E i)
      (physicalBondProjection
        (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
          (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P))
        (cmp116SourcePhysicalCoordinateCochain b)) hnativeSmall).trans
      (cmp116Eq136ResidualMajorant_mono_E0
        (le_add_of_nonneg_left hE0Direct)
        lemma1.epsilon1_nonneg hC1)

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116CenteredConditionedCombinedEq80PartialPotential
import YangMills.RG.BalabanCMP102Eq80PhysicalCombinedEq136

/-!
# Equation (1.36) in the terminal partial-potential signature

The combined direct/native theorem already proves equation `(1.36)` on the
literal source cutoff carrier.  This file performs only the final type-level
transport to the five-argument residual function used by the centered
conditioned equation-`(2.26)` term source.  Spectator and fluctuation fields
remain arbitrary because the installed source residual is independent of
them.

No new analytic premise, reindexing map, or extension outside the cutoff
support is introduced.
-/

namespace YangMills.RG

noncomputable section

private abbrev PartialEq136FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev PartialEq136CoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev PartialEq136RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PartialEq136CoarseField Q Nc →L[ℝ] PartialEq136FineField M Q Nc

private abbrev PartialEq136Bond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 240000 in
/-- Equation `(1.36)` for the terminal combined residual function.  The
direct estimate is generated internally by the equation-(80) third-jet
chain; the only source-facing analytic input for the native branch is the
named CMP109 Lemma-1 certificate. -/
theorem abs_cmp116CenteredConditionedCombinedEq80PartialResidual_le_eq136
    {Index : Type*} {nDelta M Q Nc R Delta n L lieDim q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (spectatorSupport fluctuationSupport : Finset (PartialEq136Bond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (P : Finset (PartialEq136Bond M Q))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (deltaRadius : Fin nDelta → ℝ)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hradiusCap : ∀ j, 1 + deltaRadius j ≤ radius)
    (K : PartialEq136FineField M Q Nc →L[ℝ]
      PartialEq136FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      PartialEq136CoarseField Q Nc →L[ℝ]
        PartialEq136CoarseField Q Nc)
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
    (D D₃ : PartialEq136FineField M Q Nc →
      PartialEq136CoarseField Q Nc)
    (V₀ : PartialEq136FineField M Q Nc → ℝ)
    (Pprop T : PartialEq136RectangularFieldMap M Q Nc)
    (DeltaPi : PartialEq136FineField M Q Nc →L[ℝ]
      PartialEq136FineField M Q Nc)
    (J : PartialEq136FineField M Q Nc)
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
            (fun z : PartialEq136RectangularFieldMap M Q Nc ×
                PartialEq136FineField M Q Nc => z.2)
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
      (PartialEq136Bond M Q) (Nc ^ 2 - 1))
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff
            (cmp116Eq80Lemma1CombinedSourceSmallFieldCarrier
              anchor domains E)
            (epsilon1 / gk) (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P (epsilon1 / gk)
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0) :
    ∀ (psi : RestrictedField spectatorSupport (fun _ => SUNLieCoord Nc))
      (phi : RestrictedField fluctuationSupport (fun _ => SUNLieCoord Nc))
      (y : Fin (CMP116Eq80Lemma1CombinedDomainCount anchor domains E)),
      |cmp116CenteredConditionedCombinedEq80PartialResidual
          spectatorSupport fluctuationSupport anchor domains E V
          contourCarrier e K hc hmass hK baseCoarseCovariance
          layerWord choice D D₃ V₀ Pprop T DeltaPi J gk
          sigma psi phi y
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds
              (cmp116Eq80Lemma1CombinedCenteredRegion anchor domains E P))
            (cmp116SourcePhysicalCoordinateCochain b))| ≤
        cmp116Eq136ResidualMajorant (E0Direct + lemma1.E0)
          epsilon1 C1 M q C2 kappa1 delta kappa
          (cmp116Eq80Lemma1CombinedDomainMetric anchor domains E y : ℝ) := by
  intro psi phi y
  simpa only [cmp116CenteredConditionedCombinedEq80PartialResidual_apply] using
    (abs_cmp116Eq80Lemma1CombinedPhysicalResidual_le_eq136
      Dict anchor domains E V P contourCarrier e deltaRadius radius
      hradius hradiusCap K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hDelta hDelta1 sigma hsigma
      hsmallContour layerWord choice D D₃ V₀ Pprop T DeltaPi J
      gk epsilon1 C1 C2 kappa1 delta kappa lemma1 hD hD₃ hV₀
      C Rjet sourceJetBound hsourceJetBound hC hRjet hsourceJet
      hcardRatio0 hmetricRatio0 hsummation0 hkappaCard E0Direct hE0Direct
      hepsilon1_one hC1 hresidualRate0 hsplit hcardDecay hmetricDecay
      hsmall hbudget b hcutoff y)

end

end YangMills.RG

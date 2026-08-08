/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCThirdFieldContDiff
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCThirdFieldSourceMetricBound
import YangMills.RG.BalabanCMP102Eq80SourcePi4IndexedCutoffResidual
import YangMills.RG.BalabanCMP102Eq80PhysicalIndexedResidual

/-!
# Physical source-metric producer for the indexed cubic residual

This file removes the abstract function and abstract third-jet bound from the
indexed cutoff residual theorem.  The function is the literal complete-domain
CMP102 equation-(80) FTC potential; its `C³` certificate and its source-metric
third-jet majorant are both produced internally.

The source-facing joint-jet estimates and the random-walk scalar conditions
remain visible.  No equation-(1.36) estimate is assumed here: comparison of the
explicit coefficient below with the printed residual majorant is the next,
separate scalar checkpoint.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

open MeasureTheory

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CoarseField Q Nc →L[ℝ] FineField M Q Nc

/-- The indexed cutoff residual for the literal CMP102 domain potential is
controlled by the physical source-metric third-jet producer.  In particular,
neither a free function `f`, a free regularity certificate, nor a free
pointwise `hsource` occurs in the interface. -/
theorem
    abs_half_inner_cmp116RadialTaylorResidualOperator_eq80IndexedPhysicalDomain_le_centeredEnergy_of_sourceMetric
    {M Q Nc L lieDim R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (Pcut : Finset (PhysicalBond 4 (M * (2 * Q))))
    (epsilon1 gk : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hepsilon1 : 0 ≤ epsilon1) (hgk : 0 < gk)
    (hcutoff :
      (-1 : ℂ) ^ Pcut.card *
          cmp116SmallFieldCutoff
            (cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor domains)
            (epsilon1 / gk) (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff Pcut (epsilon1 / gk)
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
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
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Pprop T : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J : FineField M Q Nc)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (C Rjet sourceJetBound : ℝ)
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
            (fun q :
                RectangularFieldMap M Q Nc × FineField M Q Nc => q.2)
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
            D D₃ Δπ J 4
              (Pprop + t • T,
                cmp109ConstrainedLinearFluctuation (L := M) gk X)
              C Rjet) 0 ≤ sourceJetBound)
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
    let Y :=
      cmp102Eq80SourcePi4IndexedLocalizationDomain
        (M := M) anchor domains i
    let Z0 := cmp102Eq80SourcePi4CenteredRegion anchor domains Pcut
    let B := physicalBondProjection Y.bondSupport
      (cmp116SourcePhysicalCoordinateCochain b)
    let sourceMajorant :=
      cmp102Eq80PhysicalDomainFTCThirdFieldSourceMetricMajorant
        baseCoarseCovariance sourceJetBound κcard κmetric
        summationRatio layerWord Y Δ
    |cmp102Eq80PhysicalIndexedCouplingScaledResidual
        anchor domains i K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ Pprop T Δπ J gk B| ≤
      (sourceMajorant *
          (gk ^ 2 * (1 + (M : ℝ) ^ 3) ^ 3) *
          (Real.sqrt (((M ^ 4 * Y.blocks.card) * 4 : ℕ) : ℝ) *
            epsilon1) / 3) / 2 *
        (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
          b ba ^ 2) := by
  dsimp only
  let Y :=
    cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor domains i
  let f : FineField M Q Nc → ℝ := fun A =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ V₀ Pprop T Δπ J A Y.blocks
  let sourceMajorant :=
    cmp102Eq80PhysicalDomainFTCThirdFieldSourceMetricMajorant
      baseCoarseCovariance sourceJetBound κcard κmetric
      summationRatio layerWord Y Δ
  have hf : ContDiff ℝ 3 f := by
    exact
      contDiff_three_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmallContour layerWord choice
        D D₃ V₀ Pprop T Δπ J Y.blocks hD hD₃ hV₀
  have hsource :
      ∀ X, cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
        ‖iteratedFDeriv ℝ 3 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk X)‖ ≤
            sourceMajorant := by
    intro X hX
    exact
      norm_iteratedFDeriv_three_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_le_sourceMetric
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmallContour layerWord choice
        D D₃ V₀ Pprop T Δπ J
        (cmp109ConstrainedLinearFluctuation (L := M) gk X) Y
        hD hD₃ hV₀ C Rjet sourceJetBound
        (hC X hX) (hRjet X hX) (hsourceJet X hX)
        hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
        hsplit hcardDecay hmetricDecay hsmall
  have hzero :
      cmp98SourceFieldSupNorm
          (0 : FineField M Q Nc) ≤ epsilon1 / gk := by
    have hdiv : 0 ≤ epsilon1 / gk :=
      div_nonneg hepsilon1 hgk.le
    simpa using hdiv
  have hsourceMajorant : 0 ≤ sourceMajorant :=
    le_trans (norm_nonneg _) (hsource 0 hzero)
  have hterminal :=
    abs_half_inner_cmp116RadialTaylorResidualOperator_eq80IndexedCouplingScaledDomainProjection_le_centeredEnergy_of_printedCutoff
      Dict anchor domains i Pcut epsilon1 gk b
      hepsilon1 hgk hcutoff f hf sourceMajorant hsourceMajorant hsource
  change
    |cmp102Eq80CouplingScaledTotalTaylorResidual gk f
      (physicalBondProjection Y.bondSupport
        (cmp116SourcePhysicalCoordinateCochain b))| ≤ _
  rw [cmp102Eq80CouplingScaledTotalTaylorResidual_eq_radial
    gk f (hf.of_le (by norm_num))]
  exact hterminal

end

end YangMills.RG

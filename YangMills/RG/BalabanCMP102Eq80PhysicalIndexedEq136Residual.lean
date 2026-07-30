/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalIndexedCutoffResidualSourceMetric
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCEq136Residual
import YangMills.RG.BalabanCMP102Eq80PhysicalIndexedResidual

/-!
# The literal indexed equation-(80) residual satisfies equation (1.36)

This file composes the physical complete-domain FTC potential, its physical
source-metric third-jet producer, the literal small/large-field cutoff, the
exact `g_k³` cancellation, and the scalar producer budget.

The terminal theorem contains no free function, free third-jet majorant, or
pointwise equation-(1.36) hypothesis.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

open MeasureTheory

namespace YangMills.RG

noncomputable section

private abbrev Eq136FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev Eq136CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev Eq136RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  Eq136CoarseField Q Nc →L[ℝ] Eq136FineField M Q Nc

/-- The literal indexed equation-(80) radial residual satisfies the printed
equation-(1.36) majorant.  All field-dependent and domain-dependent estimates
are produced internally. -/
theorem
    abs_half_inner_cmp116RadialTaylorResidualOperator_eq80IndexedPhysicalDomain_le_eq136
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (Pcut : Finset (PhysicalBond 4 (M * (2 * Q))))
    (epsilon1 gk : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hepsilon1 : 0 ≤ epsilon1) (hepsilon1_one : epsilon1 ≤ 1)
    (hgk : 0 < gk)
    (hcutoff :
      (-1 : ℂ) ^ Pcut.card *
          cmp116SmallFieldCutoff
            (cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor domains)
            (epsilon1 / gk) (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff Pcut (epsilon1 / gk)
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0)
    (K : Eq136FineField M Q Nc →L[ℝ] Eq136FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      Eq136CoarseField Q Nc →L[ℝ] Eq136CoarseField Q Nc)
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
    (D D₃ : Eq136FineField M Q Nc → Eq136CoarseField Q Nc)
    (V₀ : Eq136FineField M Q Nc → ℝ)
    (Pprop T : Eq136RectangularFieldMap M Q Nc)
    (Δπ : Eq136FineField M Q Nc →L[ℝ] Eq136FineField M Q Nc)
    (J : Eq136FineField M Q Nc)
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
            (fun q :
                Eq136RectangularFieldMap M Q Nc ×
                  Eq136FineField M Q Nc => q.2)
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
    {cardRatio metricRatio summationRatio κcard : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 < κcard)
    (E0 C1 : ℝ) (q : ℕ) (C2 kappa1 delta kappa : ℝ)
    (hresidualRate0 :
      0 ≤ cmp102Eq80Eq136ResidualMetricRate delta kappa)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp
        (-(cmp102Eq80Eq136ResidualMetricRate delta kappa * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (hbudget : CMP102Eq80Eq136ThirdJetProducerBudget
      (M := M) baseCoarseCovariance sourceJetBound κcard
      delta kappa summationRatio layerWord Δ q E0 C1 C2 kappa1) :
    let Y :=
      cmp102Eq80SourcePi4IndexedLocalizationDomain
        (M := M) anchor domains i
    let B := physicalBondProjection Y.bondSupport
      (cmp116SourcePhysicalCoordinateCochain b)
    |cmp102Eq80PhysicalIndexedCouplingScaledResidual
        anchor domains i K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmallContour layerWord choice
        D D₃ V₀ Pprop T Δπ J hD hD₃ hV₀ gk B| ≤
      cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
        C2 kappa1 delta kappa
          (cmp116CubeEdgeTreeMetric Y : ℝ) := by
  dsimp only
  let W := cmp102Eq80SourcePi4DomainAt anchor domains i
  let Y :=
    cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor domains i
  let f : Eq136FineField M Q Nc → ℝ := fun A =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ V₀ Pprop T Δπ J A Y.blocks
  let sourceMajorant :=
    cmp102Eq80PhysicalDomainFTCThirdFieldSourceMetricMajorant
      baseCoarseCovariance sourceJetBound κcard
      (cmp102Eq80Eq136ResidualMetricRate delta kappa)
      summationRatio layerWord Y Δ
  have hW : W ∈ domains := by
    simpa [W] using
      cmp102Eq80SourcePi4DomainAt_mem anchor domains i
  have hY :
      Y = cmp102Eq80SourcePi4LocalizationDomain (M := M) anchor W := by
    rfl
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
        hcardRatio0 hmetricRatio0 hsummation0 hκcard.le hresidualRate0
        hsplit hcardDecay hmetricDecay hsmall
  have hzero :
      cmp98SourceFieldSupNorm
          (0 : Eq136FineField M Q Nc) ≤ epsilon1 / gk := by
    have hdiv : 0 ≤ epsilon1 / gk :=
      div_nonneg hepsilon1 hgk.le
    simpa using hdiv
  have hsourceMajorant : 0 ≤ sourceMajorant :=
    le_trans (norm_nonneg _) (hsource 0 hzero)
  have hprinted :
      sourceMajorant * (1 + (M : ℝ) ^ 3) ^ 3 *
          Real.sqrt
            ((((M ^ 4 * Y.blocks.card) * 4 : ℕ) : ℝ)) ^ 3 *
          epsilon1 ^ 3 / 6 ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa
            (cmp116CubeEdgeTreeMetric Y : ℝ) := by
    exact
      cmp102Eq80PhysicalDomainFTCThirdFieldCubicCutoffMajorant_le_eq136
        baseCoarseCovariance sourceJetBound κcard delta kappa
        summationRatio layerWord Y Δ q E0 epsilon1 C1 C2 kappa1
        hsourceJetBound hκcard hsummation0 hsmall
        hepsilon1 hepsilon1_one hbudget
  have hterminal :=
    abs_half_inner_cmp116RadialTaylorResidualOperator_eq80CouplingScaledDomainProjection_le_eq136_of_source
      anchor domains W hW Pcut epsilon1 gk b hepsilon1 hgk hcutoff
      f hf sourceMajorant hsourceMajorant hsource
      E0 C1 q C2 kappa1 delta kappa
      (by simpa [hY] using hprinted)
  simpa [W, Y, f, hY,
    cmp102Eq80PhysicalIndexedCouplingScaledResidual,
    cmp102Eq80CouplingScaledTaylorResidual] using hterminal

end

end YangMills.RG

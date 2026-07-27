/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailDomainReassembly
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainCoefficientRegularity

/-!
# FTC contribution of one complete physical domain

For one dependent coarse/fine choice, the complete coefficient of a fixed
domain is integrated along the literal affine propagator segment.  The
finite sum over domains commutes with this FTC integral because every
domain coefficient was proved interval-integrable independently.
-/

open scoped RealInnerProductSpace
open MeasureTheory

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- Literal FTC contribution of one complete physical domain for one
dependent coarse/fine choice. -/
noncomputable def cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q))) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    cmp102Eq80PhysicalFineHeadTailDomainCoefficient
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ (P + t • T) Δπ J A
      (fderiv ℝ V₀ (A - (P + t • T) (D A))) Y

/-- The FTC integral of one complete choice is exactly the finite sum of
the FTC contributions of its complete physical domains. -/
theorem
    integral_cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries_eq_sum_domainFTCContributions
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
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
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀) :
    (∫ t in (0 : ℝ)..1,
      cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ (P + t • T) Δπ J A
        (fderiv ℝ V₀ (A - (P + t • T) (D A)))) =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J A Y := by
  calc
    (∫ t in (0 : ℝ)..1,
      cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ (P + t • T) Δπ J A
        (fderiv ℝ V₀ (A - (P + t • T) (D A)))) =
      ∫ t in (0 : ℝ)..1,
        ∑ Y : Finset (FinBox 4 (2 * Q)),
          cmp102Eq80PhysicalFineHeadTailDomainCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ (P + t • T) Δπ J A
            (fderiv ℝ V₀ (A - (P + t • T) (D A))) Y := by
      apply intervalIntegral.integral_congr
      intro t _ht
      exact
        cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries_eq_sum_domainCoefficients
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          sigma hRweak hcap hsmall layerWord choice D D₃
          (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A)))
    _ =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        ∫ t in (0 : ℝ)..1,
          cmp102Eq80PhysicalFineHeadTailDomainCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ (P + t • T) Δπ J A
            (fderiv ℝ V₀ (A - (P + t • T) (D A))) Y := by
      apply intervalIntegral.integral_finset_sum
      intro Y _hY
      exact
        intervalIntegrable_cmp102Eq80PhysicalFineHeadTailDomainCoefficient_affine
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          sigma hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J A Y hV₀
    _ =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J A Y := by
      rfl

end

end YangMills.RG

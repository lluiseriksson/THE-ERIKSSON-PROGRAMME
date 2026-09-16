/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailAbsoluteLocalization

/-!
# Complete equation-(80) coefficient of one physical domain

The absolutely convergent rectangular matrix fiber is reconstructed as a
physical minimizer direction and consumed by the equation-(80) directional
derivative.  Both maps are continuous and additive, so this construction is
exactly the head-length `tsum` of the literal scalar fiber coefficients.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- Scalar equation-(80) contribution of one physical domain at one fine
head length. -/
noncomputable def cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
    {M Q Nc R headLength n : ℕ}
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
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ)
    (Y : Finset (FinBox 4 (2 * Q))) : ℝ :=
  cmp102Eq80PropagatorDirectionalDerivative D D₃ H
    (cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y))
    Δπ J A V₀'

/-- The reconstructed scalar layer is literally the finite fiber
coefficient already used in the exact regrouping theorem. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer_eq_fiberCoefficient
    {M Q Nc R headLength n : ℕ}
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
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ)
    (Y : Finset (FinBox 4 (2 * Q))) :
    cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance sigma
        layerWord choice D D₃ H Δπ J A V₀' Y =
      cmp116CarrierAnchoredFiberCoefficient
        (cmp116CoarseFaceAdj 4 (2 * Q))
        (Finset.univ :
          Finset (CMP99SourcePi4FineWalkIndex M Q R headLength))
        (cmp102Eq80SourcePi4AnchorCarrier anchor)
        (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
          cmp99SourcePi4FineHeadTailActive anchor head choice)
        (fun head =>
          cmp102Eq80PropagatorDirectionalDerivative D D₃ H
            (cmp99SourcePi4PhysicalFineHeadTailWordTerm
              anchor K hc hmass hK baseCoarseCovariance
              sigma head layerWord choice)
            Δπ J A V₀')
        Y := by
  classical
  unfold cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
    cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
    cmp116CarrierAnchoredFiberCoefficient
  rw [show cmp99PhysicalRectangularOfComplexMatrix
      (∑ head ∈
        (Finset.univ :
          Finset (CMP99SourcePi4FineWalkIndex M Q R headLength)).filter
          (fun head =>
            cmp116CarrierAnchoredLocalizationDomain
              (cmp116CoarseFaceAdj 4 (2 * Q))
              (cmp102Eq80SourcePi4AnchorCarrier anchor)
              (fun h : CMP99SourcePi4FineWalkIndex M Q R headLength =>
                cmp99SourcePi4FineHeadTailActive anchor h choice)
              head = Y),
        cmp99SourcePi4ComplexFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice) =
      ∑ head ∈
        (Finset.univ :
          Finset (CMP99SourcePi4FineWalkIndex M Q R headLength)).filter
          (fun head =>
            cmp116CarrierAnchoredLocalizationDomain
              (cmp116CoarseFaceAdj 4 (2 * Q))
              (cmp102Eq80SourcePi4AnchorCarrier anchor)
              (fun h : CMP99SourcePi4FineWalkIndex M Q R headLength =>
                cmp99SourcePi4FineHeadTailActive anchor h choice)
              head = Y),
        cmp99PhysicalRectangularOfComplexMatrix
          (cmp99SourcePi4ComplexFineHeadTailWordTerm
            anchor K hc hmass hK baseCoarseCovariance
            sigma head layerWord choice) by
      simpa only [
        cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom_apply] using
        (map_sum
          cmp99PhysicalRectangularOfComplexMatrixContinuousAddHom
          (fun head =>
            cmp99SourcePi4ComplexFineHeadTailWordTerm
              anchor K hc hmass hK baseCoarseCovariance
              sigma head layerWord choice)
          ((Finset.univ :
            Finset (CMP99SourcePi4FineWalkIndex M Q R headLength)).filter
            (fun head =>
              cmp116CarrierAnchoredLocalizationDomain
                (cmp116CoarseFaceAdj 4 (2 * Q))
                (cmp102Eq80SourcePi4AnchorCarrier anchor)
                (fun h : CMP99SourcePi4FineWalkIndex M Q R headLength =>
                  cmp99SourcePi4FineHeadTailActive anchor h choice)
                head = Y)))]
  change
    cmp102Eq80PropagatorDirectionalDerivativeCLM
        D D₃ H Δπ J A V₀'
        (∑ head ∈
          (Finset.univ :
            Finset (CMP99SourcePi4FineWalkIndex M Q R headLength)).filter
            (fun head =>
              cmp116CarrierAnchoredLocalizationDomain
                (cmp116CoarseFaceAdj 4 (2 * Q))
                (cmp102Eq80SourcePi4AnchorCarrier anchor)
                (fun h : CMP99SourcePi4FineWalkIndex M Q R headLength =>
                  cmp99SourcePi4FineHeadTailActive anchor h choice)
                head = Y),
          cmp99PhysicalRectangularOfComplexMatrix
            (cmp99SourcePi4ComplexFineHeadTailWordTerm
              anchor K hc hmass hK baseCoarseCovariance
              sigma head layerWord choice)) = _
  rw [map_sum]
  rfl

/-- For every physical domain the scalar equation-(80) layers are genuinely
summable. -/
theorem summable_cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
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
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ)
    (Y : Finset (FinBox 4 (2 * Q))) :
    Summable fun headLength : ℕ =>
      cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance sigma
        layerWord choice D D₃ H Δπ J A V₀' Y := by
  have hmatrix :=
    summable_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice Y
  have hphysical :=
    summable_cmp99PhysicalRectangularOfComplexMatrix
      (fun headLength : ℕ =>
        cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
          (headLength := headLength)
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice Y)
      hmatrix
  simpa [cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer] using
    (summable_cmp102Eq80PropagatorDirectionalDerivative
      D D₃ H
      (fun headLength : ℕ =>
        cmp99PhysicalRectangularOfComplexMatrix
          (cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
            (headLength := headLength)
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y))
      Δπ J A V₀' hphysical)

/-- Complete scalar equation-(80) coefficient of one physical domain. -/
noncomputable def cmp102Eq80PhysicalFineHeadTailDomainCoefficient
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
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ)
    (Y : Finset (FinBox 4 (2 * Q))) : ℝ :=
  ∑' headLength : ℕ,
    cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
      (headLength := headLength)
      anchor K hc hmass hK baseCoarseCovariance sigma
      layerWord choice D D₃ H Δπ J A V₀' Y

end

end YangMills.RG

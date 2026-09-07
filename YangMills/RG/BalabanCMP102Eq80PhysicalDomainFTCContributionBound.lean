/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCContribution
import YangMills.RG.BalabanCMP102Eq80PropagatorDerivativeUniform

/-!
# Quantitative bound for one physical-domain FTC contribution

The equation-(80) functional is uniformly bounded on the compact radial
segment.  Consequently the FTC contribution of one literal physical
domain is bounded by that common coefficient times the norm of the
complete reconstructed domain matrix.

This is not the source estimate (1.43): it exposes precisely the remaining
quantitative obligation on the domain matrix coefficient, rather than
renaming that obligation as a bound on the final scalar contribution.
-/

open scoped RealInnerProductSpace Matrix.Norms.Operator

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- The reconstructed complete physical-domain coefficient is bounded by
the absolutely summable series of its reconstructed matrix layers.  The
summability is produced from the literal physical walk majorant; no
domain-size decay is asserted here. -/
theorem
    norm_reconstruct_cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient_le
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
    (Y : Finset (FinBox 4 (2 * Q))) :
    ‖cmp99PhysicalRectangularOfComplexMatrix
        (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice Y)‖ ≤
      ∑' headLength : ℕ,
        ‖cmp99PhysicalRectangularOfComplexMatrix
          (cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
            (headLength := headLength)
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y)‖ := by
  let layer := fun headLength : ℕ =>
    cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
      (headLength := headLength)
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice Y
  let major := fun headLength : ℕ =>
    ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
      ‖cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma head layerWord choice‖
  have hlayer : Summable layer :=
    summable_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice Y
  have hmajor : Summable major :=
    summable_sum_norm_cmp99SourcePi4ComplexFineHeadTailWordTerm
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice
  have hlayerNorm : Summable fun headLength : ℕ => ‖layer headLength‖ := by
    apply Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun headLength =>
        norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer_le
          (headLength := headLength)
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice Y)
      hmajor
  have hphysicalNorm :
      Summable fun headLength : ℕ =>
        ‖cmp99PhysicalRectangularOfComplexMatrix
          (layer headLength)‖ :=
    summable_norm_cmp99PhysicalRectangularOfComplexMatrix layer hlayerNorm
  change
    ‖cmp99PhysicalRectangularOfComplexMatrix
        (∑' headLength : ℕ, layer headLength)‖ ≤
      ∑' headLength : ℕ,
        ‖cmp99PhysicalRectangularOfComplexMatrix
          (layer headLength)‖
  rw [cmp99PhysicalRectangularOfComplexMatrix_tsum layer hlayer]
  exact norm_tsum_le_tsum_norm hphysicalNorm

/-- A pointwise bound for the equation-(80) functional on the radial
segment bounds the literal FTC contribution of one complete domain. -/
theorem norm_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_le
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
    (Y : Finset (FinBox 4 (2 * Q)))
    {C : ℝ}
    (hC : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      cmp102Eq80PropagatorDirectionalDerivativeBound
        D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) ≤ C) :
    ‖cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J A Y‖ ≤
      C *
        ‖cmp99PhysicalRectangularOfComplexMatrix
          (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y)‖ := by
  unfold cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
  calc
    ‖∫ t in (0 : ℝ)..1,
        cmp102Eq80PhysicalFineHeadTailDomainCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) Y‖ ≤
        (C *
          ‖cmp99PhysicalRectangularOfComplexMatrix
            (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y)‖) *
          |(1 : ℝ) - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [
        cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_derivative_matrixCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          sigma hRweak hcap hsmall layerWord choice
          D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) Y]
      exact
        (norm_cmp102Eq80PropagatorDirectionalDerivative_le
          D D₃ (P + t • T)
          (cmp99PhysicalRectangularOfComplexMatrix
            (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y))
          Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A)))).trans
        (mul_le_mul_of_nonneg_right
          (hC t ⟨le_of_lt ht.1, ht.2⟩) (norm_nonneg _))
    _ = C *
        ‖cmp99PhysicalRectangularOfComplexMatrix
          (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y)‖ := by
      norm_num

/-- Fully produced reconstructed-layer majorant for one domain FTC
contribution.  The only scalar coefficient outside the physical series is
the explicit uniform norm of the equation-(80) functional on the radial
segment. -/
theorem
    norm_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_le_reconstructedLayerMajorant
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
    (Y : Finset (FinBox 4 (2 * Q)))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      cmp102Eq80PropagatorDirectionalDerivativeBound
        D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) ≤ C) :
    ‖cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J A Y‖ ≤
      C *
        (∑' headLength : ℕ,
          ‖cmp99PhysicalRectangularOfComplexMatrix
            (cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
              (headLength := headLength)
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y)‖) := by
  let major : ℝ :=
    ∑' headLength : ℕ,
      ‖cmp99PhysicalRectangularOfComplexMatrix
        (cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
          (headLength := headLength)
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice Y)‖
  have hreconstruct :=
    norm_reconstruct_cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient_le
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice Y
  exact
    (norm_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_le
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J A Y hC).trans
      (by
        simpa [major] using
          mul_le_mul_of_nonneg_left hreconstruct hC0)

/-- The common FTC coefficient exists automatically by compactness of the
radial segment.  It is independent of the word choice and of the physical
domain. -/
theorem
    exists_uniform_bound_norm_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
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
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
        (Y : Finset (FinBox 4 (2 * Q))),
        ‖cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ V₀ P T Δπ J A Y‖ ≤
          C *
            ‖cmp99PhysicalRectangularOfComplexMatrix
              (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
                anchor K hc hmass hK baseCoarseCovariance
                sigma layerWord choice Y)‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_uniform_bound_cmp102Eq80AffinePropagatorDirectionalDerivative
      D D₃ V₀ P T Δπ J A hV₀
  refine ⟨C, hC0, ?_⟩
  intro choice Y
  exact
    norm_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_le
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J A Y hC

end

end YangMills.RG

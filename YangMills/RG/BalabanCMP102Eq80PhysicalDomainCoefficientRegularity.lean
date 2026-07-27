/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailDomainCoefficient
import YangMills.RG.BalabanCMP102Eq80MinimizerTelescoping

/-!
# Reconstruction and regularity of a complete physical-domain coefficient

The complete scalar domain coefficient is the equation-(80) directional
derivative applied once to the complete rectangular matrix coefficient.
This removes the head-length `tsum` from the varying FTC data.  Along an
affine propagator line the resulting coefficient is therefore continuous
and interval-integrable whenever the literal potential is `C¹`.
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

/-- A complete scalar domain coefficient is obtained by reconstructing its
complete rectangular matrix coefficient and applying the literal
equation-(80) derivative once. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_derivative_matrixCoefficient
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
    cmp102Eq80PhysicalFineHeadTailDomainCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ H Δπ J A V₀' Y =
      cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (cmp99PhysicalRectangularOfComplexMatrix
          (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y))
        Δπ J A V₀' := by
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
  calc
    cmp102Eq80PhysicalFineHeadTailDomainCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ H Δπ J A V₀' Y =
      ∑' headLength : ℕ,
        cmp102Eq80PropagatorDirectionalDerivative D D₃ H
          (cmp99PhysicalRectangularOfComplexMatrix
            (cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
              (headLength := headLength)
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y))
          Δπ J A V₀' := by
      rfl
    _ =
      cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (∑' headLength : ℕ,
          cmp99PhysicalRectangularOfComplexMatrix
            (cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
              (headLength := headLength)
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y))
        Δπ J A V₀' :=
      (cmp102Eq80PropagatorDirectionalDerivative_tsum
        D D₃ H
        (fun headLength : ℕ =>
          cmp99PhysicalRectangularOfComplexMatrix
            (cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
              (headLength := headLength)
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y))
        Δπ J A V₀' hphysical).symm
    _ =
      cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (cmp99PhysicalRectangularOfComplexMatrix
          (∑' headLength : ℕ,
            cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
              (headLength := headLength)
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y))
        Δπ J A V₀' := by
      rw [
        cmp99PhysicalRectangularOfComplexMatrix_tsum
          (fun headLength : ℕ =>
            cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
              (headLength := headLength)
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y)
          hmatrix]
    _ =
      cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (cmp99PhysicalRectangularOfComplexMatrix
          (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y))
        Δπ J A V₀' := by
      rfl

/-- Along an affine propagator line, a complete physical-domain coefficient
is continuous. -/
theorem continuous_cmp102Eq80PhysicalFineHeadTailDomainCoefficient_affine
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
    (hV₀ : ContDiff ℝ 1 V₀) :
    Continuous fun t : ℝ =>
      cmp102Eq80PhysicalFineHeadTailDomainCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ (P + t • T) Δπ J A
        (fderiv ℝ V₀ (A - (P + t • T) (D A))) Y := by
  let Kdomain :=
    cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y)
  have hbase :
      Continuous fun t : ℝ =>
        cmp102Eq80PropagatorDirectionalDerivative D D₃
          (P + t • T) Kdomain Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) := by
    exact
      continuous_cmp102Eq80PropagatorDirectionalDerivative
        D D₃ V₀ (fun t : ℝ => P + t • T) Kdomain Δπ J A
        (by fun_prop) (hV₀.continuous_fderiv one_ne_zero)
  apply hbase.congr
  intro t
  exact
    (cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_derivative_matrixCoefficient
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice
      D D₃ (P + t • T) Δπ J A
      (fderiv ℝ V₀ (A - (P + t • T) (D A))) Y).symm

/-- The same affine physical-domain coefficient is interval-integrable on
the FTC segment. -/
theorem intervalIntegrable_cmp102Eq80PhysicalFineHeadTailDomainCoefficient_affine
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
    (hV₀ : ContDiff ℝ 1 V₀) :
    IntervalIntegrable
      (fun t : ℝ =>
        cmp102Eq80PhysicalFineHeadTailDomainCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) Y)
      volume 0 1 :=
  by
    have hcontinuous :=
      continuous_cmp102Eq80PhysicalFineHeadTailDomainCoefficient_affine
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmall layerWord choice
        D D₃ V₀ P T Δπ J A Y hV₀
    exact hcontinuous.continuousOn.intervalIntegrable

end

end YangMills.RG

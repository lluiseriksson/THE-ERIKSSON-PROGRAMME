/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4ComplexCoarseNonsingularity
import YangMills.RG.BalabanCMP116ComplexQuadraticSchur

/-!
# Source bound for the complex CMP99 coarse-middle defect

The contour variation of the coarse middle is exactly

`Q (C(σ) - C(1)) Q*`.

This module transports the already constructed source contour estimate for
the fine covariance through the literal block maps and the physical coarse
inverse.  No independent coarse defect is introduced.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- Exact factorization of the contour coarse-middle difference. -/
theorem cmp99SourcePi4FullComplexCoarseMiddleMatrix_sub_one
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    cmp99SourcePi4FullComplexCoarseMiddleMatrix
          (R := R) anchor K hc hmass hK sigma -
        cmp99SourcePi4FullComplexCoarseMiddleMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) =
      cmp99SourcePi4ComplexBlockMatrix (M := M) (Q := Q) (Nc := Nc) *
        (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK sigma -
          cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK (fun _ => 1)) *
        cmp99SourcePi4ComplexBlockAdjointMatrix
          (M := M) (Q := Q) (Nc := Nc) := by
  unfold cmp99SourcePi4FullComplexCoarseMiddleMatrix
  ext row col
  simp only [Matrix.sub_apply, Matrix.mul_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib]

/-- The literal coarse relative defect is controlled by the fine covariance
defect and the three physical matrix factors. -/
theorem norm_cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_le
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    ‖cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
        (R := R) anchor K hc hmass hK baseCoarseCovariance sigma‖ ≤
      ‖cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance‖ *
        ‖cmp99SourcePi4ComplexBlockMatrix
          (M := M) (Q := Q) (Nc := Nc)‖ *
        ‖cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK sigma -
            cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK (fun _ => 1)‖ *
        ‖cmp99SourcePi4ComplexBlockAdjointMatrix
          (M := M) (Q := Q) (Nc := Nc)‖ := by
  rw [cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect,
    cmp99SourcePi4FullComplexCoarseMiddleMatrix_sub_one]
  let C0 :=
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance
  let Q0 :=
    cmp99SourcePi4ComplexBlockMatrix (M := M) (Q := Q) (Nc := Nc)
  let Qstar :=
    cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc)
  let D :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma -
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1)
  change ‖C0 * (Q0 * D * Qstar)‖ ≤
    ‖C0‖ * ‖Q0‖ * ‖D‖ * ‖Qstar‖
  calc
    ‖C0 * (Q0 * D * Qstar)‖ ≤ ‖C0‖ * ‖Q0 * D * Qstar‖ :=
      Matrix.linfty_opNorm_mul _ _
    _ ≤ ‖C0‖ * (‖Q0‖ * ‖D‖ * ‖Qstar‖) :=
      mul_le_mul_of_nonneg_left
        ((Matrix.linfty_opNorm_mul (Q0 * D) Qstar).trans
          (mul_le_mul_of_nonneg_right
            (Matrix.linfty_opNorm_mul Q0 D)
            (norm_nonneg Qstar)))
        (norm_nonneg C0)
    _ = _ := by ring

/-- Explicit source upper bound for the fine covariance contour defect. -/
noncomputable def cmp99SourcePi4FineComplexContourDefectBound
    (Nc Δ : ℕ) (Ahead rho rate radius Rweak : ℝ) : ℝ :=
  (cmp116SourcePi4ComplexContourPrefactor Ahead radius Rweak *
      (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹ ^ 2) *
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)

/-- Explicit source upper bound for the relative coarse-middle defect. -/
noncomputable def cmp99SourcePi4ComplexCoarseRelativeDefectBound
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (Δ : ℕ) (Ahead rho rate radius Rweak : ℝ) : ℝ :=
  ‖cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance‖ *
    ‖cmp99SourcePi4ComplexBlockMatrix
      (M := M) (Q := Q) (Nc := Nc)‖ *
    cmp99SourcePi4FineComplexContourDefectBound
      Nc Δ Ahead rho rate radius Rweak *
    ‖cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc)‖

/-- The source contour estimates generate the actual coarse relative-defect
bound. -/
theorem norm_cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_le_source
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ‖cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
        (R := R) anchor K hc hmass hK baseCoarseCovariance sigma‖ ≤
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc) baseCoarseCovariance
        Δ Ahead rho rate radius Rweak := by
  apply (norm_cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_le
    anchor K hc hmass hK baseCoarseCovariance sigma).trans
  unfold cmp99SourcePi4ComplexCoarseRelativeDefectBound
    cmp99SourcePi4FineComplexContourDefectBound
  gcongr
  exact
    linfty_opNorm_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_le
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma hradius hRweak hdiff hcap hsmall

/-- Source contour data and the explicit scalar coarse-defect budget imply
nonsingularity of the literal coarse middle. -/
theorem cmp99SourcePi4FullComplexCoarseMiddleMatrix_det_ne_zero_of_source
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange : PhysicalCovarianceFiniteRange
      K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor K hc hmass hK (fun _ => 1)) coarseRate)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1) :
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix
      (R := R) anchor K hc hmass hK sigma).det ≠ 0 := by
  apply cmp99SourcePi4FullComplexCoarseMiddleMatrix_det_ne_zero
    anchor K hsourceRange hfiniteRange hc hmass hK hD
    hcoarseRate hcoarse sigma
  exact lt_of_le_of_lt
    (norm_cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_le_source
      anchor K hc hmass hK
      (cmp99SourcePi4WeakenedCoarseCovariance
        (R := R) anchor K hc hmass hK (fun _ => 1)
        hcoarseRate hcoarse)
      hAhead hrho hrate hgeom Cert htri hsourceRange hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hcontourSmall)
    hcoarseSmall

end

end YangMills.RG

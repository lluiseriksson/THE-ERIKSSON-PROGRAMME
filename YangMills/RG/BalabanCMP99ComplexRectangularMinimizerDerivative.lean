/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexMatrixInverseRegularity
import YangMills.RG.BalabanCMP99SourcePi4ComplexCoarseDefectBound
import YangMills.RG.BalabanCMP116SourcePi4FullComplexWeakenedCovarianceDerivativeSeries

/-!
# Coordinate derivative of the complex rectangular CMP99 minimizer

For a fine covariance curve `C(u)` and fixed block matrices `Q,Q*`, this
module differentiates the literal rectangular minimizer

`H(u) = C(u) Q* (Q C(u) Q*)⁻¹`

entry by entry.  The inverse regularity is generated from the determinant
and adjugate.  The source-specific terminal theorem then obtains the
coarse-middle nonvanishing determinant from the already proved contour
defect estimate.
-/

namespace YangMills.RG

noncomputable section

/-- Coarse middle associated with a complex fine covariance curve. -/
noncomputable def cmp99ComplexCoarseMiddleCurve
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ℂ → Matrix ι ι ℂ)
    (Q : Matrix κ ι ℂ) (Qstar : Matrix ι κ ℂ)
    (u : ℂ) : Matrix κ κ ℂ :=
  (Q * C u) * Qstar

/-- Rectangular background-minimizer curve. -/
noncomputable def cmp99ComplexBackgroundMinimizerCurve
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ℂ → Matrix ι ι ℂ)
    (Q : Matrix κ ι ℂ) (Qstar : Matrix ι κ ℂ)
    (u : ℂ) : Matrix ι κ ℂ :=
  (C u * Qstar) * (cmp99ComplexCoarseMiddleCurve C Q Qstar u)⁻¹

/-- Entrywise differentiability of the fine covariance produces
entrywise differentiability of the literal rectangular minimizer at every
point where the coarse middle is nonsingular. -/
theorem
    differentiableAt_cmp99ComplexBackgroundMinimizerCurveEntry
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ℂ → Matrix ι ι ℂ)
    (Q : Matrix κ ι ℂ) (Qstar : Matrix ι κ ℂ)
    (t : ℂ)
    (hC : ∀ i j, DifferentiableAt ℂ (fun u => C u i j) t)
    (hdet : (cmp99ComplexCoarseMiddleCurve C Q Qstar t).det ≠ 0)
    (row : ι) (col : κ) :
    DifferentiableAt ℂ
      (fun u => cmp99ComplexBackgroundMinimizerCurve
        C Q Qstar u row col) t := by
  classical
  have hMiddle : ∀ i j,
      DifferentiableAt ℂ
        (fun u => cmp99ComplexCoarseMiddleCurve C Q Qstar u i j) t := by
    intro i j
    simp only [cmp99ComplexCoarseMiddleCurve, Matrix.mul_apply]
    apply DifferentiableAt.fun_sum
    intro k _
    apply DifferentiableAt.mul_const
    apply DifferentiableAt.fun_sum
    intro l _
    exact (hC l k).const_mul (Q i l)
  have hInv : ∀ i j,
      DifferentiableAt ℂ
        (fun u => (cmp99ComplexCoarseMiddleCurve C Q Qstar u)⁻¹ i j) t := by
    intro i j
    exact
      differentiableAt_complexMatrixNonsingInvEntry_of_entrywise
        (cmp99ComplexCoarseMiddleCurve C Q Qstar)
        t hMiddle hdet i j
  simp only [cmp99ComplexBackgroundMinimizerCurve, Matrix.mul_apply]
  apply DifferentiableAt.fun_sum
  intro k _
  apply DifferentiableAt.mul
  · apply DifferentiableAt.fun_sum
    intro l _
    exact (hC row l).mul_const (Qstar l k)
  · exact hInv k col

/-- Canonical entry derivative of the rectangular minimizer. -/
noncomputable def cmp99ComplexBackgroundMinimizerCurveDerivative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ℂ → Matrix ι ι ℂ)
    (Q : Matrix κ ι ℂ) (Qstar : Matrix ι κ ℂ)
    (t : ℂ) : Matrix ι κ ℂ :=
  fun row col =>
    deriv (fun u =>
      cmp99ComplexBackgroundMinimizerCurve C Q Qstar u row col) t

/-- The generated coordinate derivative is the actual complex derivative
of every minimizer entry. -/
theorem hasDerivAt_cmp99ComplexBackgroundMinimizerCurveEntry
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ℂ → Matrix ι ι ℂ)
    (Q : Matrix κ ι ℂ) (Qstar : Matrix ι κ ℂ)
    (t : ℂ)
    (hC : ∀ i j, DifferentiableAt ℂ (fun u => C u i j) t)
    (hdet : (cmp99ComplexCoarseMiddleCurve C Q Qstar t).det ≠ 0)
    (row : ι) (col : κ) :
    HasDerivAt
      (fun u => cmp99ComplexBackgroundMinimizerCurve
        C Q Qstar u row col)
      (cmp99ComplexBackgroundMinimizerCurveDerivative
        C Q Qstar t row col) t :=
  (differentiableAt_cmp99ComplexBackgroundMinimizerCurveEntry
    C Q Qstar t hC hdet row col).hasDerivAt

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- The canonical source minimizer derivative when one weakening
coordinate is varied. -/
noncomputable def
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q)) (t : ℂ) :
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  cmp99ComplexBackgroundMinimizerCurveDerivative
    (fun u =>
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK
        (Function.update sigma d u))
    (cmp99SourcePi4ComplexBlockMatrix
      (M := M) (Q := Q) (Nc := Nc))
    (cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc))
    t

set_option maxHeartbeats 2000000 in
/-- The complete covariance contour derivative and a literal nonzero
coarse determinant generate the derivative of the rectangular source
minimizer. -/
theorem
    hasDerivAt_cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_update
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
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
    (d : FinBox 4 (2 * Q))
    (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (t : ℂ)
    (hdet :
      (cmp99SourcePi4FullComplexCoarseMiddleMatrix
        (R := R) anchor K hc hmass hK
        (Function.update sigma d t)).det ≠ 0)
    (row : FineCoord M Q Nc) (col : CoarseCoord Q Nc) :
    HasDerivAt
      (fun u =>
        cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
          (R := R) anchor K hc hmass hK
          (Function.update sigma d u) row col)
      (cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative
        (R := R) anchor K hc hmass hK sigma d t row col) t := by
  let Ccurve := fun u =>
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK
      (Function.update sigma d u)
  let Qmat :=
    cmp99SourcePi4ComplexBlockMatrix
      (M := M) (Q := Q) (Nc := Nc)
  let Qstar :=
    cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc)
  have hC : ∀ i j, DifferentiableAt ℂ (fun u => Ccurve u i j) t := by
    intro i j
    exact
      (hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_update
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 sigma d hRweak hsigma hcap hsmall i j t).differentiableAt
  have hgeneric :=
    hasDerivAt_cmp99ComplexBackgroundMinimizerCurveEntry
      Ccurve Qmat Qstar t hC hdet row col
  simpa [Ccurve, Qmat, Qstar,
    cmp99ComplexCoarseMiddleCurve,
    cmp99ComplexBackgroundMinimizerCurve,
    cmp99SourcePi4FullComplexCoarseMiddleMatrix,
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix,
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative]
    using hgeneric

set_option maxHeartbeats 3000000 in
/-- Source contour bounds generate both coarse nonsingularity and the
coordinate derivative of the literal rectangular minimizer.  In
particular, the caller supplies no determinant or inverse-regularity
certificate. -/
theorem
    hasDerivAt_cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_update_of_source
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
    (d : FinBox 4 (2 * Q))
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (t : ℂ)
    (hdiffUpdate :
      ∀ x, ‖Function.update sigma d t x - 1‖ ≤ radius)
    (hcapUpdate :
      ∀ x, ‖Function.update sigma d t x‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1)
    (row : FineCoord M Q Nc) (col : CoarseCoord Q Nc) :
    HasDerivAt
      (fun u =>
        cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
          (R := R) anchor K hc hmass hK
          (Function.update sigma d u) row col)
      (cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative
        (R := R) anchor K hc hmass hK sigma d t row col) t := by
  have hdet :
      (cmp99SourcePi4FullComplexCoarseMiddleMatrix
        (R := R) anchor K hc hmass hK
        (Function.update sigma d t)).det ≠ 0 :=
    cmp99SourcePi4FullComplexCoarseMiddleMatrix_det_ne_zero_of_source
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
      (Function.update sigma d t) hradius hRweak
      hdiffUpdate hcapUpdate hcontourSmall hcoarseSmall
  exact
    hasDerivAt_cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_update
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hsourceRange
      hΔ hΔ1 sigma d hRweak hsigma hcap hcontourSmall t hdet row col

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4ComplexCoarseDefectBound

/-!
# Exact response of the complex rectangular CMP99 minimizer

Once the literal coarse middle is nonsingular, the complex rectangular
matrix

`H(σ) = C(σ) Q* (Q C(σ) Q*)⁻¹`

has exact block response `Q H(σ) = 1`.  At full coupling it is precisely
the canonical coordinate matrix of the real source-faithful CMP99
minimizer.  These results prevent the fine square covariance from being
silently substituted for the rectangular background minimizer.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

/-- The complex rectangular minimizer has exact block response throughout
the nonsingular contour. -/
theorem cmp99SourcePi4ComplexBlockMatrix_mul_backgroundMinimizer_eq_one
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hdet :
      (cmp99SourcePi4FullComplexCoarseMiddleMatrix
        (R := R) anchor K hc hmass hK sigma).det ≠ 0) :
    cmp99SourcePi4ComplexBlockMatrix (M := M) (Q := Q) (Nc := Nc) *
        cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
          (R := R) anchor K hc hmass hK sigma =
      1 := by
  unfold cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
    cmp99SourcePi4FullComplexCoarseMiddleMatrix
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc
    (cmp99SourcePi4ComplexBlockMatrix
      (M := M) (Q := Q) (Nc := Nc))]
  exact Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (by
      simpa [cmp99SourcePi4FullComplexCoarseMiddleMatrix,
        Matrix.mul_assoc] using hdet))

/-- At full coupling, the complex rectangular matrix is the canonical
matrix of the source-faithful real CMP99 minimizer. -/
theorem
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_one_eq_weakenedPhysicalH
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
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
        (R := R) anchor K hc hmass hK (fun _ => 1)) coarseRate) :
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1) =
      cmp99PhysicalRectangularComplexMatrix
        (cmp99SourcePi4WeakenedPhysicalH
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse) := by
  unfold cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
  rw [
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD,
    cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_inv_eq_coarseCovariance
      anchor K hsourceRange hrange hc hmass hK hD hcoarseRate hcoarse]
  unfold cmp99SourcePi4ComplexBlockAdjointMatrix
  rw [← cmp99PhysicalRectangularComplexMatrix_eq_endomorphismMatrix,
    ← cmp99PhysicalRectangularComplexMatrix_eq_endomorphismMatrix,
    ← cmp99PhysicalRectangularComplexMatrix_comp,
    ← cmp99PhysicalRectangularComplexMatrix_comp]
  congr 1
  unfold cmp99SourcePi4WeakenedPhysicalH
    cmp99SourcePi4WeakenedBackgroundMinimizer
  rw [cmp116SourcePi4FullWeakenedCovariance_one_eq_exact
    anchor K hsourceRange hrange hc hmass hK hD]
  apply ContinuousLinearMap.ext
  intro x
  simp [ContinuousLinearMap.comp_apply]

/-- Interacting Wilson specialization: full complex coupling recovers the
canonical rectangular matrix of the physical CMP99 minimizer itself. -/
theorem
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_one_eq_physicalH
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (anchor : FinBox 4 Q)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange
      (interactingPhysicalBasePrecisionCLM U a) physicalBondDist R)
    (hmass : 0 < mass)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (interactingPhysicalBasePrecisionCLM U a)
          cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          (sub_pos.mpr hbudget) hmass
          (isCoerciveCLM_interactingPhysicalBasePrecision
            U ha hP hε hsmall)‖ < 1)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) (fun _ => 1)) coarseRate) :
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) (fun _ => 1) =
      cmp99PhysicalRectangularComplexMatrix
        (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget) := by
  rw [
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_one_eq_weakenedPhysicalH
      anchor (interactingPhysicalBasePrecisionCLM U a)
      hsourceRange hrange (sub_pos.mpr hbudget) hmass
      (isCoerciveCLM_interactingPhysicalBasePrecision
        U ha hP hε hsmall) hD hcoarseRate hcoarse,
    cmp99SourcePi4WeakenedPhysicalH_one_eq_physicalH
      U ha hP hε hsmall hbudget anchor hsourceRange hrange hmass hD
      hcoarseRate hcoarse]

end

end YangMills.RG

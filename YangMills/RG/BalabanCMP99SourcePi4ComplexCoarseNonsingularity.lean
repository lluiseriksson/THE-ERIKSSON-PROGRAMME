/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4ComplexRectangularMinimizer

/-!
# Nonsingularity of the complex CMP99 coarse middle

The fine contour covariance is not itself the CMP99 minimizer.  The
rectangular minimizer additionally requires the inverse of the literal
coarse middle

`M(σ) = Q C(σ) Q*`.

This file proves the exact finite-dimensional inverse bridge.  At full
coupling, the inverse of `M(1)` is the coordinate matrix of the
coercivity-generated coarse covariance.  Consequently the usual relative
Neumann condition is applied to the actual coarse middle, rather than to a
renamed abstract matrix.
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

/-- The full-coupling complex coarse middle is the canonical coordinate
matrix of the real weakened coarse middle at full coupling. -/
theorem cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_eq_weakened
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
          hc hmass hK‖ < 1) :
    cmp99SourcePi4FullComplexCoarseMiddleMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1) =
      cmp116PhysicalEndomorphismComplexMatrix
        (cmp99SourcePi4WeakenedCoarseMiddle
          (R := R) anchor K hc hmass hK (fun _ => 1)) := by
  rw [cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_eq_exact
    anchor K hsourceRange hrange hc hmass hK hD]
  rw [cmp99SourcePi4WeakenedCoarseMiddle_one_eq_exact
    anchor K hsourceRange hrange hc hmass hK hD]

/-- The base coarse middle followed by the generated coarse covariance is
the identity in canonical complex coordinates. -/
theorem
    cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_mul_coarseCovariance_eq_one
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
    cmp99SourcePi4FullComplexCoarseMiddleMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) *
        cmp116PhysicalEndomorphismComplexMatrix
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse) =
      1 := by
  rw [cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_eq_weakened
    anchor K hsourceRange hrange hc hmass hK hD]
  rw [← cmp116PhysicalEndomorphismComplexMatrix_comp,
    cmp99SourcePi4WeakenedCoarseMiddle_comp_covariance
      anchor K hc hmass hK (fun _ => 1) hcoarseRate hcoarse]
  exact cmp116PhysicalEndomorphismComplexMatrix_id

/-- The base coarse middle is nonsingular, derived from its physical right
inverse. -/
theorem cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_det_ne_zero
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
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix
      (R := R) anchor K hc hmass hK (fun _ => 1)).det ≠ 0 := by
  exact Matrix.det_ne_zero_of_mul_eq_one _ _
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_mul_coarseCovariance_eq_one
      anchor K hsourceRange hrange hc hmass hK hD hcoarseRate hcoarse)

/-- The nonsingular inverse of the base coarse middle is literally the
generated physical coarse covariance matrix. -/
theorem cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_inv_eq_coarseCovariance
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
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1))⁻¹ =
      cmp116PhysicalEndomorphismComplexMatrix
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse) := by
  exact nonsingInv_eq_covariance_of_mul_eq_one _ _
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_det_ne_zero
      anchor K hsourceRange hrange hc hmass hK hD hcoarseRate hcoarse)
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_mul_coarseCovariance_eq_one
      anchor K hsourceRange hrange hc hmass hK hD hcoarseRate hcoarse)

/-- A small literal relative defect makes the actual contour coarse middle
nonsingular. -/
theorem cmp99SourcePi4FullComplexCoarseMiddleMatrix_det_ne_zero
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
        (R := R) anchor K hc hmass hK (fun _ => 1)) coarseRate)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hsmall :
      ‖cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
        (R := R) anchor K hc hmass hK
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        sigma‖ < 1) :
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix
      (R := R) anchor K hc hmass hK sigma).det ≠ 0 := by
  let base :=
    cmp99SourcePi4FullComplexCoarseMiddleMatrix
      (R := R) anchor K hc hmass hK (fun _ => 1)
  let target :=
    cmp99SourcePi4FullComplexCoarseMiddleMatrix
      (R := R) anchor K hc hmass hK sigma
  apply det_ne_zero_of_nonsingInv_mul_sub_norm_lt_one
    base target
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_det_ne_zero
      anchor K hsourceRange hrange hc hmass hK hD hcoarseRate hcoarse)
  rw [cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_inv_eq_coarseCovariance
    anchor K hsourceRange hrange hc hmass hK hD hcoarseRate hcoarse]
  simpa [cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect,
    base, target] using hsmall

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexR1
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Neumann norm control of the literal source-complex precision and `R2`

The complete contour precision is not left as an unbounded inverse.  If

`E = K0 (C_sigma - C0)` and `||E|| < 1`,

then the exact factorization `C_sigma = C0 (1 + E)` gives

`K_sigma = (1 + E)⁻¹ K0`.

The geometric series therefore supplies the explicit norm bound with
denominator `1 - ||E||`, and the literal source identity for `R2` gives its
corresponding quantitative estimate.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

/-- The inverse of a near-identity matrix has the geometric-series norm
bound in the `L∞` operator norm. -/
theorem Matrix.linfty_opNorm_inv_one_add_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Matrix ι ι ℂ) (hE : ‖E‖ < 1) :
    ‖(1 + E)⁻¹‖ ≤ (1 - ‖E‖)⁻¹ := by
  have hneg : ‖-E‖ < 1 := by simpa using hE
  rw [Matrix.nonsing_inv_eq_ringInverse]
  have hgeom := tsum_geometric_le_of_norm_lt_one (-E) hneg
  rw [geom_series_eq_inverse (-E) hneg] at hgeom
  simpa using hgeom

/-- Exact inverse factorization from a physical right inverse at the base
point and a near-identity relative covariance defect. -/
theorem Matrix.inv_eq_inv_one_add_relative_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C0 C1 P0 : Matrix ι ι ℂ)
    (hbaseRight : C0 * P0 = 1)
    (hrel : ‖P0 * (C1 - C0)‖ < 1) :
    C1⁻¹ = (1 + P0 * (C1 - C0))⁻¹ * P0 := by
  let E := P0 * (C1 - C0)
  have hneg : ‖-E‖ < 1 := by simpa [E] using hrel
  have hunit : IsUnit (1 + E) := by
    simpa only [sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one hneg)
  have hone : (1 + E) * (1 + E)⁻¹ = 1 := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    exact Ring.mul_inverse_cancel _ hunit
  have hfactor : C1 = C0 * (1 + E) := by
    dsimp [E]
    calc
      C1 = C0 + (C1 - C0) := by abel
      _ = C0 + (C0 * P0) * (C1 - C0) := by rw [hbaseRight, one_mul]
      _ = C0 * (1 + P0 * (C1 - C0)) := by noncomm_ring
  apply Matrix.inv_eq_right_inv
  change C1 * ((1 + E)⁻¹ * P0) = 1
  rw [hfactor]
  calc
    (C0 * (1 + E)) * ((1 + E)⁻¹ * P0) =
        C0 * (((1 + E) * (1 + E)⁻¹) * P0) := by
      noncomm_ring
    _ = C0 * P0 := by rw [hone, one_mul]
    _ = 1 := hbaseRight

/-- Quantitative consequence of the exact relative inverse factorization. -/
theorem Matrix.linfty_opNorm_inv_le_of_right_relative
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C0 C1 P0 : Matrix ι ι ℂ)
    (hbaseRight : C0 * P0 = 1)
    (hrel : ‖P0 * (C1 - C0)‖ < 1) :
    ‖C1⁻¹‖ ≤
      (1 - ‖P0 * (C1 - C0)‖)⁻¹ * ‖P0‖ := by
  rw [Matrix.inv_eq_inv_one_add_relative_mul C0 C1 P0 hbaseRight hrel]
  exact
    (Matrix.linfty_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right
        (Matrix.linfty_opNorm_inv_one_add_le
          (P0 * (C1 - C0)) hrel)
        (norm_nonneg P0))

/-- The corresponding correction `P0 - C1⁻¹` is bounded without an
independent contour-precision norm. -/
theorem Matrix.linfty_opNorm_base_sub_inv_le_of_right_relative
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C0 C1 P0 : Matrix ι ι ℂ)
    (hbaseRight : C0 * P0 = 1)
    (hrel : ‖P0 * (C1 - C0)‖ < 1) :
    ‖P0 - C1⁻¹‖ ≤
      ((1 - ‖P0 * (C1 - C0)‖)⁻¹ * ‖P0‖) *
        ‖C1 - C0‖ * ‖P0‖ := by
  have htargetLeft : C1⁻¹ * C1 = 1 := by
    have hneg : ‖-(P0 * (C1 - C0))‖ < 1 := by simpa using hrel
    have hunitRel : IsUnit (1 + P0 * (C1 - C0)) := by
      simpa only [sub_neg_eq_add] using
        (isUnit_one_sub_of_norm_lt_one hneg)
    have hfactor : C1 = C0 * (1 + P0 * (C1 - C0)) := by
      calc
        C1 = C0 + (C1 - C0) := by abel
        _ = C0 + (C0 * P0) * (C1 - C0) := by rw [hbaseRight, one_mul]
        _ = C0 * (1 + P0 * (C1 - C0)) := by noncomm_ring
    have hunitC0 : IsUnit C0 := by
      exact IsUnit.of_mul_eq_one P0 hbaseRight
    have hunitC1 : IsUnit C1 := by
      rw [hfactor]
      exact hunitC0.mul hunitRel
    exact Matrix.nonsing_inv_mul C1
      ((Matrix.isUnit_iff_isUnit_det C1).mp hunitC1)
  rw [Matrix.sub_eq_leftInv_mul_sub_mul_of_inverse_laws
    P0 C1⁻¹ C0 C1 hbaseRight htargetLeft]
  calc
    ‖C1⁻¹ * (C1 - C0) * P0‖ ≤
        (‖C1⁻¹‖ * ‖C1 - C0‖) * ‖P0‖ := by
      exact
        (Matrix.linfty_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right
            (Matrix.linfty_opNorm_mul _ _)
            (norm_nonneg P0))
    _ ≤
        (((1 - ‖P0 * (C1 - C0)‖)⁻¹ * ‖P0‖) *
          ‖C1 - C0‖) * ‖P0‖ := by
      gcongr
      exact Matrix.linfty_opNorm_inv_le_of_right_relative
        C0 C1 P0 hbaseRight hrel

/-- Column-norm version of the relative inverse estimate.  It is obtained
by applying the row estimate to the transposed matrices.  The relative
smallness is correspondingly the physical left defect after transposition. -/
theorem Matrix.linfty_opNorm_transpose_inv_le_of_left_relative
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C0 C1 P0 : Matrix ι ι ℂ)
    (hbaseLeft : P0 * C0 = 1)
    (hrel :
      ‖P0.transpose * (C1 - C0).transpose‖ < 1) :
    ‖(C1⁻¹).transpose‖ ≤
      (1 - ‖P0.transpose * (C1 - C0).transpose‖)⁻¹ *
        ‖P0.transpose‖ := by
  have hbaseRightTranspose :
      C0.transpose * P0.transpose = 1 := by
    rw [← Matrix.transpose_mul, hbaseLeft, Matrix.transpose_one]
  have hraw :=
    Matrix.linfty_opNorm_inv_le_of_right_relative
      C0.transpose C1.transpose P0.transpose
      hbaseRightTranspose
      (by simpa only [Matrix.transpose_sub] using hrel)
  simpa only [Matrix.transpose_sub, ← Matrix.transpose_nonsing_inv] using hraw

/-- Column-norm correction estimate.  As in the inverse estimate above, the
full defect dependence is retained and no ambient dimension appears. -/
theorem Matrix.linfty_opNorm_transpose_base_sub_inv_le_of_left_relative
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C0 C1 P0 : Matrix ι ι ℂ)
    (hbaseLeft : P0 * C0 = 1)
    (hrel :
      ‖P0.transpose * (C1 - C0).transpose‖ < 1) :
    ‖(P0 - C1⁻¹).transpose‖ ≤
      ((1 - ‖P0.transpose * (C1 - C0).transpose‖)⁻¹ *
          ‖P0.transpose‖) *
        ‖(C1 - C0).transpose‖ * ‖P0.transpose‖ := by
  have hbaseRightTranspose :
      C0.transpose * P0.transpose = 1 := by
    rw [← Matrix.transpose_mul, hbaseLeft, Matrix.transpose_one]
  have hraw :=
    Matrix.linfty_opNorm_base_sub_inv_le_of_right_relative
      C0.transpose C1.transpose P0.transpose
      hbaseRightTranspose
      (by simpa only [Matrix.transpose_sub] using hrel)
  simpa only [Matrix.transpose_sub, ← Matrix.transpose_nonsing_inv] using hraw

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Source-specific precision bound from the exact fully coupled inverse and
the actual relative contour defect. -/
theorem linfty_opNorm_cmp116SourcePi4FullComplexWeakenedPrecisionMatrix_le
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
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
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hrel :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK sigma‖ < 1) :
    ‖cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
        (R := R) anchor K hc hmass hK sigma‖ ≤
      (1 -
        ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
          (R := R) anchor K hc hmass hK sigma‖)⁻¹ *
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖ := by
  let C0 :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK (fun _ => 1)
  let C1 :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma
  let P0 := cmp116PhysicalEndomorphismComplexMatrix K
  have hbaseInv :
      P0 * C0 = 1 := by
    dsimp [P0, C0]
    rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD]
    exact
      cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
        K hc hmass hK hD
  have hbaseDet : C0.det ≠ 0 := by
    dsimp [C0]
    exact
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_det_ne_zero
        anchor K hsourceRange hrange hc hmass hK hD
  have hbaseRight : C0 * P0 = 1 := by
    have hPinv : C0⁻¹ = P0 := Matrix.inv_eq_left_inv hbaseInv
    rw [← hPinv]
    exact Matrix.mul_nonsing_inv C0 (isUnit_iff_ne_zero.mpr hbaseDet)
  have hrel' : ‖P0 * (C1 - C0)‖ < 1 := by
    simpa [P0, C0, C1,
      cmp116SourcePi4FullComplexRelativeCovarianceDefect] using hrel
  change ‖C1⁻¹‖ ≤ (1 - ‖P0 * (C1 - C0)‖)⁻¹ * ‖P0‖
  exact Matrix.linfty_opNorm_inv_le_of_right_relative
    C0 C1 P0 hbaseRight hrel'

/-- Literal source `R2` bound with no independent contour-precision norm. -/
theorem linfty_opNorm_cmp116SourcePi4FullComplexR2Matrix_le
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
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
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hrel :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK sigma‖ < 1) :
    ‖cmp116SourcePi4FullComplexR2Matrix
        (R := R) anchor K hc hmass hK sigma‖ ≤
      ((1 -
        ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
          (R := R) anchor K hc hmass hK sigma‖)⁻¹ *
          ‖cmp116PhysicalEndomorphismComplexMatrix K‖) *
        ‖cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK sigma -
          cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK (fun _ => 1)‖ *
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖ := by
  let C0 :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK (fun _ => 1)
  let C1 :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma
  let P0 := cmp116PhysicalEndomorphismComplexMatrix K
  have hbaseInv : P0 * C0 = 1 := by
    dsimp [P0, C0]
    rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD]
    exact
      cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
        K hc hmass hK hD
  have hbaseDet : C0.det ≠ 0 := by
    dsimp [C0]
    exact
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_det_ne_zero
        anchor K hsourceRange hrange hc hmass hK hD
  have hbaseRight : C0 * P0 = 1 := by
    have hPinv : C0⁻¹ = P0 := Matrix.inv_eq_left_inv hbaseInv
    rw [← hPinv]
    exact Matrix.mul_nonsing_inv C0 (isUnit_iff_ne_zero.mpr hbaseDet)
  have hrel' : ‖P0 * (C1 - C0)‖ < 1 := by
    simpa [P0, C0, C1,
      cmp116SourcePi4FullComplexRelativeCovarianceDefect] using hrel
  change ‖P0 - C1⁻¹‖ ≤
    ((1 - ‖P0 * (C1 - C0)‖)⁻¹ * ‖P0‖) *
      ‖C1 - C0‖ * ‖P0‖
  exact Matrix.linfty_opNorm_base_sub_inv_le_of_right_relative
    C0 C1 P0 hbaseRight hrel'

/-- Literal source `R2` column bound from the transposed relative covariance
defect.  This is the missing orientation needed by the bilateral `R3/R1`
budget. -/
theorem linfty_opNorm_transpose_cmp116SourcePi4FullComplexR2Matrix_le
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
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
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hrelTranspose :
      ‖(cmp116PhysicalEndomorphismComplexMatrix K).transpose *
        (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK sigma -
            cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK (fun _ => 1)).transpose‖ < 1) :
    ‖(cmp116SourcePi4FullComplexR2Matrix
        (R := R) anchor K hc hmass hK sigma).transpose‖ ≤
      ((1 -
          ‖(cmp116PhysicalEndomorphismComplexMatrix K).transpose *
            (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
                  (R := R) anchor K hc hmass hK sigma -
                cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
                  (R := R) anchor K hc hmass hK (fun _ => 1)).transpose‖)⁻¹ *
          ‖(cmp116PhysicalEndomorphismComplexMatrix K).transpose‖) *
        ‖(cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK sigma -
            cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK (fun _ => 1)).transpose‖ *
        ‖(cmp116PhysicalEndomorphismComplexMatrix K).transpose‖ := by
  let C0 :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK (fun _ => 1)
  let C1 :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma
  let P0 := cmp116PhysicalEndomorphismComplexMatrix K
  have hbaseLeft : P0 * C0 = 1 := by
    dsimp [P0, C0]
    rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD]
    exact
      cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
        K hc hmass hK hD
  change ‖(P0 - C1⁻¹).transpose‖ ≤
    ((1 - ‖P0.transpose * (C1 - C0).transpose‖)⁻¹ *
        ‖P0.transpose‖) *
      ‖(C1 - C0).transpose‖ * ‖P0.transpose‖
  exact
    Matrix.linfty_opNorm_transpose_base_sub_inv_le_of_left_relative
      C0 C1 P0 hbaseLeft (by simpa [P0, C0, C1] using hrelTranspose)

end

end YangMills.RG

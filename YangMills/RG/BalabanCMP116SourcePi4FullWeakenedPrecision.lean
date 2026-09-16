/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullWeakenedCovariance

/-!
# Precision of the complete source `Pi^4` weakened covariance

The full source covariance constructed upstream is a real physical
endomorphism for every real weakening field.  This file transports it to the
canonical finite CMP116 matrix and defines its precision by the
nonsingular-matrix inverse.

No invertibility is silently asserted away from the fully coupled point:
the inverse identities at a general weakening field explicitly require a
nonzero determinant.  At `s = 1`, nonsingularity is derived from the exact
physical right-inverse theorem, and the weakened precision is proved
literally equal to the original physical precision matrix.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Canonical finite matrix of the complete real weakened covariance. -/
noncomputable def cmp116SourcePi4FullWeakenedCovarianceMatrix
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix
    (cmp116SourcePi4FullWeakenedCovariance
      (R := R) anchor K hc hmass hK s)

/-- The finite weakened precision.  Its inverse laws are exposed only under
the actual nonsingularity condition. -/
noncomputable def cmp116SourcePi4FullWeakenedPrecisionMatrix
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  (cmp116SourcePi4FullWeakenedCovarianceMatrix
    (R := R) anchor K hc hmass hK s)⁻¹

/-- A nonzero weakened covariance determinant gives the left inverse law. -/
theorem cmp116SourcePi4_fullWeakenedPrecision_mul_covariance_eq_one
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (hdet :
      (cmp116SourcePi4FullWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK s).det ≠ 0) :
    cmp116SourcePi4FullWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK s *
        cmp116SourcePi4FullWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK s =
      1 := by
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr hdet)

/-- At full coupling the covariance matrix is the exact quotient-safe
physical covariance matrix. -/
theorem cmp116SourcePi4FullWeakenedCovarianceMatrix_one_eq_exact
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
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
          hc hmass hK‖ < 1) :
    cmp116SourcePi4FullWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1) =
      cmp116PhysicalEndomorphismComplexMatrix
        (cmp116SourcePi4QuotientExactPatchedCovariance
          K hc hmass hK) := by
  rw [cmp116SourcePi4FullWeakenedCovarianceMatrix,
    cmp116SourcePi4FullWeakenedCovariance_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD]

/-- Full coupling is nonsingular as a consequence of the physical
precision--covariance identity. -/
theorem cmp116SourcePi4FullWeakenedCovarianceMatrix_one_det_ne_zero
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
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
          hc hmass hK‖ < 1) :
    (cmp116SourcePi4FullWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK (fun _ => 1)).det ≠ 0 := by
  have hinv :
      cmp116PhysicalEndomorphismComplexMatrix K *
          cmp116SourcePi4FullWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK (fun _ => 1) =
        1 :=
    cmp116SourcePi4_precision_mul_fullWeakenedCovarianceMatrix_one_eq_one
      anchor K hsourceRange hrange hc hmass hK hD
  intro hzero
  have hdet := congrArg Matrix.det hinv
  rw [Matrix.det_mul, hzero, mul_zero, Matrix.det_one] at hdet
  exact zero_ne_one hdet

/-- The complete weakened precision recovers the original physical precision
matrix at full coupling. -/
theorem cmp116SourcePi4FullWeakenedPrecisionMatrix_one_eq_physical
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
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
          hc hmass hK‖ < 1) :
    cmp116SourcePi4FullWeakenedPrecisionMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1) =
      cmp116PhysicalEndomorphismComplexMatrix K := by
  rw [cmp116SourcePi4FullWeakenedPrecisionMatrix,
    cmp116SourcePi4FullWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD]
  exact Matrix.inv_eq_left_inv
    (cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
      K hc hmass hK hD)

end

end YangMills.RG

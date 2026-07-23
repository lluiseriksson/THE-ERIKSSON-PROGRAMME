/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexWeakenedCovariance

/-!
# Precision of the complete complex source covariance

The contour precision is the nonsingular inverse of the complete
length-ordered complex covariance matrix.  The definition itself does not
claim invertibility at arbitrary complex weakening parameters.  Every inverse
law retains the determinant condition, while full coupling is proved
nonsingular from the physical precision--covariance identity.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Complete complex source precision matrix. -/
noncomputable def cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
    (R := R) anchor K hc hmass hK sigma)⁻¹

/-- Nonsingularity gives the precision--covariance inverse law. -/
theorem cmp116SourcePi4_fullComplexWeakenedPrecision_mul_covariance_eq_one
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hdet :
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma).det ≠ 0) :
    cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK sigma *
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma =
      1 := by
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr hdet)

/-- Full coupling is nonsingular, derived from the exact physical inverse. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_det_ne_zero
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
          hc hmass hK‖ < 1) :
    (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK (fun _ => 1)).det ≠ 0 := by
  rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
    anchor K hsourceRange hrange hc hmass hK hD]
  intro hzero
  have hinv :=
    cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
      K hc hmass hK hD
  have hdet := congrArg Matrix.det hinv
  rw [Matrix.det_mul, hzero, mul_zero, Matrix.det_one] at hdet
  exact zero_ne_one hdet

/-- At full coupling the complex precision is the original physical
precision matrix. -/
theorem cmp116SourcePi4FullComplexWeakenedPrecisionMatrix_one_eq_physical
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
          hc hmass hK‖ < 1) :
    cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1) =
      cmp116PhysicalEndomorphismComplexMatrix K := by
  rw [cmp116SourcePi4FullComplexWeakenedPrecisionMatrix,
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD]
  exact Matrix.inv_eq_left_inv
    (cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
      K hc hmass hK hD)

end

end YangMills.RG

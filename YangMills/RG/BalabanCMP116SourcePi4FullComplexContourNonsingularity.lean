/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexWeakenedPrecision
import YangMills.RG.BalabanCMP116Eq214ContourRelativeNorm

/-!
# Nonsingularity criterion for the complete source contour

This file exposes the exact Neumann condition still required on the complex
source contour.  The base inverse is not an abstract algebraic matrix: at the
fully coupled point it is proved to be the original physical precision.

Consequently a bound on

`K_phys * (C(sigma) - C(1))`

directly yields nonsingularity of the complete complex covariance and the
precision--covariance inverse identity.  This is the quantitative condition
to be discharged from the source Cauchy/kernel estimates.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The physical relative contour defect of the complete covariance. -/
noncomputable def cmp116SourcePi4FullComplexRelativeCovarianceDefect
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) :=
  cmp116PhysicalEndomorphismComplexMatrix K *
    (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma -
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1))

/-- The complete contour covariance is nonsingular under its literal
physical relative-defect condition. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_det_ne_zero
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
    (hsmall :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK sigma‖ < 1) :
    (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma).det ≠ 0 := by
  let base :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK (fun _ => 1)
  let target :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma
  have hbase :
      cmp116PhysicalEndomorphismComplexMatrix K * base = 1 := by
    change cmp116PhysicalEndomorphismComplexMatrix K *
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) = 1
    rw [
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
        anchor K hsourceRange hrange hc hmass hK hD]
    exact
      cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
        K hc hmass hK hD
  have hbaseDet : base.det ≠ 0 := by
    intro hzero
    have hdet := congrArg Matrix.det hbase
    rw [Matrix.det_mul, hzero, mul_zero, Matrix.det_one] at hdet
    exact zero_ne_one hdet
  have hbaseInv :
      base⁻¹ = cmp116PhysicalEndomorphismComplexMatrix K :=
    Matrix.inv_eq_left_inv hbase
  change target.det ≠ 0
  apply det_ne_zero_of_nonsingInv_mul_sub_norm_lt_one
    base target hbaseDet
  rw [hbaseInv]
  simpa [cmp116SourcePi4FullComplexRelativeCovarianceDefect,
    base, target] using hsmall

/-- The complete complex precision is an actual left inverse throughout any
contour satisfying the physical relative-defect condition. -/
theorem cmp116SourcePi4_fullComplexPrecision_mul_covariance_eq_one_of_relativeDefect
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
    (hsmall :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK sigma‖ < 1) :
    cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK sigma *
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma =
      1 := by
  exact
    cmp116SourcePi4_fullComplexWeakenedPrecision_mul_covariance_eq_one
      anchor K hc hmass hK sigma
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_det_ne_zero
        anchor K hsourceRange hrange hc hmass hK hD sigma hsmall)

end

end YangMills.RG

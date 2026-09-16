/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214ContourDeterminantRatio
import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalContourDensity

/-!
# Relative determinant identity on the restricted physical contour

This file specializes the exact relative determinant identity to the source
`Pi⁴` covariance whose complex weakening varies only on the physical contour
carrier.  It does not infer a rank bound from that restriction: propagation
through the covariance remains visible in the literal relative defect.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The restricted-contour determinant density is exactly the inverse square
root, in its fixed logarithmic branch, of the physical relative covariance
determinant. -/
theorem cmp116SourceRestrictedContour_logDetDensity_sq_mul_relativeDet_eq_one
    {nDelta M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (z : Fin nDelta → ℂ)
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
    (hsmall :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e z)‖ < 1) :
    cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e z)) ^ 2 *
      (1 +
        cmp116SourcePi4FullComplexRelativeCovarianceDefect
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e z)).det =
      1 := by
  let sigma :=
    cmp116SourceRestrictedShiftedCoupling contourCarrier e z
  let baseCovariance :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK (fun _ => 1)
  let contourCovariance :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma
  let contourPrecision :=
    cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
      (R := R) anchor K hc hmass hK sigma
  have hbase :
      cmp116PhysicalEndomorphismComplexMatrix K * baseCovariance = 1 := by
    dsimp [baseCovariance]
    rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD]
    exact
      cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
        K hc hmass hK hD
  have hcontour : contourPrecision * contourCovariance = 1 := by
    exact
      cmp116SourcePi4_fullComplexPrecision_mul_covariance_eq_one_of_relativeDefect
        anchor K hsourceRange hrange hc hmass hK hD sigma hsmall
  have hratio :=
    cmp116Eq214LogDeterminantDensity_sq_mul_det_one_add_relativeDefect
      (cmp116PhysicalEndomorphismComplexMatrix K)
      contourPrecision baseCovariance contourCovariance hbase hcontour
  simpa [sigma, baseCovariance, contourCovariance, contourPrecision,
    cmp116SourcePi4FullComplexRelativeCovarianceDefect] using hratio

/-- Source-facing Weinstein--Aronszajn reduction.  Once a physical first-hit
construction factors the literal relative covariance defect through `κ`, the
logarithmic density is normalized by a determinant on `κ`, not on the ambient
walk-coordinate space. -/
theorem cmp116SourceRestrictedContour_logDetDensity_sq_mul_reducedDet_eq_one
    {nDelta M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (z : Fin nDelta → ℂ)
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
    (hsmall :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e z)‖ < 1)
    (A : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) κ ℂ)
    (B : Matrix κ
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (hfactor :
      cmp116SourcePi4FullComplexRelativeCovarianceDefect
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling contourCarrier e z) =
        A * B) :
    cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e z)) ^ 2 *
      (1 + B * A).det =
      1 := by
  have h :=
    cmp116SourceRestrictedContour_logDetDensity_sq_mul_relativeDet_eq_one
      anchor contourCarrier e z K hsourceRange hrange hc hmass hK hD hsmall
  rw [hfactor, Matrix.det_one_add_mul_comm A B] at h
  exact h

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214LogDeterminantDensity

/-!
# The exact relative determinant behind the CMP116 contour density

The complex contour covariance need not have finite-range inverse and its
defect need not have bilateral finite support.  The source-faithful algebraic
object is instead the relative covariance defect

`D = K₀ * (Cσ - C₀)`.

Whenever `K₀ C₀ = 1`, the determinant factors exactly through `1 + D`.
Combining this with the logarithmic determinant density gives

`density² * det (1 + D) = 1`.

No rank, locality, trace, or quantitative determinant estimate is asserted
here.
-/

namespace YangMills.RG

noncomputable section

/-- Exact determinant factorization through the relative covariance defect. -/
theorem det_targetCovariance_eq_det_baseCovariance_mul_det_one_add_relativeDefect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basePrecision baseCovariance targetCovariance : Matrix ι ι ℂ)
    (hbase : basePrecision * baseCovariance = 1) :
    targetCovariance.det =
      baseCovariance.det *
        (1 + basePrecision * (targetCovariance - baseCovariance)).det := by
  have hrelative :
      1 + basePrecision * (targetCovariance - baseCovariance) =
        basePrecision * targetCovariance := by
    calc
      1 + basePrecision * (targetCovariance - baseCovariance) =
          basePrecision * baseCovariance +
            basePrecision * (targetCovariance - baseCovariance) := by
              rw [hbase]
      _ = basePrecision * targetCovariance := by
        rw [Matrix.mul_sub]
        abel
  have hdetbase :
      basePrecision.det * baseCovariance.det = 1 := by
    have h := congrArg Matrix.det hbase
    simpa [Matrix.det_mul] using h
  rw [hrelative, Matrix.det_mul]
  calc
    targetCovariance.det =
        1 * targetCovariance.det := by rw [one_mul]
    _ = (baseCovariance.det * basePrecision.det) *
          targetCovariance.det := by
      rw [mul_comm baseCovariance.det basePrecision.det, hdetbase]
    _ = baseCovariance.det *
          (basePrecision.det * targetCovariance.det) := by ring

/-- The logarithmic determinant density is the inverse square root of the
literal relative covariance determinant, expressed without choosing another
square-root branch. -/
theorem cmp116Eq214LogDeterminantDensity_sq_mul_det_one_add_relativeDefect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basePrecision contourPrecision baseCovariance contourCovariance :
      Matrix ι ι ℂ)
    (hbase : basePrecision * baseCovariance = 1)
    (hcontour : contourPrecision * contourCovariance = 1) :
    cmp116Eq214LogDeterminantDensity basePrecision contourPrecision ^ 2 *
        (1 + basePrecision *
          (contourCovariance - baseCovariance)).det =
      1 := by
  have hbaseDet : basePrecision.det ≠ 0 := by
    intro hzero
    have h := congrArg Matrix.det hbase
    simp [Matrix.det_mul, hzero] at h
  have hcontourDet : contourPrecision.det ≠ 0 := by
    intro hzero
    have h := congrArg Matrix.det hcontour
    simp [Matrix.det_mul, hzero] at h
  have hbaseInv :
      basePrecision.det * baseCovariance.det = 1 := by
    have h := congrArg Matrix.det hbase
    simpa [Matrix.det_mul] using h
  have hcontourInv :
      contourPrecision.det * contourCovariance.det = 1 := by
    have h := congrArg Matrix.det hcontour
    simpa [Matrix.det_mul] using h
  have hdensity :=
    cmp116Eq214LogDeterminantDensity_sq_mul_base_det
      basePrecision contourPrecision hbaseDet hcontourDet
  have hfactor :=
    det_targetCovariance_eq_det_baseCovariance_mul_det_one_add_relativeDefect
      basePrecision baseCovariance contourCovariance hbase
  calc
    cmp116Eq214LogDeterminantDensity basePrecision contourPrecision ^ 2 *
          (1 + basePrecision *
            (contourCovariance - baseCovariance)).det =
        (cmp116Eq214LogDeterminantDensity
            basePrecision contourPrecision ^ 2 *
          (basePrecision.det * baseCovariance.det)) *
          (1 + basePrecision *
            (contourCovariance - baseCovariance)).det := by
              rw [hbaseInv, mul_one]
    _ = (cmp116Eq214LogDeterminantDensity
            basePrecision contourPrecision ^ 2 *
          basePrecision.det) *
        (baseCovariance.det *
          (1 + basePrecision *
            (contourCovariance - baseCovariance)).det) := by ring
    _ = contourPrecision.det * contourCovariance.det := by
      rw [hdensity, ← hfactor]
    _ = 1 := hcontourInv

/-- A source-constructed factorization of the relative defect through a
smaller intermediate coordinate type moves the determinant to that type by
Weinstein--Aronszajn.  The factorization itself remains an explicit equality;
this theorem does not infer it from a support slogan. -/
theorem cmp116Eq214LogDeterminantDensity_sq_mul_reducedDet_of_relativeDefect_eq_mul
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (basePrecision contourPrecision baseCovariance contourCovariance :
      Matrix ι ι ℂ)
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ)
    (hbase : basePrecision * baseCovariance = 1)
    (hcontour : contourPrecision * contourCovariance = 1)
    (hfactor :
      basePrecision * (contourCovariance - baseCovariance) = A * B) :
    cmp116Eq214LogDeterminantDensity basePrecision contourPrecision ^ 2 *
        (1 + B * A).det =
      1 := by
  have h :=
    cmp116Eq214LogDeterminantDensity_sq_mul_det_one_add_relativeDefect
      basePrecision contourPrecision baseCovariance contourCovariance
      hbase hcontour
  rw [hfactor, Matrix.det_one_add_mul_comm A B] at h
  exact h

end

end YangMills.RG

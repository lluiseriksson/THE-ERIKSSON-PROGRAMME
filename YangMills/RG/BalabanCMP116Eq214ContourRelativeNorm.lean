/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214LogDeterminantDensity
import YangMills.RG.BalabanCMP116ComplexPhysicalWalkMatrix
import YangMills.RG.BalabanCMP99PatchedParametrixGeometricWeightedDecay

/-!
# Row-sum producers for the CMP116 contour Neumann criterion

The physical complex-kernel estimates are entrywise and volume-uniform.  The
determinant argument consumes the `L∞` operator norm of the relative precision
defect.  This module provides the exact finite-dimensional bridge:

* a uniform absolute row-sum bound controls the matrix `L∞` operator norm;
* separate bounds on the base inverse and contour defect imply the relative
  Neumann smallness condition.

Neither theorem receives invertibility of the contour matrix.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

/-- A literal right inverse of a finite square matrix already proves that its
determinant is nonzero.  This removes a redundant base-nonsingularity premise
from the source contour installer. -/
theorem Matrix.det_ne_zero_of_mul_eq_one
    {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing 𝕜] [Nontrivial 𝕜]
    (A B : Matrix ι ι 𝕜) (hAB : A * B = 1) :
    A.det ≠ 0 := by
  have hdet : A.det * B.det = 1 := by
    rw [← Matrix.det_mul, hAB, Matrix.det_one]
  intro hzero
  rw [hzero, zero_mul] at hdet
  exact zero_ne_one hdet

/-- A uniform absolute row-sum estimate controls the matrix `L∞` operator
norm. -/
theorem Matrix.linfty_opNorm_le_of_row_sum_le
    {ι κ 𝕜 : Type*}
    [Fintype ι] [Fintype κ]
    [Nonempty ι]
    [SeminormedAddCommGroup 𝕜]
    (A : Matrix ι κ 𝕜) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ bound) :
    ‖A‖ ≤ bound := by
  let boundNN : NNReal := ⟨bound, hbound⟩
  have hsup :
      (Finset.univ : Finset ι).sup
          (fun i => ∑ j : κ, ‖A i j‖₊) ≤ boundNN := by
    apply Finset.sup_le
    intro i _
    change (∑ j : κ, ‖A i j‖₊).1 ≤ boundNN.1
    simpa [boundNN] using hrow i
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast hsup

/-- Entrywise domination by a nonnegative kernel, followed by a uniform
kernel row sum, controls the matrix `L∞` operator norm. -/
theorem Matrix.linfty_opNorm_le_of_entry_le_kernel
    {ι κ 𝕜 : Type*}
    [Fintype ι] [Fintype κ]
    [Nonempty ι]
    [SeminormedAddCommGroup 𝕜]
    (A : Matrix ι κ 𝕜)
    (kernel : ι → κ → ℝ) (amplitude rowMass : ℝ)
    (hamplitude : 0 ≤ amplitude)
    (hkernel : ∀ i j, 0 ≤ kernel i j)
    (hentry : ∀ i j, ‖A i j‖ ≤ amplitude * kernel i j)
    (hrowMass : ∀ i, ∑ j, kernel i j ≤ rowMass) :
    ‖A‖ ≤ amplitude * rowMass := by
  apply Matrix.linfty_opNorm_le_of_row_sum_le
  · exact mul_nonneg hamplitude
      ((Finset.sum_nonneg fun j _ =>
        hkernel (Classical.choice (inferInstance : Nonempty ι)) j).trans
        (hrowMass (Classical.choice (inferInstance : Nonempty ι))))
  · intro i
    calc
      ∑ j, ‖A i j‖ ≤ ∑ j, amplitude * kernel i j :=
        Finset.sum_le_sum fun j _ => hentry i j
      _ = amplitude * ∑ j, kernel i j := by
        rw [Finset.mul_sum]
      _ ≤ amplitude * rowMass :=
        mul_le_mul_of_nonneg_left (hrowMass i) hamplitude

/-- A fixed-rate entrywise estimate on physical bond--Lie coordinates gives
a volume-independent matrix `L∞` operator-norm bound.  The only finite
internal multiplicity is the literal Lie-coordinate count `Nc² - 1`. -/
theorem physicalWalkMatrix_linfty_opNorm_le_of_fixedRate
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (A : Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℂ)
    (amplitude rate : ℝ)
    (hamplitude : 0 ≤ amplitude)
    (hgeom : ((2 ^ d : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (hentry : ∀ row col,
      ‖A row col‖ ≤
        amplitude *
          Real.exp (-(rate *
            (physicalBondDist row.1 col.1 : ℝ)))) :
    ‖A‖ ≤
      amplitude *
        (((Nc ^ 2 - 1 : ℕ) : ℝ) *
          cmp99PhysicalBondGeometricRowSum d rate) := by
  apply Matrix.linfty_opNorm_le_of_entry_le_kernel
    A
    (fun row col =>
      Real.exp (-(rate *
        (physicalBondDist row.1 col.1 : ℝ))))
    amplitude
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum d rate)
    hamplitude
  · intro row col
    exact (Real.exp_pos _).le
  · exact hentry
  · intro row
    have hsum :
        (∑ source : PhysicalBond d N,
          Real.exp (-(rate *
            (physicalBondDist row.1 source : ℝ)))) ≤
          cmp99PhysicalBondGeometricRowSum d rate := by
      simpa only [physicalBondDist_comm] using
        (physicalBondDist_exp_sum_le_cmp99GeometricRowSum row.1 hgeom)
    calc
      ∑ col : CMP116PhysicalWalkCoordinate d N Nc,
          Real.exp (-(rate *
            (physicalBondDist row.1 col.1 : ℝ))) =
          ((Nc ^ 2 - 1 : ℕ) : ℝ) *
            ∑ source : PhysicalBond d N,
              Real.exp (-(rate *
                (physicalBondDist row.1 source : ℝ))) := by
            rw [Fintype.sum_prod_type, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro source _
            simp
      _ ≤ ((Nc ^ 2 - 1 : ℕ) : ℝ) *
          cmp99PhysicalBondGeometricRowSum d rate :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)

/-- Bounds on the inverse base precision and on the contour defect produce
the exact relative smallness condition used by the Neumann determinant
criterion. -/
theorem nonsingInv_mul_sub_norm_lt_one_of_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base contour : Matrix ι ι ℂ)
    (inverseBound defectBound : ℝ)
    (hinverse : ‖base⁻¹‖ ≤ inverseBound)
    (hdefect : ‖contour - base‖ ≤ defectBound)
    (hsmall : inverseBound * defectBound < 1) :
    ‖base⁻¹ * (contour - base)‖ < 1 := by
  calc
    ‖base⁻¹ * (contour - base)‖ ≤
        ‖base⁻¹‖ * ‖contour - base‖ :=
      Matrix.linfty_opNorm_mul _ _
    _ ≤ inverseBound * defectBound :=
      mul_le_mul hinverse hdefect (norm_nonneg _) (by
        exact (norm_nonneg _).trans hinverse)
    _ < 1 := hsmall

/-- A supplied physical covariance which is a right inverse of a nonsingular
base precision is literally the matrix nonsingular inverse. -/
theorem nonsingInv_eq_covariance_of_mul_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base covariance : Matrix ι ι ℂ)
    (hbase : base.det ≠ 0)
    (hcovariance : base * covariance = 1) :
    base⁻¹ = covariance := by
  have hbaseDetUnit : IsUnit base.det := isUnit_iff_ne_zero.mpr hbase
  calc
    base⁻¹ = base⁻¹ * 1 := by rw [mul_one]
    _ = base⁻¹ * (base * covariance) := by rw [hcovariance]
    _ = (base⁻¹ * base) * covariance := by rw [Matrix.mul_assoc]
    _ = covariance := by
      rw [Matrix.nonsing_inv_mul base hbaseDetUnit, one_mul]

/-- A physical covariance row bound and a contour-precision defect row bound
produce the Neumann smallness condition without exposing the algebraic
inverse as an independent analytic object. -/
theorem nonsingInv_mul_sub_norm_lt_one_of_covariance_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base contour covariance : Matrix ι ι ℂ)
    (covarianceBound defectBound : ℝ)
    (hbase : base.det ≠ 0)
    (hcovariance : base * covariance = 1)
    (hcovarianceBound : ‖covariance‖ ≤ covarianceBound)
    (hdefect : ‖contour - base‖ ≤ defectBound)
    (hsmall : covarianceBound * defectBound < 1) :
    ‖base⁻¹ * (contour - base)‖ < 1 := by
  apply nonsingInv_mul_sub_norm_lt_one_of_bounds
    base contour covarianceBound defectBound
  · simpa [nonsingInv_eq_covariance_of_mul_eq_one
      base covariance hbase hcovariance] using hcovarianceBound
  · exact hdefect
  · exact hsmall

end

end YangMills.RG

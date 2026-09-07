/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import YangMills.RG.BalabanCMP116Eq214PhysicalContourDensity

/-!
# The logarithmic determinant branch in CMP116 equation (2.14)

The Gaussian normalization is the square root of a determinant ratio.  An
arbitrary algebraic square root would destroy the analytic contour
interpretation.  We instead use the explicit logarithmic branch

`exp ((log det K₁ - log det K₀) / 2)`.

At the base point it is definitionally normalized to one.  Whenever both
determinants are nonzero its square times `det K₀` is exactly `det K₁`.
Analyticity on the physical contour will subsequently be obtained by keeping
the determinant image inside a source-certified logarithm domain.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

/-- Explicit logarithmic branch of the CMP116 determinant-density ratio. -/
def cmp116Eq214LogDeterminantDensity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base contour : Matrix ι ι ℂ) : ℂ :=
  Complex.exp ((Complex.log contour.det - Complex.log base.det) / 2)

/-- The logarithmic determinant density is exactly one at the base matrix. -/
@[simp]
theorem cmp116Eq214LogDeterminantDensity_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base : Matrix ι ι ℂ) :
    cmp116Eq214LogDeterminantDensity base base = 1 := by
  simp [cmp116Eq214LogDeterminantDensity]

/-- Exact determinant normalization on the non-singular physical contour. -/
theorem cmp116Eq214LogDeterminantDensity_sq_mul_base_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base contour : Matrix ι ι ℂ)
    (hbase : base.det ≠ 0) (hcontour : contour.det ≠ 0) :
    cmp116Eq214LogDeterminantDensity base contour ^ 2 * base.det =
      contour.det := by
  rw [cmp116Eq214LogDeterminantDensity, pow_two, ← Complex.exp_add]
  have hexp :
      Complex.exp
          ((Complex.log contour.det - Complex.log base.det) / 2 +
            (Complex.log contour.det - Complex.log base.det) / 2) =
        contour.det / base.det := by
    rw [show
      (Complex.log contour.det - Complex.log base.det) / 2 +
          (Complex.log contour.det - Complex.log base.det) / 2 =
        Complex.log contour.det - Complex.log base.det by ring]
    rw [Complex.exp_sub, Complex.exp_log hcontour, Complex.exp_log hbase]
  rw [hexp]
  exact div_mul_cancel₀ contour.det hbase

/-- A real positive-definite precision remains nonsingular after canonical
complexification.  This is the base-point producer for the determinant
density, obtained from physical coercivity rather than postulated directly. -/
theorem det_map_complexOfReal_ne_zero_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    (A.map Complex.ofRealHom).det ≠ 0 := by
  change (Complex.ofRealHom.mapMatrix A).det ≠ 0
  rw [← Complex.ofRealHom.map_det]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hA.det_pos)

/-- A contour precision is nonsingular when its relative perturbation from a
nonsingular base precision has `L∞` operator norm strictly below one.

This is the finite-dimensional Neumann criterion in the exact form needed by
the CMP116 contour: the hypothesis is quantitative and will be produced from
the physical complex-kernel row bounds, rather than supplied as a renamed
determinant assumption. -/
theorem det_ne_zero_of_nonsingInv_mul_sub_norm_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (base contour : Matrix ι ι ℂ)
    (hbase : base.det ≠ 0)
    (hsmall : ‖base⁻¹ * (contour - base)‖ < 1) :
    contour.det ≠ 0 := by
  have hbaseDetUnit : IsUnit base.det := isUnit_iff_ne_zero.mpr hbase
  have hbaseUnit : IsUnit base :=
    (Matrix.isUnit_iff_isUnit_det base).mpr hbaseDetUnit
  have hpertUnit :
      IsUnit (1 + base⁻¹ * (contour - base)) := by
    have hneg :
        ‖-(base⁻¹ * (contour - base))‖ < 1 := by
      simpa only [norm_neg] using hsmall
    simpa only [sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one hneg)
  have hfactor :
      base * (1 + base⁻¹ * (contour - base)) = contour := by
    rw [mul_add, mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hbaseDetUnit]
    abel
  have hcontourUnit : IsUnit contour := by
    rw [← hfactor]
    exact hbaseUnit.mul hpertUnit
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det contour).mp hcontourUnit)

end

end YangMills.RG

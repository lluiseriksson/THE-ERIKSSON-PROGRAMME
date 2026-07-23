/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
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

end

end YangMills.RG

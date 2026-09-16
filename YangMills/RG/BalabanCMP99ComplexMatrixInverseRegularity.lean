/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Entrywise regularity of a nonsingular complex matrix inverse

The rectangular CMP99 minimizer contains the inverse of the coarse middle
`M(σ) = Q C(σ) Q*`.  Matrix norms in Mathlib intentionally offer several
non-definitionally-equal topologies.  The contour development is already
entrywise, so this module proves the required inverse regularity directly
from the determinant-adjugate formula.  No inverse differentiability
hypothesis is introduced.
-/

namespace YangMills.RG

noncomputable section

/-- A finite determinant curve is differentiable when all of its entries
are differentiable. -/
theorem differentiableAt_complexMatrixDet_of_entrywise
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) (t : ℂ)
    (hentry : ∀ i j, DifferentiableAt ℂ (fun u => M u i j) t) :
    DifferentiableAt ℂ (fun u => (M u).det) t := by
  classical
  simp_rw [Matrix.det_apply']
  fun_prop

/-- Every entry of the adjugate curve is differentiable under the same
entrywise premise. -/
theorem differentiableAt_complexMatrixAdjugateEntry_of_entrywise
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) (t : ℂ)
    (hentry : ∀ i j, DifferentiableAt ℂ (fun u => M u i j) t)
    (row col : ι) :
    DifferentiableAt ℂ (fun u => (M u).adjugate row col) t := by
  classical
  simp_rw [Matrix.adjugate_apply]
  apply differentiableAt_complexMatrixDet_of_entrywise
  intro i j
  by_cases hij : i = col
  · subst i
    simp only [Matrix.updateRow_self]
    fun_prop
  · simpa [Matrix.updateRow_apply, hij] using hentry i j

/-- Over `ℂ`, the nonsingular inverse is globally the determinant inverse
times the adjugate, including at singular matrices where both sides use the
zero convention. -/
theorem complexMatrixNonsingInv_eq_detInv_smul_adjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    A⁻¹ = (A.det)⁻¹ • A.adjugate := by
  by_cases h : A.det = 0
  · rw [Matrix.nonsing_inv_apply_not_isUnit]
    · simp [h]
    · simpa [isUnit_iff_ne_zero, h]
  · rw [Matrix.nonsing_inv_apply
      (A := A) (isUnit_iff_ne_zero.mpr h)]
    simp [Units.val_inv_eq_inv_val]

/-- Every inverse entry is differentiable at a nonsingular point.  The
producer consumes only the entry derivatives of the original matrix curve
and the literal nonvanishing determinant. -/
theorem differentiableAt_complexMatrixNonsingInvEntry_of_entrywise
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) (t : ℂ)
    (hentry : ∀ i j, DifferentiableAt ℂ (fun u => M u i j) t)
    (hdet : (M t).det ≠ 0)
    (row col : ι) :
    DifferentiableAt ℂ (fun u => (M u)⁻¹ row col) t := by
  rw [show (fun u => (M u)⁻¹ row col) =
      fun u => ((M u).det)⁻¹ * (M u).adjugate row col by
    funext u
    rw [complexMatrixNonsingInv_eq_detInv_smul_adjugate (M u)]
    rfl]
  exact
    (differentiableAt_complexMatrixDet_of_entrywise M t hentry).inv hdet
      |>.mul
        (differentiableAt_complexMatrixAdjugateEntry_of_entrywise
          M t hentry row col)

/-- The canonical derivative of an inverse entry is produced rather than
received as an analytic premise. -/
theorem hasDerivAt_complexMatrixNonsingInvEntry_of_entrywise
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) (t : ℂ)
    (hentry : ∀ i j, DifferentiableAt ℂ (fun u => M u i j) t)
    (hdet : (M t).det ≠ 0)
    (row col : ι) :
    HasDerivAt (fun u => (M u)⁻¹ row col)
      (deriv (fun u => (M u)⁻¹ row col) t) t :=
  (differentiableAt_complexMatrixNonsingInvEntry_of_entrywise
    M t hentry hdet row col).hasDerivAt

end

end YangMills.RG

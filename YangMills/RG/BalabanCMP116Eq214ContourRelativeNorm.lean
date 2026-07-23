/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214LogDeterminantDensity

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

end

end YangMills.RG

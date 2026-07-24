/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace bounds for the matrix L-infinity operator norm

This arbitrary finite-index version is used after cycling a rectangular
first-hit factorization onto its localized intermediate coordinate space.
-/

namespace YangMills.RG

open scoped Matrix.Norms.Operator

noncomputable section

/-- One matrix entry is bounded by the L-infinity operator norm. -/
theorem norm_matrix_entry_le_linfty_opNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) :
    ‖A i j‖ ≤ ‖A‖ := by
  calc
    ‖A i j‖ ≤ ∑ k : ι, ‖A i k‖ := by
      exact Finset.single_le_sum (fun k _ => norm_nonneg (A i k))
        (Finset.mem_univ j)
    _ ≤ ‖A‖ := by
      rw [Matrix.linfty_opNorm_def]
      have hnn :
          (∑ k : ι, ‖A i k‖₊) ≤
            (Finset.univ : Finset ι).sup
              (fun r : ι => ∑ k : ι, ‖A r k‖₊) :=
        Finset.le_sup
          (s := (Finset.univ : Finset ι))
          (f := fun r : ι => ∑ k : ι, ‖A r k‖₊)
          (Finset.mem_univ i)
      have hreal :
          ((show NNReal from ∑ k : ι, ‖A i k‖₊) : ℝ) ≤
            ((show NNReal from
              (Finset.univ : Finset ι).sup
                (fun r : ι => ∑ k : ι, ‖A r k‖₊)) : ℝ) :=
        NNReal.coe_le_coe.mpr hnn
      simpa using hreal

/-- The trace costs at most the localized finite dimension in L-infinity
operator norm. -/
theorem norm_matrix_trace_le_card_mul_linfty_opNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    ‖A.trace‖ ≤ (Fintype.card ι : ℝ) * ‖A‖ := by
  unfold Matrix.trace
  calc
    ‖∑ i : ι, A i i‖ ≤ ∑ i : ι, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_matrix_entry_le_linfty_opNorm A i i
    _ = (Fintype.card ι : ℝ) * ‖A‖ := by simp

/-- Transport the localized trace bound across an exact trace identity. -/
theorem norm_matrix_trace_le_card_mul_linfty_opNorm_of_eq
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (htrace : A.trace = B.trace) :
    ‖A.trace‖ ≤ (Fintype.card κ : ℝ) * ‖B‖ := by
  rw [htrace]
  exact norm_matrix_trace_le_card_mul_linfty_opNorm B

end

end YangMills.RG

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

/-- Cycle a rectangular localized factorization through an arbitrary power
of an ambient defect. -/
theorem trace_rectangular_mul_pow_eq_reduced
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ)
    (D : Matrix ι ι ℂ) (m : ℕ) :
    Matrix.trace ((A * B) * D ^ m) =
      Matrix.trace ((B * D ^ m) * A) := by
  calc
    Matrix.trace ((A * B) * D ^ m) =
        Matrix.trace (A * (B * D ^ m)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace ((B * D ^ m) * A) :=
      Matrix.trace_mul_comm _ _

/-- A localized rectangular factor in a trace power costs only its
intermediate dimension.  The remaining ambient defect contributes through
its operator norm power. -/
theorem norm_trace_rectangular_mul_pow_le_card_mul
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ)
    (D : Matrix ι ι ℂ) (m : ℕ) :
    ‖Matrix.trace ((A * B) * D ^ m)‖ ≤
      (Fintype.card κ : ℝ) *
        ((‖B‖ * ‖D ^ m‖) * ‖A‖) := by
  rw [trace_rectangular_mul_pow_eq_reduced]
  calc
    ‖Matrix.trace ((B * D ^ m) * A)‖ ≤
        (Fintype.card κ : ℝ) * ‖(B * D ^ m) * A‖ :=
      norm_matrix_trace_le_card_mul_linfty_opNorm _
    _ ≤ (Fintype.card κ : ℝ) *
        ((‖B‖ * ‖D ^ m‖) * ‖A‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        ‖(B * D ^ m) * A‖ ≤ ‖B * D ^ m‖ * ‖A‖ :=
          Matrix.linfty_opNorm_mul _ _
        _ ≤ (‖B‖ * ‖D ^ m‖) * ‖A‖ := by
          gcongr
          exact Matrix.linfty_opNorm_mul _ _

/-- The same localized trace estimate with the complex scalar coefficient
carried by one physical coordinate-pivot term. -/
theorem norm_scalar_mul_trace_rectangular_mul_pow_le_card_mul
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (w : ℂ) (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ)
    (D : Matrix ι ι ℂ) (m : ℕ) :
    ‖w * Matrix.trace ((A * B) * D ^ m)‖ ≤
      (Fintype.card κ : ℝ) *
        (‖w‖ * ((‖B‖ * ‖D ^ m‖) * ‖A‖)) := by
  rw [norm_mul]
  calc
    ‖w‖ * ‖Matrix.trace ((A * B) * D ^ m)‖ ≤
        ‖w‖ * ((Fintype.card κ : ℝ) *
          ((‖B‖ * ‖D ^ m‖) * ‖A‖)) := by
      exact mul_le_mul_of_nonneg_left
        (norm_trace_rectangular_mul_pow_le_card_mul A B D m)
        (norm_nonneg w)
    _ = (Fintype.card κ : ℝ) *
        (‖w‖ * ((‖B‖ * ‖D ^ m‖) * ‖A‖)) := by ring

end

end YangMills.RG

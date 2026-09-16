/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.MatrixDetExponential
import YangMills.RG.NearLogLocalInverse

/-!
# Exact determinant identity for the matrix Mercator logarithm

Combining the local inverse `exp (nearLog D) = 1 + D` with the
finite-dimensional determinant/exponential identity gives the exact scalar
bridge needed by the CMP116 contour density.
-/

namespace YangMills.RG

open scoped Matrix.Norms.Operator

noncomputable section

/-- On the open matrix Mercator ball, the relative determinant is the
exponential of the traced matrix logarithm. -/
theorem det_one_add_eq_exp_trace_nearLog
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Matrix ι ι ℂ) (hD : ‖D‖ < 1) :
    Matrix.det (1 + D) =
      Complex.exp (Matrix.trace (nearLog D)) := by
  rw [← exp_nearLog_eq_one_add hD]
  exact det_matrix_exp_eq_exp_trace (nearLog D)

/-- A square-root density normalized by `d² exp z = 1` is bounded by
`exp (‖z‖ / 2)`.  No choice of logarithmic branch is needed for this norm
estimate. -/
theorem norm_density_le_exp_half_norm_of_sq_mul_exp_eq_one
    (d z : ℂ) (hsq : d ^ 2 * Complex.exp z = 1) :
    ‖d‖ ≤ Real.exp (‖z‖ / 2) := by
  have hn : ‖d‖ ^ 2 * Real.exp z.re = 1 := by
    have hnorm := congrArg norm hsq
    simpa [norm_mul, norm_pow, Complex.norm_exp] using hnorm
  have hsquare : ‖d‖ ^ 2 = Real.exp (-z.re) := by
    calc
      ‖d‖ ^ 2 =
          ‖d‖ ^ 2 * (Real.exp z.re * Real.exp (-z.re)) := by
            rw [← Real.exp_add]
            simp
      _ = (‖d‖ ^ 2 * Real.exp z.re) * Real.exp (-z.re) := by ring
      _ = Real.exp (-z.re) := by rw [hn, one_mul]
  have hRe : -z.re ≤ ‖z‖ :=
    (neg_le_abs z.re).trans (Complex.abs_re_le_norm z)
  have hsquareLe : ‖d‖ ^ 2 ≤ Real.exp ‖z‖ := by
    rw [hsquare]
    exact Real.exp_le_exp.mpr hRe
  have htargetSq :
      (Real.exp (‖z‖ / 2)) ^ 2 = Real.exp ‖z‖ := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hd0 : 0 ≤ ‖d‖ := norm_nonneg d
  have ht0 : 0 ≤ Real.exp (‖z‖ / 2) := (Real.exp_pos _).le
  nlinarith [hsquareLe, htargetSq]

/-- Exact determinant normalization plus the matrix Mercator identity gives
the branch-independent exponential trace bound for a contour density. -/
theorem norm_density_le_exp_half_norm_trace_nearLog
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ℂ) (D : Matrix ι ι ℂ) (hD : ‖D‖ < 1)
    (hsq : d ^ 2 * Matrix.det (1 + D) = 1) :
    ‖d‖ ≤ Real.exp
      (‖Matrix.trace (nearLog D)‖ / 2) := by
  rw [det_one_add_eq_exp_trace_nearLog D hD] at hsq
  exact
    norm_density_le_exp_half_norm_of_sq_mul_exp_eq_one
      d (Matrix.trace (nearLog D)) hsq

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexR1

/-!
# Trace telescope for the complex CMP116 `R1`

The literal `R1` telescope contains one covariance defect in each of its
three summands once the source `R3` is written as `U (C1 - C0) V`.
Under a trace, cyclicity moves that defect to the final position.  This is
the exact algebraic interface consumed by the coordinate-pivot first-hit
estimate; the remaining ambient factor is arbitrary.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- Cyclically move the second factor of a four-factor product to the final
position. -/
theorem Matrix.trace_fourFactors_rotate_second
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C D : Matrix ι ι ℂ) :
    Matrix.trace (((A * B) * C) * D) =
      Matrix.trace (((C * D) * A) * B) := by
  calc
    Matrix.trace (((A * B) * C) * D) =
        Matrix.trace ((A * B) * (C * D)) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace ((C * D) * (A * B)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((C * D) * A) * B) := by
      congr 1
      noncomm_ring

/-- A transposed covariance defect can likewise be returned to the final
position without introducing a new source expansion. -/
theorem Matrix.trace_transposeDefect_rotate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V E Q : Matrix ι ι ℂ) :
    Matrix.trace ((V.transpose * E.transpose) * Q) =
      Matrix.trace ((V * Q.transpose) * E) := by
  calc
    Matrix.trace ((V.transpose * E.transpose) * Q) =
        Matrix.trace (V.transpose * (E.transpose * Q)) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace ((E.transpose * Q) * V.transpose) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        (Matrix.transpose ((E.transpose * Q) * V.transpose)) := by
      rw [Matrix.trace_transpose]
    _ = Matrix.trace ((V * Q.transpose) * E) := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul]
      simp only [Matrix.transpose_transpose]
      congr 1
      noncomm_ring

set_option maxHeartbeats 3000000 in
/-- If the Gamma defect factors through the literal covariance defect, then
the trace of `R1` against an arbitrary ambient matrix is a sum of three
traces whose final factor is that covariance defect. -/
theorem Matrix.trace_r1Telescope_mul_eq_covarianceDefectTerms
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G0 G1 C0 C1 U V P : Matrix ι ι ℂ)
    (hG : G1 - G0 = U * (C1 - C0) * V) :
    let E := C1 - C0
    Matrix.trace
        ((G1.transpose * C1 * G1 -
          G0.transpose * C0 * G0) * P) =
      Matrix.trace
          ((((V * P.transpose) * G1.transpose) * C1.transpose * U) * E) +
        Matrix.trace (((G1 * P) * G0.transpose) * E) +
        Matrix.trace
          (((((V * P) * G0.transpose) * C0) * U) * E) := by
  let E := C1 - C0
  change
    Matrix.trace
        ((G1.transpose * C1 * G1 -
          G0.transpose * C0 * G0) * P) =
      Matrix.trace
          ((((V * P.transpose) * G1.transpose) * C1.transpose * U) * E) +
        Matrix.trace (((G1 * P) * G0.transpose) * E) +
        Matrix.trace (((((V * P) * G0.transpose) * C0) * U) * E)
  have hG' : G1 - G0 = U * E * V := by
    simpa [E] using hG
  have hGt :
      Matrix.transpose (G1 - G0) =
        (V.transpose * E.transpose) * U.transpose := by
    rw [hG']
    simp only [Matrix.transpose_mul]
    noncomm_ring
  have hfirst :
      Matrix.trace
          ((Matrix.transpose (G1 - G0) * C1 * G1) * P) =
        Matrix.trace
          ((((V * P.transpose) * G1.transpose) * C1.transpose * U) * E) := by
    calc
      Matrix.trace
          ((Matrix.transpose (G1 - G0) * C1 * G1) * P) =
          Matrix.trace
            ((V.transpose * E.transpose) *
              (((U.transpose * C1) * G1) * P)) := by
        rw [hGt]
        congr 1
        noncomm_ring
      _ = Matrix.trace
          ((V * ((((U.transpose * C1) * G1) * P).transpose)) * E) :=
        Matrix.trace_transposeDefect_rotate V E
          (((U.transpose * C1) * G1) * P)
      _ = Matrix.trace
          ((((V * P.transpose) * G1.transpose) * C1.transpose * U) * E) := by
        congr 1
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
        noncomm_ring
  have hmiddle :
      Matrix.trace ((G0.transpose * E * G1) * P) =
        Matrix.trace (((G1 * P) * G0.transpose) * E) := by
    simpa only using
      Matrix.trace_fourFactors_rotate_second G0.transpose E G1 P
  have hlast :
      Matrix.trace ((G0.transpose * C0 * (G1 - G0)) * P) =
        Matrix.trace (((((V * P) * G0.transpose) * C0) * U) * E) := by
    calc
      Matrix.trace ((G0.transpose * C0 * (G1 - G0)) * P) =
          Matrix.trace ((((G0.transpose * C0) * U) * E * V) * P) := by
        rw [hG']
        congr 1
        noncomm_ring
      _ = Matrix.trace (((V * P) * ((G0.transpose * C0) * U)) * E) :=
          Matrix.trace_fourFactors_rotate_second
            ((G0.transpose * C0) * U) E V P
      _ = Matrix.trace (((((V * P) * G0.transpose) * C0) * U) * E) := by
        congr 1
        noncomm_ring
  rw [Matrix.transpose_mul_cov_mul_sub_eq_telescope G0 G1 C0 C1,
    Matrix.add_mul, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add]
  change
    Matrix.trace
        ((Matrix.transpose (G1 - G0) * C1 * G1) * P) +
        Matrix.trace ((G0.transpose * E * G1) * P) +
        Matrix.trace ((G0.transpose * C0 * (G1 - G0)) * P) =
      Matrix.trace
          ((((V * P.transpose) * G1.transpose) * C1.transpose * U) * E) +
        Matrix.trace (((G1 * P) * G0.transpose) * E) +
        Matrix.trace (((((V * P) * G0.transpose) * C0) * U) * E)
  rw [hfirst, hmiddle, hlast]

end

end YangMills.RG

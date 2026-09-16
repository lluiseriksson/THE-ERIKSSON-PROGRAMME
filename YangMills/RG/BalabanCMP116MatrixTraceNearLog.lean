/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116MatrixTraceLinftyOpNorm
import YangMills.RG.NearLog

/-!
# Localized trace bounds for a matrix Mercator logarithm

The trace is made into a continuous real-linear functional for the
L-infinity operator norm.  It may then pass through the convergent Mercator
series.  A geometric bound on the traces of positive powers gives a
dimension-free scalar logarithm bound.
-/

namespace YangMills.RG

open scoped Matrix.Norms.Operator

noncomputable section

/-- Matrix trace as a continuous real-linear map for the L-infinity operator
norm. -/
def matrixTraceLinftyCLM
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] ℂ :=
  (Matrix.traceLinearMap (n := ι) ℝ ℂ).mkContinuous
    (Fintype.card ι) fun A => by
      simpa using norm_matrix_trace_le_card_mul_linfty_opNorm A

@[simp]
theorem matrixTraceLinftyCLM_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    matrixTraceLinftyCLM A = A.trace := rfl

/-- Trace commutes with the convergent matrix Mercator series. -/
theorem trace_nearLog_eq_tsum_trace_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Matrix ι ι ℂ) (hD : ‖D‖ < 1) :
    Matrix.trace (nearLog D) =
      ∑' m : ℕ, logCoeff m • Matrix.trace (D ^ m) := by
  have hsum :
      Summable (fun m : ℕ => logCoeff m • D ^ m) :=
    summable_logCoeff_smul_pow hD
  have hmap := (matrixTraceLinftyCLM (ι := ι)).map_tsum hsum
  simpa [nearLog] using hmap

/-- Shift the zero Mercator coefficient out of the traced series. -/
theorem trace_nearLog_eq_tsum_succ_trace_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Matrix ι ι ℂ) (hD : ‖D‖ < 1) :
    Matrix.trace (nearLog D) =
      ∑' m : ℕ, logCoeff (m + 1) • Matrix.trace (D ^ (m + 1)) := by
  have hsum :
      Summable (fun m : ℕ => logCoeff m • D ^ m) :=
    summable_logCoeff_smul_pow hD
  have htrace :
      Summable (fun m : ℕ => logCoeff m • Matrix.trace (D ^ m)) := by
    simpa using (matrixTraceLinftyCLM (ι := ι)).summable hsum
  rw [trace_nearLog_eq_tsum_trace_pow D hD, htrace.tsum_eq_zero_add]
  simp

/-- If each positive trace power has a localized geometric bound, then the
traced Mercator logarithm has the corresponding geometric sum bound. -/
theorem norm_trace_nearLog_le_of_trace_pow_geometric
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Matrix ι ι ℂ) (hD : ‖D‖ < 1)
    {L q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (htrace : ∀ m : ℕ,
      ‖Matrix.trace (D ^ (m + 1))‖ ≤ L * q ^ m) :
    ‖Matrix.trace (nearLog D)‖ ≤ L / (1 - q) := by
  have hgeo : Summable (fun m : ℕ => L * q ^ m) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left L
  have hterm : ∀ m : ℕ,
      ‖logCoeff (m + 1) • Matrix.trace (D ^ (m + 1))‖ ≤
        L * q ^ m := by
    intro m
    change
      ‖((logCoeff (m + 1) : ℂ) *
        Matrix.trace (D ^ (m + 1)))‖ ≤ L * q ^ m
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |logCoeff (m + 1)| * ‖Matrix.trace (D ^ (m + 1))‖ ≤
          1 * (L * q ^ m) := by
        apply mul_le_mul (abs_logCoeff_le_one (m + 1)) (htrace m)
          (norm_nonneg _) zero_le_one
      _ = L * q ^ m := one_mul _
  have hnorm :
      Summable (fun m : ℕ =>
        ‖logCoeff (m + 1) • Matrix.trace (D ^ (m + 1))‖) :=
    hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  rw [trace_nearLog_eq_tsum_succ_trace_pow D hD]
  calc
    ‖∑' m : ℕ, logCoeff (m + 1) • Matrix.trace (D ^ (m + 1))‖ ≤
        ∑' m : ℕ,
          ‖logCoeff (m + 1) • Matrix.trace (D ^ (m + 1))‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, L * q ^ m :=
      hnorm.tsum_le_tsum hterm hgeo
    _ = L / (1 - q) := by
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

end

end YangMills.RG

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
open scoped Matrix.Norms.Operator

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

/-- Norm budget of the three ambient multipliers generated by the `R1`
telescope, excluding the common covariance-trace cost and the final
multiplier norm. -/
noncomputable def Matrix.r1TraceMultiplierBudget
    {ι : Type*} [Fintype ι]
    (G0 G1 C0 C1 U V : Matrix ι ι ℂ) : ℝ :=
  ‖V‖ * ‖G1.transpose‖ * ‖C1.transpose‖ * ‖U‖ +
    ‖G1‖ * ‖G0.transpose‖ +
    ‖V‖ * ‖G0.transpose‖ * ‖C0‖ * ‖U‖

set_option maxHeartbeats 3000000 in
/-- An arbitrary carrier-linear trace estimate for the covariance defect
propagates through the exact `R1` telescope.  This algebraic theorem is used
only internally; the source-facing wrapper constructs the covariance estimate
from coordinate pivots. -/
theorem Matrix.norm_trace_r1Telescope_mul_le_of_covarianceTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G0 G1 C0 C1 U V P : Matrix ι ι ℂ)
    (hG : G1 - G0 = U * (C1 - C0) * V)
    {traceCost : ℝ} (htraceCost : 0 ≤ traceCost)
    (hcov : ∀ T : Matrix ι ι ℂ,
      ‖Matrix.trace (T * (C1 - C0))‖ ≤ traceCost * ‖T‖)
    (hPt : P.transpose = P) :
    ‖Matrix.trace
        ((G1.transpose * C1 * G1 -
          G0.transpose * C0 * G0) * P)‖ ≤
      traceCost *
        (Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V * ‖P‖) := by
  let E := C1 - C0
  let T1 := (((V * P.transpose) * G1.transpose) * C1.transpose * U)
  let T2 := ((G1 * P) * G0.transpose)
  let T3 := ((((V * P) * G0.transpose) * C0) * U)
  have heq :=
    Matrix.trace_r1Telescope_mul_eq_covarianceDefectTerms
      G0 G1 C0 C1 U V P hG
  change
    Matrix.trace
        ((G1.transpose * C1 * G1 -
          G0.transpose * C0 * G0) * P) =
      Matrix.trace (T1 * E) + Matrix.trace (T2 * E) +
        Matrix.trace (T3 * E) at heq
  rw [heq]
  have hT1 :
      ‖T1‖ ≤
        (‖V‖ * ‖G1.transpose‖ * ‖C1.transpose‖ * ‖U‖) * ‖P‖ := by
    dsimp [T1]
    rw [hPt]
    calc
      ‖V * P * G1.transpose * C1.transpose * U‖ ≤
          ‖V * P * G1.transpose * C1.transpose‖ * ‖U‖ :=
        Matrix.linfty_opNorm_mul _ _
      _ ≤ (‖V * P * G1.transpose‖ * ‖C1.transpose‖) * ‖U‖ := by
        gcongr
        exact Matrix.linfty_opNorm_mul _ _
      _ ≤ ((‖V * P‖ * ‖G1.transpose‖) * ‖C1.transpose‖) * ‖U‖ := by
        gcongr
        exact Matrix.linfty_opNorm_mul _ _
      _ ≤ (((‖V‖ * ‖P‖) * ‖G1.transpose‖) *
            ‖C1.transpose‖) * ‖U‖ := by
        gcongr
        exact Matrix.linfty_opNorm_mul _ _
      _ =
          (‖V‖ * ‖G1.transpose‖ * ‖C1.transpose‖ * ‖U‖) * ‖P‖ := by
        ring
  have hT2 :
      ‖T2‖ ≤ (‖G1‖ * ‖G0.transpose‖) * ‖P‖ := by
    dsimp [T2]
    calc
      ‖G1 * P * G0.transpose‖ ≤ ‖G1 * P‖ * ‖G0.transpose‖ :=
        Matrix.linfty_opNorm_mul _ _
      _ ≤ (‖G1‖ * ‖P‖) * ‖G0.transpose‖ := by
        gcongr
        exact Matrix.linfty_opNorm_mul _ _
      _ = (‖G1‖ * ‖G0.transpose‖) * ‖P‖ := by ring
  have hT3 :
      ‖T3‖ ≤
        (‖V‖ * ‖G0.transpose‖ * ‖C0‖ * ‖U‖) * ‖P‖ := by
    dsimp [T3]
    calc
      ‖V * P * G0.transpose * C0 * U‖ ≤
          ‖V * P * G0.transpose * C0‖ * ‖U‖ :=
        Matrix.linfty_opNorm_mul _ _
      _ ≤ (‖V * P * G0.transpose‖ * ‖C0‖) * ‖U‖ := by
        gcongr
        exact Matrix.linfty_opNorm_mul _ _
      _ ≤ ((‖V * P‖ * ‖G0.transpose‖) * ‖C0‖) * ‖U‖ := by
        gcongr
        exact Matrix.linfty_opNorm_mul _ _
      _ ≤ (((‖V‖ * ‖P‖) * ‖G0.transpose‖) * ‖C0‖) * ‖U‖ := by
        gcongr
        exact Matrix.linfty_opNorm_mul _ _
      _ =
          (‖V‖ * ‖G0.transpose‖ * ‖C0‖ * ‖U‖) * ‖P‖ := by
        ring
  calc
    ‖Matrix.trace (T1 * E) + Matrix.trace (T2 * E) +
        Matrix.trace (T3 * E)‖ ≤
        ‖Matrix.trace (T1 * E)‖ + ‖Matrix.trace (T2 * E)‖ +
          ‖Matrix.trace (T3 * E)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ traceCost * ‖T1‖ + traceCost * ‖T2‖ +
          traceCost * ‖T3‖ := by
      gcongr
      · exact hcov T1
      · exact hcov T2
      · exact hcov T3
    _ ≤ traceCost *
        ((‖V‖ * ‖G1.transpose‖ * ‖C1.transpose‖ * ‖U‖ +
            ‖G1‖ * ‖G0.transpose‖ +
            ‖V‖ * ‖G0.transpose‖ * ‖C0‖ * ‖U‖) * ‖P‖) := by
      calc
        traceCost * ‖T1‖ + traceCost * ‖T2‖ + traceCost * ‖T3‖ ≤
            traceCost *
                ((‖V‖ * ‖G1.transpose‖ * ‖C1.transpose‖ * ‖U‖) *
                  ‖P‖) +
              traceCost * ((‖G1‖ * ‖G0.transpose‖) * ‖P‖) +
              traceCost *
                ((‖V‖ * ‖G0.transpose‖ * ‖C0‖ * ‖U‖) * ‖P‖) := by
          gcongr
        _ = traceCost *
            ((‖V‖ * ‖G1.transpose‖ * ‖C1.transpose‖ * ‖U‖ +
                ‖G1‖ * ‖G0.transpose‖ +
                ‖V‖ * ‖G0.transpose‖ * ‖C0‖ * ‖U‖) * ‖P‖) := by
          ring
    _ = traceCost *
        (Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V * ‖P‖) := by
      rfl

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 4000000 in
/-- Physical source specialization: contour nonsingularity constructs the
exact `R2` resolvent product, hence the literal `R3` Gamma defect, and the
trace of the literal `R1` is reduced to three occurrences of the complete
source covariance defect.  No rank or support hypothesis is introduced. -/
theorem trace_cmp116SourcePi4FullComplexR1Matrix_mul_eq_covarianceDefectTerms
    {M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hseries :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius Rweak < 1)
    (P : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ) :
    let C0 := cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK
    let C1 :=
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma
    let P0 := cmp116PhysicalEndomorphismComplexMatrix K
    let P1 :=
      cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
        (R := R) anchor K hc hmass hK sigma
    let G0 := cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0
    let G1 :=
      cmp116SourcePi4FullComplexGammaMatrix
        (R := R) anchor K root hc hmass hK Z0 sigma
    let constraint := cmp116SourcePi4ConstraintMatrix M Q Nc
    let complement :=
      cmp116SourcePi4ComplementProjectionMatrix
        (M := M) (Nc := Nc) Z0
    let rootMatrix := cmp116SourcePi4ReferenceRootMatrix root
    let E := C1 - C0
    let U := -(constraint.transpose * P1)
    let V := P0 * (constraint * complement) * rootMatrix
    Matrix.trace
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0 sigma * P) =
      Matrix.trace
          ((((V * P.transpose) * G1.transpose) * C1.transpose * U) * E) +
        Matrix.trace (((G1 * P) * G0.transpose) * E) +
        Matrix.trace (((((V * P) * G0.transpose) * C0) * U) * E) := by
  dsimp only
  let C0 := cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK
  let C1 :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma
  let P0 := cmp116PhysicalEndomorphismComplexMatrix K
  let P1 :=
    cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
      (R := R) anchor K hc hmass hK sigma
  let G0 := cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0
  let G1 :=
    cmp116SourcePi4FullComplexGammaMatrix
      (R := R) anchor K root hc hmass hK Z0 sigma
  let constraint := cmp116SourcePi4ConstraintMatrix M Q Nc
  let complement :=
    cmp116SourcePi4ComplementProjectionMatrix
      (M := M) (Nc := Nc) Z0
  let rootMatrix := cmp116SourcePi4ReferenceRootMatrix root
  let E := C1 - C0
  let U := -(constraint.transpose * P1)
  let V := P0 * (constraint * complement) * rootMatrix
  change
    Matrix.trace
        ((G1.transpose * C1 * G1 - G0.transpose * C0 * G0) * P) =
      Matrix.trace
          ((((V * P.transpose) * G1.transpose) * C1.transpose * U) * E) +
        Matrix.trace (((G1 * P) * G0.transpose) * E) +
        Matrix.trace (((((V * P) * G0.transpose) * C0) * U) * E)
  have hR2 :
      cmp116SourcePi4FullComplexR2Matrix
          (R := R) anchor K hc hmass hK sigma =
        P1 * E * P0 := by
    have hraw :=
      cmp116SourcePi4FullComplexR2Matrix_eq_resolventProduct
        (R := R) (Δ := Delta)
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1 sigma
        hradius hRweak hdiff hcap hseries hneumann
    have hone :
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK (fun _ => 1) = C0 := by
      dsimp [C0]
      exact
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
          anchor K hsourceRange hfiniteRange hc hmass hK hD
    simpa [P0, P1, C0, C1, E, hone] using hraw
  have hG : G1 - G0 = U * E * V := by
    have hsource :=
      cmp116SourcePi4FullComplexR3Matrix_eq_neg_constraint_mul_R2
        (R := R) anchor K root hc hmass hK Z0 sigma
    change
      cmp116SourcePi4FullComplexR3Matrix
          (R := R) anchor K root hc hmass hK Z0 sigma =
        U * E * V
    rw [hsource, hR2]
    simp only [U, V, P0, constraint, complement, rootMatrix]
    noncomm_ring
  exact
    Matrix.trace_r1Telescope_mul_eq_covarianceDefectTerms
      G0 G1 C0 C1 U V P hG

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116R1TraceTelescope
import YangMills.RG.BalabanCMP116SourceCoordinatePivotCovarianceTraceBound

/-!
# Coordinate-pivot trace bound for the physical complex `R1`

This module composes the literal source `R1` telescope with the physical
coordinate-pivot trace estimate.  The public theorem contains no supplied
covariance trace bound: contour summability constructs it internally.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 5000000 in
/-- The literal source-complex `R1`, traced against any symmetric ambient
multiplier, has a source-carrier-linear bound generated entirely from the
physical contour certificate. -/
theorem norm_trace_cmp116SourcePi4FullComplexR1Matrix_mul_le
    {q M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin q ≃ ↥carrier) (z : Fin q → ℂ)
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
    {Ahead rho rate : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
      physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius Rweak < 1)
    (P : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (hPt : P.transpose = P) :
    let sigma := cmp116SourceRestrictedShiftedCoupling carrier e z
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    let walkRatio :=
      cmp116SourcePi4ComplexContourRatio Delta rho Rweak
    let traceUnit :=
      (q : ℝ) * 625 *
        (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        (radius * Rweak ^ 10000) * geometricRow *
        (Ahead * geometricRow)
    let traceCost := traceUnit * (1 - walkRatio)⁻¹ ^ 2
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
    let U := -(constraint.transpose * P1)
    let V := P0 * (constraint * complement) * rootMatrix
    ‖Matrix.trace
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0 sigma * P)‖ ≤
      traceCost *
        (Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V * ‖P‖) := by
  dsimp only
  let sigma := cmp116SourceRestrictedShiftedCoupling carrier e z
  let geometricRow : ℝ :=
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)
  let walkRatio : ℝ :=
    cmp116SourcePi4ComplexContourRatio Delta rho Rweak
  let traceUnit : ℝ :=
    (q : ℝ) * 625 *
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
      (radius * Rweak ^ 10000) * geometricRow *
      (Ahead * geometricRow)
  let traceCost : ℝ := traceUnit * (1 - walkRatio)⁻¹ ^ 2
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
    ‖Matrix.trace
        ((G1.transpose * C1 * G1 - G0.transpose * C0 * G0) * P)‖ ≤
      traceCost *
        (Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V * ‖P‖)
  have hsigmaDiff : ∀ d, ‖sigma d - 1‖ ≤ radius := by
    intro d
    by_cases hd : d ∈ carrier
    · simpa [sigma,
        norm_cmp116SourceRestrictedShiftedCoupling_sub_one_of_mem
          carrier e z hd] using hz (e.symm ⟨d, hd⟩)
    · rw [show sigma d = 1 by
        exact cmp116SourceRestrictedShiftedCoupling_eq_one_of_not_mem
          carrier e z hd]
      simpa using hradius
  have hsigmaCap : ∀ d, ‖sigma d‖ ≤ Rweak := by
    intro d
    by_cases hd : d ∈ carrier
    · simpa [sigma, cmp116SourceRestrictedShiftedCoupling, hd] using
        hcap (e.symm ⟨d, hd⟩)
    · rw [show sigma d = 1 by
        exact cmp116SourceRestrictedShiftedCoupling_eq_one_of_not_mem
          carrier e z hd, norm_one]
      exact hRweak
  have hone :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) = C0 := by
    dsimp [C0]
    exact
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
        anchor K hsourceRange hfiniteRange hc hmass hK hD
  have hR2 :
      cmp116SourcePi4FullComplexR2Matrix
          (R := R) anchor K hc hmass hK sigma =
        P1 * E * P0 := by
    have hraw :=
      cmp116SourcePi4FullComplexR2Matrix_eq_resolventProduct
        (R := R) (Δ := Delta)
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1 sigma
        hradius hRweak hsigmaDiff hsigmaCap hcontourSmall hneumann
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
  have hrow0 : 0 ≤ geometricRow := by
    dsimp [geometricRow]
    exact mul_nonneg (by positivity)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
  have hunit0 : 0 ≤ traceUnit := by
    dsimp [traceUnit]
    positivity
  have hcost0 : 0 ≤ traceCost := by
    dsimp [traceCost]
    positivity
  have hcov : ∀ T : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ,
      ‖Matrix.trace (T * E)‖ ≤ traceCost * ‖T‖ := by
    intro T
    have hb :=
      norm_trace_mul_cmp116SourcePi4FullComplexCovarianceDifference_le
        (R := R) (Delta := Delta)
        anchor carrier e z K hc hmass hK hAhead hrho Cert hrate hgeom
        htri hsourceRange hDelta hDelta1 radius Rweak hradius hRweak
        hz hcap hcontourSmall T
    rw [hone] at hb
    change ‖Matrix.trace (T * E)‖ ≤
      (traceUnit * ‖T‖) * (1 - walkRatio)⁻¹ ^ 2 at hb
    calc
      ‖Matrix.trace (T * E)‖ ≤
          (traceUnit * ‖T‖) * (1 - walkRatio)⁻¹ ^ 2 := hb
      _ = traceCost * ‖T‖ := by
        dsimp [traceCost]
        ring
  exact
    Matrix.norm_trace_r1Telescope_mul_le_of_covarianceTrace
      G0 G1 C0 C1 U V P hG hcost0 hcov hPt

end

end YangMills.RG

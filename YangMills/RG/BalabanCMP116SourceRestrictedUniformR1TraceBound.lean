/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceR1CoordinatePivotTraceBound

/-!
# Uniform trace tests for the restricted source `R1`

The coordinate-pivot theorem generates the carrier-linear covariance trace
cost, but its final ambient multiplier budget still depends on the contour
point.  This module isolates the exact scalar bound needed to make the trace
test uniform on a Cauchy polydisc.  It does not replace that bound by an
arbitrary trace hypothesis: the matrix tested is the literal source `R1`,
and the only residual premise names its explicit telescope multiplier.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Uniform trace coefficient after the physical coordinate-pivot cost and
the source `R1` multiplier budget have been combined. -/
noncomputable def cmp116SourceRestrictedUniformR1TraceCost
    (q M Nc Delta : ℕ)
    (radius Rweak rate Ahead rho multiplierBound : ℝ) : ℝ :=
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
  (traceUnit * (1 - walkRatio)⁻¹ ^ 2) * multiplierBound

set_option maxHeartbeats 6000000 in
/-- A uniform bound on the explicit source telescope multiplier turns the
physical coordinate-pivot estimate into a uniform symmetric trace test for
the literal complex `R1`. -/
theorem norm_trace_cmp116SourcePi4FullComplexR1Matrix_mul_le_uniform
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
    {Ahead rho rate radius Rweak multiplierBound : ℝ}
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
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius Rweak < 1)
    (hmultiplier :
      let sigma := cmp116SourceRestrictedShiftedCoupling carrier e z
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
      Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V ≤
        multiplierBound)
    (P : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (hPt : P.transpose = P) :
    ‖Matrix.trace
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling carrier e z) * P)‖ ≤
      cmp116SourceRestrictedUniformR1TraceCost
        q M Nc Delta radius Rweak rate Ahead rho multiplierBound * ‖P‖ := by
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
  let U := -(constraint.transpose * P1)
  let V := P0 * (constraint * complement) * rootMatrix
  have hraw :=
    norm_trace_cmp116SourcePi4FullComplexR1Matrix_mul_le
      anchor carrier e z K root hsourceRange hfiniteRange
      hc hmass hK hD hAhead hrho Cert hrate hgeom htri
      hDelta hDelta1 Z0 radius Rweak hradius hRweak hz hcap
      hcontourSmall hneumann P hPt
  change
    ‖Matrix.trace
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0 sigma * P)‖ ≤
      traceCost * multiplierBound * ‖P‖
  change
    ‖Matrix.trace
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0 sigma * P)‖ ≤
      traceCost *
        (Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V * ‖P‖) at hraw
  have hgeometricRow : 0 ≤ geometricRow := by
    dsimp [geometricRow]
    exact mul_nonneg (by positivity)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
  have htraceCost : 0 ≤ traceCost := by
    dsimp [traceCost, traceUnit]
    positivity
  calc
    ‖Matrix.trace
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0 sigma * P)‖ ≤
        traceCost *
          (Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V * ‖P‖) := hraw
    _ ≤ traceCost * (multiplierBound * ‖P‖) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right hmultiplier (norm_nonneg P)
      · exact htraceCost
    _ = traceCost * multiplierBound * ‖P‖ := by ring

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116DeterminantNearLog
import YangMills.RG.BalabanCMP116SourceRestrictedContourDeterminantRatio
import YangMills.RG.BalabanCMP116SourceCoordinatePivotTsumBound

/-!
# Source-restricted CMP116 determinant density from the localized trace

The exact determinant normalization and the physical first-hit trace bound
are now connected without an ambient-dimension determinant estimate.  The
first endpoint below is the source-specific exact bridge.  The terminal
endpoint consumes the carrier-linear trace estimate.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The literal source-restricted determinant density is bounded by one half
of the norm of the traced physical Mercator logarithm. -/
theorem norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_half_trace
    {nDelta M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (z : Fin nDelta → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    (hsmall :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e z)‖ < 1) :
    ‖cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e z))‖ ≤
      Real.exp
        (‖Matrix.trace
          (nearLog
            (cmp116SourcePi4FullComplexRelativeCovarianceDefect
              (R := R) anchor K hc hmass hK
                (cmp116SourceRestrictedShiftedCoupling
                  contourCarrier e z)))‖ / 2) := by
  let density :=
    cmp116Eq214LogDeterminantDensity
      (cmp116PhysicalEndomorphismComplexMatrix K)
      (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e z))
  let defect :=
    cmp116SourcePi4FullComplexRelativeCovarianceDefect
      (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling contourCarrier e z)
  have hsq : density ^ 2 * (1 + defect).det = 1 := by
    simpa [density, defect] using
      (cmp116SourceRestrictedContour_logDetDensity_sq_mul_relativeDet_eq_one
        anchor contourCarrier e z K hsourceRange hrange
        hc hmass hK hD hsmall)
  simpa [density, defect] using
    (norm_density_le_exp_half_norm_trace_nearLog
      density defect hsmall hsq)

set_option maxHeartbeats 4000000 in
/-- The source-restricted determinant density has an explicit
carrier-linear exponential bound.  Every constant is produced by the
physical first-hit walk construction; no ambient matrix dimension occurs. -/
theorem norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_traceBudget
    {q M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin q ≃ ↥carrier) (z : Fin q → ℂ)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange :
      PhysicalCovarianceFiniteRange K physicalBondDist R)
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
        physicalBondDist target middle +
          physicalBondDist middle source)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (hdefectSmall :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling carrier e z)‖ < 1) :
    let geometricRow :=
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate)
    let walkRatio :=
      cmp116SourcePi4ComplexContourRatio Delta rho Rweak
    let defect :=
      cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling carrier e z)
    let tracePrefactor :=
      (q : ℝ) * 625 *
        (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
        (radius * Rweak ^ 10000) * geometricRow *
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        (Ahead * geometricRow)
    ‖cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling carrier e z))‖ ≤
      Real.exp
        (((tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) /
          (1 - ‖defect‖)) / 2) := by
  dsimp only
  let geometricRow : ℝ :=
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)
  let walkRatio : ℝ :=
    cmp116SourcePi4ComplexContourRatio Delta rho Rweak
  let defect :=
    cmp116SourcePi4FullComplexRelativeCovarianceDefect
      (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling carrier e z)
  let tracePrefactor : ℝ :=
    (q : ℝ) * 625 *
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
      (radius * Rweak ^ 10000) * geometricRow *
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
      (Ahead * geometricRow)
  have hdensity :=
    norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_half_trace
      anchor carrier e z K hsourceRange hfiniteRange
      hc hmass hK hD hdefectSmall
  have htrace :
      ‖Matrix.trace (nearLog defect)‖ ≤
        (tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) /
          (1 - ‖defect‖) := by
    simpa [defect, geometricRow, walkRatio, tracePrefactor] using
      (norm_trace_nearLog_cmp116SourcePi4FullComplexRelativeCovarianceDefect_le
        (R := R) (Delta := Delta)
        anchor carrier e z K hc hmass hK hAhead hrho Cert
        hrate hgeom htri hsourceRange hDelta hDelta1
        radius Rweak hradius hRweak hz hcap
        hcontourSmall hdefectSmall)
  calc
    ‖cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling carrier e z))‖ ≤
        Real.exp (‖Matrix.trace (nearLog defect)‖ / 2) := by
          simpa [defect] using hdensity
    _ ≤ Real.exp
        (((tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) /
          (1 - ‖defect‖)) / 2) := by
      apply Real.exp_le_exp.mpr
      linarith

end

end YangMills.RG

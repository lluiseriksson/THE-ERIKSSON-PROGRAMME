/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116DeterminantNearLog
import YangMills.RG.BalabanCMP116SourceRestrictedContourDeterminantRatio
import YangMills.RG.BalabanCMP116SourceCoordinatePivotTsumBound
import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalContourDensity

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

namespace CMP116Eq214PhysicalContourDensity

/-- The literal restricted contour object generates its determinant bound
internally from the physical near logarithm.  The only remaining outer
Gaussian obligation is the real quadratic estimate for the *literal*
source-complex `R₁`; there is no abstract determinant or `outerWeight`
majorant in the interface. -/
theorem norm_restricted_outerWeight_le_exp_half_trace_mul_of_r1
    {nDelta nY M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (anchor : FinBox 4 Q)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (hcarrier : contourCarrier ⊆ cmp116SourceSigmaZero anchor)
    (e : Fin nDelta ≃ ↥contourCarrier)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (K root : PhysicalEndomorphism M Q Nc)
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
    (hcontour : ∀ z,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius z →
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e z)).det ≠ 0)
    (S : Finset
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc))
    (outerRate : ℝ)
    (z : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hsmall :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling
            contourCarrier e z)‖ < 1)
    (hr1 :
      (cmp116Eq214ComplexQuadratic
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling
              contourCarrier e z)) x).re ≤
        outerRate * ∑ i ∈ S, x i ^ 2) :
    let Cphysical :=
      C.withSourcePi4RestrictedComplexGaussian
        anchor contourCarrier hcarrier e Z0 K root
        hsourceRange hrange hc hmass hK hD hcontour
    ‖Cphysical.toLocalFiniteGaussianData.outerWeight
        z tau psi phi x‖ ≤
      Real.exp
          (‖Matrix.trace
            (nearLog
              (cmp116SourcePi4FullComplexRelativeCovarianceDefect
                (R := R) anchor K hc hmass hK
                  (cmp116SourceRestrictedShiftedCoupling
                    contourCarrier e z)))‖ / 2) *
        Real.exp (outerRate * ∑ i ∈ S, x i ^ 2) := by
  dsimp only
  let Cphysical :=
    C.withSourcePi4RestrictedComplexGaussian
      anchor contourCarrier hcarrier e Z0 K root
      hsourceRange hrange hc hmass hK hD hcontour
  apply Cphysical.norm_outerWeight_le_of_determinantDensity_of_r1
    S
    (Real.exp
      (‖Matrix.trace
        (nearLog
          (cmp116SourcePi4FullComplexRelativeCovarianceDefect
            (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling
                contourCarrier e z)))‖ / 2))
    outerRate z tau psi phi x
  · simpa [Cphysical] using
      (norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_half_trace
        anchor contourCarrier e z K hsourceRange hrange
        hc hmass hK hD hsmall)
  · simpa [Cphysical] using hr1

set_option maxHeartbeats 5000000 in
/-- Fully explicit determinant part of the restricted outer weight.  The
near-log trace is discharged by the carrier-linear physical first-hit walk
budget, so the interface contains neither an ambient dimension nor a free
determinant estimate. -/
theorem norm_restricted_outerWeight_le_exp_traceBudget_mul_of_r1
    {q nY M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity q nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (hcarrier : carrier ⊆ cmp116SourceSigmaZero anchor)
    (e : Fin q ≃ ↥carrier)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (K root : PhysicalEndomorphism M Q Nc)
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
    (hcontour : ∀ z,
      CMP116Eq214ShiftedPolydisc q C.deltaRadius z →
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling
            carrier e z)).det ≠ 0)
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
    (z : Fin q → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (hdefectSmall :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling carrier e z)‖ < 1)
    (S : Finset
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc))
    (outerRate : ℝ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hr1 :
      (cmp116Eq214ComplexQuadratic
        (cmp116SourcePi4FullComplexR1Matrix
          (R := R) anchor K root hc hmass hK Z0
            (cmp116SourceRestrictedShiftedCoupling carrier e z)) x).re ≤
        outerRate * ∑ i ∈ S, x i ^ 2) :
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
    let determinantBudget :=
      ((tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) /
        (1 - ‖defect‖)) / 2
    let Cphysical :=
      C.withSourcePi4RestrictedComplexGaussian
        anchor carrier hcarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD hcontour
    ‖Cphysical.toLocalFiniteGaussianData.outerWeight
        z tau psi phi x‖ ≤
      Real.exp determinantBudget *
        Real.exp (outerRate * ∑ i ∈ S, x i ^ 2) := by
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
  let determinantBudget : ℝ :=
    ((tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) /
      (1 - ‖defect‖)) / 2
  let Cphysical :=
    C.withSourcePi4RestrictedComplexGaussian
      anchor carrier hcarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD hcontour
  apply Cphysical.norm_outerWeight_le_of_determinantDensity_of_r1
    S (Real.exp determinantBudget) outerRate z tau psi phi x
  · simpa [Cphysical, determinantBudget, defect, tracePrefactor,
      walkRatio, geometricRow] using
      (norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_traceBudget
        anchor carrier e z K hsourceRange hfiniteRange
        hc hmass hK hD hAhead hrho Cert hrate hgeom htri
        hDelta hDelta1 radius Rweak hradius hRweak hz hcap
        hcontourSmall hdefectSmall)
  · simpa [Cphysical] using hr1

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG

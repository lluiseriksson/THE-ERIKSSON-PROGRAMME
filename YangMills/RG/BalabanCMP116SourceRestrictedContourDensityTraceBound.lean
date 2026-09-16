/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116DeterminantNearLog
import YangMills.RG.BalabanCMP116SourceRestrictedContourDeterminantRatio
import YangMills.RG.BalabanCMP116SourceCoordinatePivotTsumBound
import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalContourDensity
import YangMills.RG.BalabanCMP116Eq214PhysicalGapCarrier

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

/-- Determinant cost per active source coordinate.  The full trace budget is
this constant times the localized contour cardinality. -/
noncomputable def cmp116SourceRestrictedContourDeterminantPerCarrierCost
    (M Nc Delta : ℕ)
    (radius Rweak rate Ahead rho precisionNorm defectNorm : ℝ) : ℝ :=
  let geometricRow :=
    (((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate)
  let walkRatio :=
    cmp116SourcePi4ComplexContourRatio Delta rho Rweak
  (((625 *
      (((40000 * M ^ 4) * (Nc ^ 2 - 1) : ℕ) : ℝ) *
      (radius * Rweak ^ 10000) * geometricRow *
      precisionNorm * (Ahead * geometricRow)) *
      (1 - walkRatio)⁻¹ ^ 2) /
    (1 - defectNorm)) / 2

set_option maxHeartbeats 5000000 in
/-- A contour carrier contained in `Z₀` converts the exact determinant trace
budget into the source-ledger form `exp(c_det |Z₀|)`.  The inclusion is
visible because it is the genuine remaining geometric relation between the
Cauchy coordinates and the localization region. -/
theorem norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_detCost_card
    {q M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier Z0 : Finset (FinBox 4 (2 * Q)))
    (hcarrierZ0 : carrier ⊆ Z0)
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
    ‖cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling carrier e z))‖ ≤
      Real.exp
        (cmp116SourceRestrictedContourDeterminantPerCarrierCost
          M Nc Delta radius Rweak rate Ahead rho
          ‖cmp116PhysicalEndomorphismComplexMatrix K‖
          ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
            (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling carrier e z)‖ *
          (Z0.card : ℝ)) := by
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
  let rawBudget : ℝ :=
    ((tracePrefactor * (1 - walkRatio)⁻¹ ^ 2) /
      (1 - ‖defect‖)) / 2
  let detCost : ℝ :=
    cmp116SourceRestrictedContourDeterminantPerCarrierCost
      M Nc Delta radius Rweak rate Ahead rho
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ ‖defect‖
  have hdensity :
      ‖cmp116Eq214LogDeterminantDensity
          (cmp116PhysicalEndomorphismComplexMatrix K)
          (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
            (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling carrier e z))‖ ≤
        Real.exp rawBudget := by
    simpa [rawBudget, tracePrefactor, defect, walkRatio, geometricRow] using
      (norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_traceBudget
        anchor carrier e z K hsourceRange hfiniteRange
        hc hmass hK hD hAhead hrho Cert hrate hgeom htri
        hDelta hDelta1 radius Rweak hradius hRweak hz hcap
        hcontourSmall hdefectSmall)
  have hq : q = carrier.card :=
    CMP116Eq214PhysicalContourDensity.withSourcePi4RestrictedComplexGaussian_delta_card
      carrier e
  have hcardNat : carrier.card ≤ Z0.card :=
    Finset.card_le_card hcarrierZ0
  have hcard : (q : ℝ) ≤ (Z0.card : ℝ) := by
    rw [hq]
    exact_mod_cast hcardNat
  have hdefectPos : 0 < 1 - ‖defect‖ := by
    dsimp [defect]
    linarith
  have hgeometricRow : 0 ≤ geometricRow := by
    dsimp [geometricRow]
    exact mul_nonneg (by positivity)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
  have hRweak0 : 0 ≤ Rweak := le_trans zero_le_one hRweak
  have hcost : 0 ≤ detCost := by
    dsimp [detCost,
      cmp116SourceRestrictedContourDeterminantPerCarrierCost,
      geometricRow, walkRatio]
    positivity
  have hbudget : rawBudget = detCost * (q : ℝ) := by
    dsimp [rawBudget, tracePrefactor, detCost,
      cmp116SourceRestrictedContourDeterminantPerCarrierCost,
      geometricRow, walkRatio]
    ring
  calc
    ‖cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling carrier e z))‖ ≤
        Real.exp rawBudget := hdensity
    _ ≤ Real.exp (detCost * (Z0.card : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [hbudget]
      exact mul_le_mul_of_nonneg_left hcard hcost
    _ = Real.exp
        (cmp116SourceRestrictedContourDeterminantPerCarrierCost
          M Nc Delta radius Rweak rate Ahead rho
          ‖cmp116PhysicalEndomorphismComplexMatrix K‖
          ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
            (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling carrier e z)‖ *
          (Z0.card : ℝ)) := by
      rfl

set_option maxHeartbeats 5000000 in
/-- For the literal equation-(2.14) gap `Z₀ \ Y₀(D)`, the localization
inclusion required by the determinant estimate is generated internally.
Thus the determinant cost is carrier-linear for the physical Cauchy
coordinates, without a separate `carrier ⊆ Z₀` premise. -/
theorem norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_detCost_card_physicalGap
    {q M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (D : Finset (Finset (FinBox 4 (2 * Q))))
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (e : Fin q ≃
      ↥(cmp116Eq214PhysicalGapCarrier (M := M) D Z0))
    (z : Fin q → ℂ)
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
          (cmp116SourceRestrictedShiftedCoupling
            (cmp116Eq214PhysicalGapCarrier (M := M) D Z0) e z)‖ < 1) :
    ‖cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK
            (cmp116SourceRestrictedShiftedCoupling
              (cmp116Eq214PhysicalGapCarrier (M := M) D Z0) e z))‖ ≤
      Real.exp
        (cmp116SourceRestrictedContourDeterminantPerCarrierCost
          M Nc Delta radius Rweak rate Ahead rho
          ‖cmp116PhysicalEndomorphismComplexMatrix K‖
          ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
            (R := R) anchor K hc hmass hK
              (cmp116SourceRestrictedShiftedCoupling
                (cmp116Eq214PhysicalGapCarrier (M := M) D Z0) e z)‖ *
          (Z0.card : ℝ)) := by
  exact
    norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_detCost_card
      anchor
      (cmp116Eq214PhysicalGapCarrier (M := M) D Z0) Z0
      (cmp116Eq214PhysicalGapCarrier_subset_Z0 D Z0)
      e z K hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho Cert hrate hgeom htri hDelta hDelta1
      radius Rweak hradius hRweak hz hcap hcontourSmall hdefectSmall

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

set_option maxHeartbeats 5000000 in
/-- Ledger-ready outer bound.  Once the physical contour carrier lies in
`Z₀`, the determinant contributes exactly an exponential cost per
localization block, while the literal complex `R₁` contributes the outer
Gaussian energy rate. -/
theorem norm_restricted_outerWeight_le_exp_detCost_card_mul_of_r1
    {q nY M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity q nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (anchor : FinBox 4 Q)
    (carrier Z0 : Finset (FinBox 4 (2 * Q)))
    (hsourceCarrier : carrier ⊆ cmp116SourceSigmaZero anchor)
    (hcarrierZ0 : carrier ⊆ Z0)
    (e : Fin q ≃ ↥carrier)
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
          (cmp116SourceRestrictedShiftedCoupling carrier e z)).det ≠ 0)
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
    let defect :=
      cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling carrier e z)
    let detCost :=
      cmp116SourceRestrictedContourDeterminantPerCarrierCost
        M Nc Delta radius Rweak rate Ahead rho
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖ ‖defect‖
    let Cphysical :=
      C.withSourcePi4RestrictedComplexGaussian
        anchor carrier hsourceCarrier e Z0 K root
        hsourceRange hfiniteRange hc hmass hK hD hcontour
    ‖Cphysical.toLocalFiniteGaussianData.outerWeight
        z tau psi phi x‖ ≤
      Real.exp (detCost * (Z0.card : ℝ)) *
        Real.exp (outerRate * ∑ i ∈ S, x i ^ 2) := by
  dsimp only
  let defect :=
    cmp116SourcePi4FullComplexRelativeCovarianceDefect
      (R := R) anchor K hc hmass hK
        (cmp116SourceRestrictedShiftedCoupling carrier e z)
  let detCost :=
    cmp116SourceRestrictedContourDeterminantPerCarrierCost
      M Nc Delta radius Rweak rate Ahead rho
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ ‖defect‖
  let Cphysical :=
    C.withSourcePi4RestrictedComplexGaussian
      anchor carrier hsourceCarrier e Z0 K root
      hsourceRange hfiniteRange hc hmass hK hD hcontour
  apply Cphysical.norm_outerWeight_le_of_determinantDensity_of_r1
    S (Real.exp (detCost * (Z0.card : ℝ)))
      outerRate z tau psi phi x
  · simpa [Cphysical, detCost, defect] using
      (norm_cmp116SourceRestrictedContour_logDetDensity_le_exp_detCost_card
        anchor carrier Z0 hcarrierZ0 e z K
        hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho Cert hrate hgeom htri hDelta hDelta1
        radius Rweak hradius hRweak hz hcap
        hcontourSmall hdefectSmall)
  · simpa [Cphysical] using hr1

set_option maxHeartbeats 5000000 in
/-- Fully geometric specialization of the ledger-ready outer bound.  The
Cauchy carrier is the literal gap `Z₀ \ Y₀(D)`; membership of the
distinguished `Pi⁴` block domain in `D` generates its inclusion in `sigma₀`,
and gap containment in `Z₀` is definitional.  Only the genuine complex
`R₁` quadratic estimate remains analytic. -/
theorem norm_restricted_outerWeight_le_exp_detCost_card_physicalGap_of_pi4_mem
    {q nY M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity q nY
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi E (Nc ^ 2 - 1))
    (anchor : FinBox 4 Q)
    (D : Finset (Finset (FinBox 4 (2 * Q))))
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (hPi4 :
      cmp99SourceDomainLargeBlocks (cmp99SourcePi4CollarDomain anchor) ∈ D)
    (e : Fin q ≃
      ↥(cmp116Eq214PhysicalGapCarrier (M := M) D Z0))
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
            (cmp116Eq214PhysicalGapCarrier (M := M) D Z0) e z)).det ≠ 0)
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
          (cmp116SourceRestrictedShiftedCoupling
            (cmp116Eq214PhysicalGapCarrier (M := M) D Z0) e z)‖ < 1)
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
            (cmp116SourceRestrictedShiftedCoupling
              (cmp116Eq214PhysicalGapCarrier (M := M) D Z0) e z)) x).re ≤
        outerRate * ∑ i ∈ S, x i ^ 2) :
    let gap := cmp116Eq214PhysicalGapCarrier (M := M) D Z0
    let defect :=
      cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling gap e z)
    let detCost :=
      cmp116SourceRestrictedContourDeterminantPerCarrierCost
        M Nc Delta radius Rweak rate Ahead rho
        ‖cmp116PhysicalEndomorphismComplexMatrix K‖ ‖defect‖
    let Cphysical :=
      C.withSourcePi4RestrictedComplexGaussian
        anchor gap
        (cmp116Eq214PhysicalGapCarrier_subset_sigmaZero_of_pi4_mem
          anchor D Z0 hPi4)
        e Z0 K root hsourceRange hfiniteRange hc hmass hK hD hcontour
    ‖Cphysical.toLocalFiniteGaussianData.outerWeight
        z tau psi phi x‖ ≤
      Real.exp (detCost * (Z0.card : ℝ)) *
        Real.exp (outerRate * ∑ i ∈ S, x i ^ 2) := by
  dsimp only
  exact
    norm_restricted_outerWeight_le_exp_detCost_card_mul_of_r1
      C anchor
      (cmp116Eq214PhysicalGapCarrier (M := M) D Z0) Z0
      (cmp116Eq214PhysicalGapCarrier_subset_sigmaZero_of_pi4_mem
        anchor D Z0 hPi4)
      (cmp116Eq214PhysicalGapCarrier_subset_Z0 D Z0)
      e K root hsourceRange hfiniteRange hc hmass hK hD hcontour
      hAhead hrho Cert hrate hgeom htri hDelta hDelta1
      radius Rweak hradius hRweak z hz hcap hcontourSmall hdefectSmall
      S outerRate tau psi phi x hr1

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG

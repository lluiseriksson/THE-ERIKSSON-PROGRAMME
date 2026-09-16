/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedHeadDefect
import YangMills.RG.BalabanCMP116SourceRestrictedVisitedTransferPower
import YangMills.RG.BalabanCMP116SourcePi4FullComplexContourNonsingularity
import YangMills.RG.BalabanCMP116SourceRestrictedContourDeterminantRatio

/-!
# Finite source factorization from the restricted visited resolvent

This module specializes the generic finite-state resolvent factorization to
the literal source `Pi^4` patched-parametrix walk.  Both contour dependences
are retained: the distinguished-head weight and the continuation transfer.
Their two finite factorizations are concatenated and then consumed by the
literal physical relative covariance defect.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The complete restricted source covariance defect factors through the
disjoint union of active heads and active transfer targets, paired with the
physical scalar coordinate. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_restricted_sub_one_eq_finiteFactorization
    {nContour M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nContour ≃ ↥carrier)
    (z : Fin nContour → ℂ)
    (hsum :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
          (cmp116SourceRestrictedShiftedCoupling carrier e z) ^ n)
    (hsumOne :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
          (fun _ => 1) ^ n) :
    let sigma :=
      cmp116SourceRestrictedShiftedCoupling carrier e z
    let domainActive :=
      cmp116SourcePi4RestrictedDomainActive anchor
    let successors :=
      cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R
    let R0 :=
      cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK
    let continuation :=
      cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK
    let Tnew :=
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors continuation sigma
    let Tbase :=
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors continuation (fun _ => 1)
    let Nnew :=
      cmp116RestrictedVisitedTransferResolvent
        carrier domainActive successors continuation sigma
    let Nbase :=
      cmp116RestrictedVisitedTransferResolvent
        carrier domainActive successors continuation (fun _ => 1)
    let p :=
      cmp116RestrictedTransferTargetActive carrier domainActive
    let AHead :=
      cmp116RestrictedHeadDefectLeft carrier domainActive R0 sigma
    let BHead :=
      cmp116RestrictedHeadDefectRight
        (Label := Unit) carrier domainActive Nnew
    let ADynamic :=
      cmp116RestrictedHeadReadoutProductLeft
        carrier domainActive R0 (fun _ => 1)
        (Nnew * Matrix.predicateColumnRestriction p (Tnew - Tbase))
    let BDynamic :=
      cmp116RestrictedHeadReadoutProductRight
        carrier
        (Matrix.predicateColumnInclusion
          (R := Matrix
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
          p * Nbase)
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma -
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK (fun _ => 1) =
      Matrix.sumFactorLeft AHead ADynamic *
        Matrix.sumFactorRight BHead BDynamic := by
  dsimp only
  have hnew :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_restricted_eq_headReadout_resolvent
      (R := R) anchor K hc hmass hK carrier e z hsum
  have hbase :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_restricted_eq_headReadout_resolvent
      (R := R) anchor K hc hmass hK carrier e
        (0 : Fin nContour → ℂ) (by
          simpa [cmp116SourceRestrictedShiftedCoupling_zero] using hsumOne)
  rw [cmp116SourceRestrictedShiftedCoupling_zero] at hbase
  rw [hnew, hbase]
  exact
    cmp116RestrictedVisitedTransferHeadReadout_resolvent_sub_one_eq_finiteFactorization
      carrier
      (cmp116SourcePi4RestrictedDomainActive anchor)
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
      (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
      (cmp116SourceRestrictedShiftedCoupling carrier e z)
      hsum hsumOne

/-- The literal physical relative covariance defect inherits the same finite
factorization, with the base precision absorbed into its left leg. -/
theorem cmp116SourcePi4FullComplexRelativeCovarianceDefect_restricted_eq_finiteFactorization
    {nContour M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nContour ≃ ↥carrier)
    (z : Fin nContour → ℂ)
    (hsum :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
          (cmp116SourceRestrictedShiftedCoupling carrier e z) ^ n)
    (hsumOne :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
          (fun _ => 1) ^ n) :
    let sigma :=
      cmp116SourceRestrictedShiftedCoupling carrier e z
    let domainActive :=
      cmp116SourcePi4RestrictedDomainActive anchor
    let successors :=
      cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R
    let R0 :=
      cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK
    let continuation :=
      cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK
    let Tnew :=
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors continuation sigma
    let Tbase :=
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors continuation (fun _ => 1)
    let Nnew :=
      cmp116RestrictedVisitedTransferResolvent
        carrier domainActive successors continuation sigma
    let Nbase :=
      cmp116RestrictedVisitedTransferResolvent
        carrier domainActive successors continuation (fun _ => 1)
    let p :=
      cmp116RestrictedTransferTargetActive carrier domainActive
    let AHead :=
      cmp116RestrictedHeadDefectLeft carrier domainActive R0 sigma
    let BHead :=
      cmp116RestrictedHeadDefectRight
        (Label := Unit) carrier domainActive Nnew
    let ADynamic :=
      cmp116RestrictedHeadReadoutProductLeft
        carrier domainActive R0 (fun _ => 1)
        (Nnew * Matrix.predicateColumnRestriction p (Tnew - Tbase))
    let BDynamic :=
      cmp116RestrictedHeadReadoutProductRight
        carrier
        (Matrix.predicateColumnInclusion
          (R := Matrix
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
          p * Nbase)
    let A :=
      Matrix.sumFactorLeft AHead ADynamic
    let B :=
      Matrix.sumFactorRight BHead BDynamic
    cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK sigma =
      (cmp116PhysicalEndomorphismComplexMatrix K * A) * B := by
  dsimp only
  unfold cmp116SourcePi4FullComplexRelativeCovarianceDefect
  rw [
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_restricted_sub_one_eq_finiteFactorization
      anchor K hc hmass hK carrier e z hsum hsumOne,
    Matrix.mul_assoc]

/-- The finite active-state factorization is consumed directly by the
source Weinstein--Aronszajn theorem.  The determinant now lives on the
disjoint union of active heads and active transfer targets, paired with one
physical scalar coordinate. -/
theorem cmp116SourceRestrictedContour_logDetDensity_sq_mul_activeStateDet_eq_one
    {nContour M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
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
    (carrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nContour ≃ ↥carrier)
    (z : Fin nContour → ℂ)
    (hsmall :
      ‖cmp116SourcePi4FullComplexRelativeCovarianceDefect
        (R := R) anchor K hc hmass hK
          (cmp116SourceRestrictedShiftedCoupling carrier e z)‖ < 1)
    (hsum :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
          (cmp116SourceRestrictedShiftedCoupling carrier e z) ^ n)
    (hsumOne :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
          (fun _ => 1) ^ n) :
    let sigma :=
      cmp116SourceRestrictedShiftedCoupling carrier e z
    let domainActive :=
      cmp116SourcePi4RestrictedDomainActive anchor
    let successors :=
      cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R
    let R0 :=
      cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK
    let continuation :=
      cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK
    let Tnew :=
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors continuation sigma
    let Tbase :=
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors continuation (fun _ => 1)
    let Nnew :=
      cmp116RestrictedVisitedTransferResolvent
        carrier domainActive successors continuation sigma
    let Nbase :=
      cmp116RestrictedVisitedTransferResolvent
        carrier domainActive successors continuation (fun _ => 1)
    let p :=
      cmp116RestrictedTransferTargetActive carrier domainActive
    let AHead :=
      cmp116RestrictedHeadDefectLeft carrier domainActive R0 sigma
    let BHead :=
      cmp116RestrictedHeadDefectRight
        (Label := Unit) carrier domainActive Nnew
    let ADynamic :=
      cmp116RestrictedHeadReadoutProductLeft
        carrier domainActive R0 (fun _ => 1)
        (Nnew * Matrix.predicateColumnRestriction p (Tnew - Tbase))
    let BDynamic :=
      cmp116RestrictedHeadReadoutProductRight
        carrier
        (Matrix.predicateColumnInclusion
          (R := Matrix
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
            (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
          p * Nbase)
    let A := Matrix.sumFactorLeft AHead ADynamic
    let B := Matrix.sumFactorRight BHead BDynamic
    cmp116Eq214LogDeterminantDensity
        (cmp116PhysicalEndomorphismComplexMatrix K)
        (cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
          (R := R) anchor K hc hmass hK sigma) ^ 2 *
      (1 + B * (cmp116PhysicalEndomorphismComplexMatrix K * A)).det =
      1 := by
  dsimp only
  apply
    cmp116SourceRestrictedContour_logDetDensity_sq_mul_reducedDet_eq_one
      anchor carrier e z K hsourceRange hrange hc hmass hK hD hsmall
      (cmp116PhysicalEndomorphismComplexMatrix K *
        Matrix.sumFactorLeft
          (cmp116RestrictedHeadDefectLeft carrier
            (cmp116SourcePi4RestrictedDomainActive anchor)
            (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
            (cmp116SourceRestrictedShiftedCoupling carrier e z))
          (cmp116RestrictedHeadReadoutProductLeft carrier
            (cmp116SourcePi4RestrictedDomainActive anchor)
            (cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK)
            (fun _ => 1)
            (cmp116RestrictedVisitedTransferResolvent carrier
                (cmp116SourcePi4RestrictedDomainActive anchor)
                (cmp99PhysicalPatchSuccessorSteps
                  (cmp99SourcePi4Charts :
                    Finset (CMP99SourcePi4Chart Unit Q))
                  (cmp99SourcePi4ChartCore (M := M))
                  cmp99SourcePi4ChartEnlarged physicalBondDist R)
                (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
                (cmp116SourceRestrictedShiftedCoupling carrier e z) *
              Matrix.predicateColumnRestriction
                (cmp116RestrictedTransferTargetActive carrier
                  (cmp116SourcePi4RestrictedDomainActive anchor))
                (cmp116RestrictedVisitedTransferMatrix carrier
                    (cmp116SourcePi4RestrictedDomainActive anchor)
                    (cmp99PhysicalPatchSuccessorSteps
                      (cmp99SourcePi4Charts :
                        Finset (CMP99SourcePi4Chart Unit Q))
                      (cmp99SourcePi4ChartCore (M := M))
                      cmp99SourcePi4ChartEnlarged physicalBondDist R)
                    (cmp116SourcePi4RestrictedContinuationMatrix
                      K hc hmass hK)
                    (cmp116SourceRestrictedShiftedCoupling carrier e z) -
                  cmp116RestrictedVisitedTransferMatrix carrier
                    (cmp116SourcePi4RestrictedDomainActive anchor)
                    (cmp99PhysicalPatchSuccessorSteps
                      (cmp99SourcePi4Charts :
                        Finset (CMP99SourcePi4Chart Unit Q))
                      (cmp99SourcePi4ChartCore (M := M))
                      cmp99SourcePi4ChartEnlarged physicalBondDist R)
                    (cmp116SourcePi4RestrictedContinuationMatrix
                      K hc hmass hK) (fun _ => 1)))))
      (Matrix.sumFactorRight
        (cmp116RestrictedHeadDefectRight
          (Label := Unit) carrier
          (cmp116SourcePi4RestrictedDomainActive anchor)
          (cmp116RestrictedVisitedTransferResolvent carrier
            (cmp116SourcePi4RestrictedDomainActive anchor)
            (cmp99PhysicalPatchSuccessorSteps
              (cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q))
              (cmp99SourcePi4ChartCore (M := M))
              cmp99SourcePi4ChartEnlarged physicalBondDist R)
            (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
            (cmp116SourceRestrictedShiftedCoupling carrier e z)))
        (cmp116RestrictedHeadReadoutProductRight carrier
          (Matrix.predicateColumnInclusion
            (R := Matrix
              (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
              (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
            (cmp116RestrictedTransferTargetActive carrier
              (cmp116SourcePi4RestrictedDomainActive anchor)) *
            cmp116RestrictedVisitedTransferResolvent carrier
              (cmp116SourcePi4RestrictedDomainActive anchor)
              (cmp99PhysicalPatchSuccessorSteps
                (cmp99SourcePi4Charts :
                  Finset (CMP99SourcePi4Chart Unit Q))
                (cmp99SourcePi4ChartCore (M := M))
                cmp99SourcePi4ChartEnlarged physicalBondDist R)
              (cmp116SourcePi4RestrictedContinuationMatrix K hc hmass hK)
              (fun _ => 1))))
  exact
    cmp116SourcePi4FullComplexRelativeCovarianceDefect_restricted_eq_finiteFactorization
      anchor K hc hmass hK carrier e z hsum hsumOne

end

end YangMills.RG

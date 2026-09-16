/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116R1ActiveFactorization
import YangMills.RG.BalabanCMP116SourceRestrictedVisitedDeterminantBound
import YangMills.RG.BalabanCMP116SourcePi4FullComplexR2

/-!
# Source-restricted active factorization of complex `R1`

The restricted visited-resolvent factorization of the covariance defect is
inserted into the exact source identities for `R2`, `R3`, and the three-term
`R1` telescope.  The result is an existential factorization over a fixed,
source-defined active type.  The rectangular legs are constructed inside the
proof; callers cannot substitute a synthetic finite-rank model.

The only intermediate equality exposed here is the exact resolvent identity
for `R2`.  A physical wrapper will discharge it from contour
nonsingularity and Neumann smallness.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

attribute [local instance] Classical.propDecidable

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Three telescope copies of the literal restricted covariance active
state. -/
abbrev CMP116SourceRestrictedR1ActiveState
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q))) :=
  CMP116R1TelescopeActiveState
    (CMP116SourceRestrictedActiveDeterminantState
      (M := M) (Nc := Nc) anchor carrier)

/-- Twelve copies after taking the symmetric entrywise-real part required
by the exact outer Gaussian. -/
abbrev CMP116SourceRestrictedR1SymmetricRealActiveState
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q))) :=
  CMP116R1SymmetricRealActiveState
    (CMP116SourceRestrictedActiveDeterminantState
      (M := M) (Nc := Nc) anchor carrier)

set_option maxHeartbeats 3000000 in
/-- The literal source-complex `R1` factors through three copies of the
restricted visited covariance state. -/
theorem cmp116SourcePi4FullComplexR1Matrix_restricted_exists_activeFactorization_of_r2
    {nContour M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
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
          (fun _ => 1) ^ n)
    (hbase :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) =
        cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK)
    (hR2 :
      let sigma := cmp116SourceRestrictedShiftedCoupling carrier e z
      cmp116SourcePi4FullComplexR2Matrix
          (R := R) anchor K hc hmass hK sigma =
        cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
            (R := R) anchor K hc hmass hK sigma *
          (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK sigma -
            cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK (fun _ => 1)) *
          cmp116PhysicalEndomorphismComplexMatrix K) :
    ∃ L :
        Matrix
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
          (CMP116SourceRestrictedR1ActiveState
            (M := M) (Nc := Nc) anchor carrier) ℂ,
      ∃ Rleg :
        Matrix
          (CMP116SourceRestrictedR1ActiveState
            (M := M) (Nc := Nc) anchor carrier)
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ,
        cmp116SourcePi4FullComplexR1Matrix
            (R := R) anchor K root hc hmass hK Z0
              (cmp116SourceRestrictedShiftedCoupling carrier e z) =
          L * Rleg := by
  let sigma := cmp116SourceRestrictedShiftedCoupling carrier e z
  let domainActive := cmp116SourcePi4RestrictedDomainActive anchor
  let successors :=
    cmp99PhysicalPatchSuccessorSteps
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (cmp99SourcePi4ChartCore (M := M))
      cmp99SourcePi4ChartEnlarged physicalBondDist R
  let R0 := cmp116SourcePi4RestrictedHeadMatrix K hc hmass hK
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
    cmp116RestrictedTransferTargetActive
      (Label := Unit) carrier domainActive
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
  let C0 :=
    cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK
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
  have hC : C1 - C0 = A * B := by
    have hfactor :=
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_restricted_sub_one_eq_finiteFactorization
        (R := R) anchor K hc hmass hK carrier e z hsum hsumOne
    rw [hbase] at hfactor
    simpa [sigma, domainActive, successors, R0, continuation, Tnew, Tbase,
      Nnew, Nbase, p, AHead, BHead, ADynamic, BDynamic, A, B, C0, C1]
      using hfactor
  have hG : G1 - G0 = U * (A * B) * V := by
    have hsource :=
      cmp116SourcePi4FullComplexR3Matrix_eq_neg_constraint_mul_R2
        (R := R) anchor K root hc hmass hK Z0 sigma
    have hR2' :
        cmp116SourcePi4FullComplexR2Matrix
            (R := R) anchor K hc hmass hK sigma =
          P1 * (C1 - C0) * P0 := by
      simpa [sigma, P0, P1, C0, C1, hbase] using hR2
    change
      cmp116SourcePi4FullComplexR3Matrix
          (R := R) anchor K root hc hmass hK Z0 sigma =
        U * (A * B) * V
    rw [hsource, hR2', hC]
    simp only [U, V, constraint, complement, rootMatrix]
    noncomm_ring
  let L :=
    Matrix.r1TelescopeFactorLeft G0 C0 U V A B
  let Rleg :=
    Matrix.r1TelescopeFactorRight G1 C1 U V A B
  refine ⟨L, Rleg, ?_⟩
  have hfactor :=
    Matrix.r1TelescopeFactorLeft_mul_right
      G0 G1 C0 C1 U V A B hC hG
  rw [cmp116SourcePi4FullComplexR1Matrix]
  simpa [sigma, C0, C1, G0, G1, L, Rleg] using hfactor.symm

set_option maxHeartbeats 4000000 in
/-- Physical source wrapper: contour invertibility and Neumann smallness
produce both exact equalities required above, so the public conclusion
contains no supplied covariance or `R2` factorization. -/
theorem cmp116SourcePi4FullComplexR1Matrix_restricted_exists_activeFactorization
    {nContour M Q Nc R Delta : ℕ}
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
    (Z0 : Finset (FinBox 4 (2 * Q)))
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
          (fun _ => 1) ^ n)
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
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d,
      ‖cmp116SourceRestrictedShiftedCoupling carrier e z d - 1‖ ≤
        radius)
    (hcap : ∀ d,
      ‖cmp116SourceRestrictedShiftedCoupling carrier e z d‖ ≤
        Rweak)
    (hseries :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius Rweak < 1) :
    ∃ L :
        Matrix
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
          (CMP116SourceRestrictedR1ActiveState
            (M := M) (Nc := Nc) anchor carrier) ℂ,
      ∃ Rleg :
        Matrix
          (CMP116SourceRestrictedR1ActiveState
            (M := M) (Nc := Nc) anchor carrier)
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ,
        cmp116SourcePi4FullComplexR1Matrix
            (R := R) anchor K root hc hmass hK Z0
              (cmp116SourceRestrictedShiftedCoupling carrier e z) =
          L * Rleg := by
  have hbase :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      (R := R) anchor K hsourceRange hfiniteRange hc hmass hK hD
  have hR2 :=
    cmp116SourcePi4FullComplexR2Matrix_eq_resolventProduct
      (R := R) anchor K hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1
      (cmp116SourceRestrictedShiftedCoupling carrier e z)
      hradius hRweak hdiff hcap hseries hneumann
  exact
    cmp116SourcePi4FullComplexR1Matrix_restricted_exists_activeFactorization_of_r2
      anchor K root hc hmass hK Z0 carrier e z hsum hsumOne
      hbase hR2

end

end YangMills.RG

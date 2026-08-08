/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedVisitedResolventFactorization
import YangMills.RG.BalabanCMP116SourceRestrictedVisitedTransferSummability

/-!
# Physical producer for the restricted active-state determinant

The two transfer-power summability hypotheses formerly required by the
finite active-state determinant are now generated from the literal source
`Pi^4` branching, active budget, and physical fixed-rate walk certificate.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

attribute [local instance] Classical.propDecidable

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 2000000

/-- Source active-state determinant identity with transfer summability
constructed internally from physical walk data. -/
theorem cmp116SourceRestrictedContour_logDetDensity_sq_mul_activeStateDet_eq_one_of_physicalWalks
    {nContour M Q Nc R Δ : ℕ}
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
    {Ahead rho rate : ℝ}
    (hrho : 0 ≤ rho) (hrate : 0 < rate)
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (Rweak : ℝ) (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d ∈ carrier,
      ‖cmp116SourceRestrictedShiftedCoupling carrier e z d‖ ≤ Rweak)
    (hseries :
      (cmp116SourcePi4TerminalBranching Δ : ℝ) *
        rho * Rweak ^ 10000 < 1) :
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
  have hsum :
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
          (cmp116SourceRestrictedShiftedCoupling carrier e z) ^ n :=
    summable_cmp116SourcePi4RestrictedVisitedTransferMatrix_pow
      anchor K hsourceRange hc hmass hK hrho hrate hgeom Cert htri
      hΔ hΔ1 carrier
      (cmp116SourceRestrictedShiftedCoupling carrier e z)
      Rweak hRweak hcap hseries
  have hcapOne : ∀ d ∈ carrier, ‖(1 : ℂ)‖ ≤ Rweak := by
    intro d hd
    simpa using hRweak
  have hsumOne :
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
          (fun _ => 1) ^ n :=
    summable_cmp116SourcePi4RestrictedVisitedTransferMatrix_pow
      anchor K hsourceRange hc hmass hK hrho hrate hgeom Cert htri
      hΔ hΔ1 carrier (fun _ => 1)
      Rweak hRweak hcapOne hseries
  exact
    cmp116SourceRestrictedContour_logDetDensity_sq_mul_activeStateDet_eq_one
      anchor K hsourceRange hrange hc hmass hK hD carrier e z hsmall
      hsum hsumOne

end

end YangMills.RG

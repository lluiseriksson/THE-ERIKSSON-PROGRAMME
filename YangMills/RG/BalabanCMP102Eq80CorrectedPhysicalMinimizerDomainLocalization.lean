/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80CorrectedPhysicalMinimizerLocalizedTelescoping
import YangMills.RG.BalabanCMP102Eq80PhysicalMinimizerDomainLocalization

/-!
# Corrected physical minimizer localized by complete domains

This specializes the domain-localized nonlinear increment to the interacting
Wilson precision, the unique physical CMP102 background correction and
complete weakening coupling.  The terminal convergence theorem therefore has
no arbitrary precision, correction map or weakening field.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- One corrected nonlinear increment written as complete coefficients of
literal physical domains. -/
noncomputable def
    cmp102Eq80CorrectedSourcePi4PhysicalDomainLocalizedMinimizerIncrement
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass coarseRate : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (anchor : FinBox 4 Q)
    (hmass : 0 < mass)
    (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) (fun _ => 1)) coarseRate)
    (ρ radius r s : FineField M Q Nc → ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) (r A) (s A))
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (neumannLength : ℕ)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A' : FineField M Q Nc) : ℝ :=
  cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrement
    (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
    (sub_pos.mpr hbudget) hmass
    (isCoerciveCLM_interactingPhysicalBasePrecision
      U ha hP hε hsmall)
    (cmp99SourcePi4WeakenedCoarseCovariance
      (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
      (sub_pos.mpr hbudget) hmass
      (isCoerciveCLM_interactingPhysicalBasePrecision
        U ha hP hε hsmall)
      (fun _ => 1) hcoarseRate hcoarse)
    (fun _ => 1) neumannLength
    (cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius r s S hcontract)
    D₃ V₀ Δπ J A'

/-- Ordered sums of the corrected complete-domain increments converge to the
literal corrected equation-(80) potential at the physical minimizer. -/
theorem
    tendsto_sum_cmp102Eq80CorrectedSourcePi4PhysicalDomainLocalizedMinimizerIncrements
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (anchor : FinBox 4 Q)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange : PhysicalCovarianceFiniteRange
      (interactingPhysicalBasePrecisionCLM U a) physicalBondDist R)
    (hmass : 0 < mass)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (interactingPhysicalBasePrecisionCLM U a)
          cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          (sub_pos.mpr hbudget) hmass
          (isCoerciveCLM_interactingPhysicalBasePrecision
            U ha hP hε hsmall)‖ < 1)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) (fun _ => 1)) coarseRate)
    {Ahead walkRho rate contourRadius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hwalkRho : 0 ≤ walkRho)
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (interactingPhysicalBasePrecisionCLM U a)
      cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      (sub_pos.mpr hbudget) hmass
      (isCoerciveCLM_interactingPhysicalBasePrecision
        U ha hP hε hsmall)
      physicalBondDist Ahead walkRho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (hcontourRadius : 0 ≤ contourRadius) (hRweak : 1 ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ walkRho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
          (sub_pos.mpr hbudget) hmass
          (isCoerciveCLM_interactingPhysicalBasePrecision
            U ha hP hε hsmall)
          (fun _ => 1) hcoarseRate hcoarse)
        Δ Ahead walkRho rate contourRadius Rweak < 1)
    (ρ radius r s : FineField M Q Nc → ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) (r A) (s A))
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A' : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀) :
    Filter.Tendsto
      (fun n =>
        ∑ i ∈ Finset.range n,
          cmp102Eq80CorrectedSourcePi4PhysicalDomainLocalizedMinimizerIncrement
            (R := R) U ha hP hε hsmall hbudget anchor
            hmass hcoarseRate hcoarse ρ radius r s S hcontract
            i D₃ V₀ Δπ J A')
      Filter.atTop
      (nhds
        (cmp102Eq80CorrectedPhysicalGlobalPotential
            U ha hP hε hsmall hbudget ρ radius r s S hcontract
            D₃ V₀ Δπ J A' -
          cmp102Eq80GlobalPotential
            (cmp102Eq80PhysicalBackgroundCorrection
              U ha hP hε hsmall hbudget ρ radius r s S hcontract)
            D₃ V₀ 0 Δπ J A')) := by
  let K := interactingPhysicalBasePrecisionCLM U a
  let hc := sub_pos.mpr hbudget
  let hK := isCoerciveCLM_interactingPhysicalBasePrecision
    U ha hP hε hsmall
  let D := cmp102Eq80PhysicalBackgroundCorrection
    U ha hP hε hsmall hbudget ρ radius r s S hcontract
  have hdiff : ∀ d : FinBox 4 (2 * Q),
      ‖(1 : ℂ) - 1‖ ≤ contourRadius := by
    intro d
    simp [hcontourRadius]
  have hcap : ∀ d : FinBox 4 (2 * Q), ‖(1 : ℂ)‖ ≤ Rweak := by
    intro d
    simpa using hRweak
  have htend :=
    tendsto_sum_cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrements
      (R := R) (Δ := Δ) anchor K hsourceRange hfiniteRange
      hc hmass hK hD hcoarseRate hcoarse
      hAhead hwalkRho hrate hgeom Cert htri hΔ hΔ1
      (fun _ => 1) hcontourRadius hRweak hdiff hcap
      hcontourSmall hcoarseSmall D D₃ V₀ Δπ J A' hV₀
  rw [
    cmp99SourcePi4PhysicalFullBackgroundMinimizer_one_eq_physicalH
      U ha hP hε hsmall hbudget anchor hsourceRange hfiniteRange
      hmass hD hcoarseRate hcoarse] at htend
  simpa [
    cmp102Eq80CorrectedSourcePi4PhysicalDomainLocalizedMinimizerIncrement,
    cmp102Eq80CorrectedPhysicalGlobalPotential,
    cmp102Eq80PhysicalGlobalPotential,
    K, hc, hK, D] using htend

end

end YangMills.RG

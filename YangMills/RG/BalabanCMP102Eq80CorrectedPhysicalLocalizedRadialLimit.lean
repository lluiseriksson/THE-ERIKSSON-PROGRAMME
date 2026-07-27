/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80CorrectedPhysicalMinimizerLocalizedTelescoping
import YangMills.RG.BalabanCMP102Eq80CorrectedPhysicalBackgroundDependentRadial

/-!
# Localized physical expansion converges to the radial CMP102 sector

This file composes the exact physical minimizer reconstruction with the
radial Taylor identity for precisely the background-dependent part of the
corrected equation-(80) potential.

It does not identify this sector with the complete domain activity
`V_k(Y, ·)` and does not choose the separate source residual `V''_k`.
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

private abbrev FineEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FineField M Q Nc →L[ℝ] FineField M Q Nc

/-- The ordered localized physical increments converge directly to the
radial quadratic form of the background-dependent CMP102 sector. -/
theorem
    tendsto_sum_cmp102Eq80CorrectedSourcePi4PhysicalLocalizedIncrements_to_radial
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
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J A' : FineField M Q Nc)
    (hD₃smooth : ContDiff ℝ ⊤ D₃) (hV₀smooth : ContDiff ℝ ⊤ V₀)
    (hD₃0 : D₃ 0 = 0)
    (hD₃ : HasFDerivAt D₃
      (0 : FineField M Q Nc →L[ℝ] CoarseField Q Nc) 0)
    (hV₀0 : V₀ 0 = 0)
    (hV₀ : HasFDerivAt V₀
      (0 : FineField M Q Nc →L[ℝ] ℝ) 0) :
    Filter.Tendsto
      (fun n =>
        ∑ i ∈ Finset.range n,
          cmp102Eq80CorrectedSourcePi4PhysicalLocalizedMinimizerIncrement
            (R := R) U ha hP hε hsmall hbudget anchor
            hmass hcoarseRate hcoarse ρ radius
            (fun _ => r₀) (fun _ => s₀) S hcontract
            i D₃ V₀ Δπ J A')
      Filter.atTop
      (nhds
        ((1 / 2 : ℝ) * inner ℝ A'
          (cmp102Eq80CorrectedPhysicalBackgroundDependentRadialOperator
            U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hρ hcontract
            D₃ V₀ Δπ J hD₃smooth hV₀smooth A' A'))) := by
  have htend :=
    tendsto_sum_cmp102Eq80CorrectedSourcePi4PhysicalLocalizedMinimizerIncrements
      (R := R) (Δ := Δ) U ha hP hε hsmall hbudget anchor
      hsourceRange hfiniteRange hmass hD hcoarseRate hcoarse
      hAhead hwalkRho hrate hgeom Cert htri hΔ hΔ1
      hcontourRadius hRweak hcontourSmall hcoarseSmall
      ρ radius (fun _ => r₀) (fun _ => s₀) S hcontract
      D₃ V₀ Δπ J A' (hV₀smooth.of_le le_top)
  have hradial :=
    cmp102Eq80CorrectedPhysicalBackgroundDependentPotential_eq_radial
      U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hρ hcontract
      D₃ V₀ Δπ J hD₃smooth hV₀smooth hD₃0 hD₃ hV₀0 hV₀ A'
  rw [← hradial]
  simpa [
    cmp102Eq80CorrectedPhysicalBackgroundDependentPotential] using htend

end

end YangMills.RG

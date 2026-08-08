/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4RectangularWeakenedPotential
import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionFirstOrder
import YangMills.RG.BalabanCMP102Eq80CorrectedPhysicalRegularity
import YangMills.RG.BalabanCMP116RadialTaylorOperator

/-!
# Radial equation-(1.42) operator for the rectangular source weakening

This module combines the physically selected CMP102 background correction
with the source-faithful rectangular weakened minimizer

`H(s) = G(s) Q* (Q G(s) Q*)⁻¹`.

Normalization, first-order vanishing, and `C²` regularity in the fine field
are generated from the physical correction.  Hence the radial Taylor
operator is attached to the correctly typed weakened equation-(80)
potential.  At full coupling this potential is literally the corrected
physical CMP102 potential.
-/

namespace YangMills.RG

open YangMills Filter
open scoped RealInnerProductSpace Topology

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

/-- Corrected equation-(80) potential with the literal rectangular source
weakening. -/
noncomputable def
    cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (anchor : FinBox 4 Q)
    (hmass : 0 < mass)
    (weakening : FinBox 4 (2 * Q) → ℝ)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) weakening) coarseRate)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J A : FineField M Q Nc) : ℝ :=
  cmp102Eq80SourcePi4RectangularWeakenedPotential
    (R := R) U ha hP hε hsmall hbudget anchor hmass
    weakening hcoarseRate hcoarse
    (cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r₀) (fun _ => s₀) S hcontract)
    D₃ V₀ Δπ J A

/-- At full coupling the corrected weakened potential is exactly the
corrected physical equation-(80) potential. -/
theorem
    cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential_one_eq_physical
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (anchor : FinBox 4 Q)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange
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
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J A : FineField M Q Nc) :
    cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
        (R := R) U ha hP hε hsmall hbudget
        ρ radius r₀ s₀ S hcontract anchor hmass
        (fun _ => 1) hcoarseRate hcoarse D₃ V₀ Δπ J A =
      cmp102Eq80CorrectedPhysicalGlobalPotential
        U ha hP hε hsmall hbudget ρ radius
        (fun _ => r₀) (fun _ => s₀) S hcontract D₃ V₀ Δπ J A := by
  unfold cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
  unfold cmp102Eq80CorrectedPhysicalGlobalPotential
  exact
    cmp102Eq80SourcePi4RectangularWeakenedPotential_one_eq_physical
      U ha hP hε hsmall hbudget anchor hsourceRange hrange hmass hD
      hcoarseRate hcoarse
      (cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r₀) (fun _ => s₀) S hcontract)
      D₃ V₀ Δπ J A

/-- Normalization at the origin is generated by the physical correction. -/
theorem
    cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential_zero
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (anchor : FinBox 4 Q) (hmass : 0 < mass)
    (weakening : FinBox 4 (2 * Q) → ℝ)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) weakening) coarseRate)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J : FineField M Q Nc)
    (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
      (R := R) U ha hP hε hsmall hbudget
      ρ radius r₀ s₀ S hcontract anchor hmass
      weakening hcoarseRate hcoarse D₃ V₀ Δπ J 0 = 0 := by
  exact
    cmp102Eq80SourcePi4RectangularWeakenedPotential_zero
      U ha hP hε hsmall hbudget anchor hmass weakening
      hcoarseRate hcoarse
      (cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r₀) (fun _ => s₀) S hcontract)
      D₃ V₀ Δπ J
      (cmp102Eq80PhysicalBackgroundCorrection_zero
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r₀) (fun _ => s₀) S hcontract)
      hD₃0 hV₀0

/-- `C²` regularity in the fine field, generated without a regularity
premise for the implicit physical correction. -/
theorem
    contDiff_two_cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (anchor : FinBox 4 Q) (hmass : 0 < mass)
    (weakening : FinBox 4 (2 * Q) → ℝ)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) weakening) coarseRate)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J : FineField M Q Nc)
    (hD₃ : ContDiff ℝ ⊤ D₃) (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ 2
      (cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
        (R := R) U ha hP hε hsmall hbudget
        ρ radius r₀ s₀ S hcontract anchor hmass
        weakening hcoarseRate hcoarse D₃ V₀ Δπ J) := by
  have hDtwo : ContDiff ℝ 2
      (cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r₀) (fun _ => s₀) S hcontract) :=
    (contDiff_top_cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hρ hcontract).of_le le_top
  have hD₃two : ContDiff ℝ 2 D₃ := hD₃.of_le le_top
  have hV₀two : ContDiff ℝ 2 V₀ := hV₀.of_le le_top
  exact
    contDiff_two_cmp102Eq80SourcePi4RectangularWeakenedPotential
      U ha hP hε hsmall hbudget anchor hmass weakening
      hcoarseRate hcoarse
      (cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r₀) (fun _ => s₀) S hcontract)
      D₃ V₀ Δπ J
      hDtwo hD₃two hV₀two

set_option maxHeartbeats 10000000 in
/-- First-order vanishing with no derivative premise for the implicit
physical correction. -/
theorem
    cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential_hasFDerivAt_zero
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (anchor : FinBox 4 Q) (hmass : 0 < mass)
    (weakening : FinBox 4 (2 * Q) → ℝ)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) weakening) coarseRate)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J : FineField M Q Nc)
    (hD₃0 : D₃ 0 = 0)
    (hD₃ : HasFDerivAt D₃
      (0 : FineField M Q Nc →L[ℝ] CoarseField Q Nc) 0)
    (hV₀ : HasFDerivAt V₀
      (0 : FineField M Q Nc →L[ℝ] ℝ) 0) :
    HasFDerivAt
      (cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
        (R := R) U ha hP hε hsmall hbudget
        ρ radius r₀ s₀ S hcontract anchor hmass
        weakening hcoarseRate hcoarse D₃ V₀ Δπ J)
      (0 : FineField M Q Nc →L[ℝ] ℝ) 0 := by
  let D :=
    cmp102Eq80PhysicalBackgroundCorrection
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r₀) (fun _ => s₀) S hcontract
  let K :=
    cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant
      U ha hP hε hsmall hbudget ρ radius
      (fun _ => r₀) (fun _ => s₀) S 0
  have hrate :
      0 ≤ cmp102PhysicalCorrectionContractionRate Nc 4 M r₀ s₀ :=
    cmp102PhysicalCorrectionContractionRate_nonneg
      r₀ s₀ (S 0).r_nonneg (S 0).s_nonneg
  have hdenom :
      0 < 1 - ((S 0).toBallData).contractionRate :=
    sub_pos.mpr (hcontract 0)
  have hK0 : 0 ≤ K := by
    unfold K cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant
    positivity
  have hK : ∀ᶠ A in 𝓝 0,
      cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant
        U ha hP hε hsmall hbudget ρ radius
        (fun _ => r₀) (fun _ => s₀) S A ≤ K := by
    filter_upwards [] with A
    exact le_of_eq (by
      unfold K cmp102Eq80PhysicalBackgroundCorrectionLinearGrowthConstant
      rfl)
  have hDgrowth : ∀ᶠ A in 𝓝 0, ‖D A‖ ≤ K * ‖A‖ := by
    filter_upwards [hK] with A hKA
    exact
      (norm_cmp102Eq80PhysicalBackgroundCorrection_le
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r₀) (fun _ => s₀) S hcontract A).trans
        (mul_le_mul_of_nonneg_right hKA (norm_nonneg A))
  unfold cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
  exact cmp102Eq80GlobalPotential_hasFDerivAt_zero_of_linearGrowth
    D D₃ V₀
    (cmp99SourcePi4WeakenedPhysicalH
      (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
      (sub_pos.mpr hbudget) hmass
      (isCoerciveCLM_interactingPhysicalBasePrecision
        U ha hP hε hsmall) weakening hcoarseRate hcoarse)
    Δπ J K hK0
    (cmp102Eq80PhysicalBackgroundCorrection_zero
      U ha hP hε hsmall hbudget ρ radius
        (fun _ => r₀) (fun _ => s₀) S hcontract)
    hD₃0 hDgrowth hD₃ hV₀

/-- Radial Taylor operator for the correctly typed corrected weakening. -/
noncomputable def
    cmp102Eq80CorrectedSourcePi4RectangularRadialOperator
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (anchor : FinBox 4 Q) (hmass : 0 < mass)
    (weakening : FinBox 4 (2 * Q) → ℝ)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) weakening) coarseRate)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J : FineField M Q Nc)
    (hD₃ : ContDiff ℝ ⊤ D₃) (hV₀ : ContDiff ℝ ⊤ V₀)
    (A : FineField M Q Nc) :
    FineEndomorphism M Q Nc :=
  cmp116RadialTaylorOperator
    (cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
      (R := R) U ha hP hε hsmall hbudget
      ρ radius r₀ s₀ S hcontract anchor hmass
      weakening hcoarseRate hcoarse D₃ V₀ Δπ J)
    A
    (contDiff_two_cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
      U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hρ hcontract
      anchor hmass weakening hcoarseRate hcoarse D₃ V₀ Δπ J hD₃ hV₀)

set_option maxHeartbeats 10000000 in
/-- Exact equation-(1.42) radial identity for the source-faithful
rectangular weakened potential. -/
theorem
    cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential_eq_radial
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (anchor : FinBox 4 Q) (hmass : 0 < mass)
    (weakening : FinBox 4 (2 * Q) → ℝ)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) weakening) coarseRate)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J : FineField M Q Nc)
    (hD₃smooth : ContDiff ℝ ⊤ D₃) (hV₀smooth : ContDiff ℝ ⊤ V₀)
    (hD₃0 : D₃ 0 = 0)
    (hD₃ : HasFDerivAt D₃
      (0 : FineField M Q Nc →L[ℝ] CoarseField Q Nc) 0)
    (hV₀0 : V₀ 0 = 0)
    (hV₀ : HasFDerivAt V₀
      (0 : FineField M Q Nc →L[ℝ] ℝ) 0)
    (A : FineField M Q Nc) :
    cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
        (R := R) U ha hP hε hsmall hbudget
        ρ radius r₀ s₀ S hcontract anchor hmass
        weakening hcoarseRate hcoarse D₃ V₀ Δπ J A =
      (1 / 2 : ℝ) * inner ℝ A
        (cmp102Eq80CorrectedSourcePi4RectangularRadialOperator
          (R := R) U ha hP hε hsmall hbudget
          ρ radius r₀ s₀ S hρ hcontract anchor hmass
          weakening hcoarseRate hcoarse D₃ V₀ Δπ J
          hD₃smooth hV₀smooth A A) := by
  let f :=
    cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
      (R := R) U ha hP hε hsmall hbudget
      ρ radius r₀ s₀ S hcontract anchor hmass
      weakening hcoarseRate hcoarse D₃ V₀ Δπ J
  have hsmooth : ContDiff ℝ 2 f :=
    contDiff_two_cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential
      U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hρ hcontract
      anchor hmass weakening hcoarseRate hcoarse
      D₃ V₀ Δπ J hD₃smooth hV₀smooth
  have hf0 : f 0 = 0 := by
    exact cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential_zero
      U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hcontract
      anchor hmass weakening hcoarseRate hcoarse
      D₃ V₀ Δπ J hD₃0 hV₀0
  have hdf0 : fderiv ℝ f 0 = 0 :=
    (cmp102Eq80CorrectedSourcePi4RectangularWeakenedPotential_hasFDerivAt_zero
      U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hcontract
      anchor hmass weakening hcoarseRate hcoarse
      D₃ V₀ Δπ J hD₃0 hD₃ hV₀).fderiv
  simpa [f, cmp102Eq80CorrectedSourcePi4RectangularRadialOperator] using
    cmp116RadialTaylorOperator_eq_of_normalized f A hsmooth hf0 hdf0

end

end YangMills.RG

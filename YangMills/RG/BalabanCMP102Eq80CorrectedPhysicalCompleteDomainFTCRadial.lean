/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCompleteDomainFTCReassembly
import YangMills.RG.BalabanCMP102Eq80CorrectedPhysicalMinimizerLocalizedTelescoping
import YangMills.RG.BalabanCMP102Eq80CorrectedPhysicalBackgroundDependentRadial

/-!
# Corrected physical complete-domain FTC series and its radial limit

The complete source-ordered domain FTC reassembly is specialized here to
the interacting Wilson precision, complete weakening `sigma = 1`, and the
unique physical CMP102 correction.

The resulting finite sum of complete domain series is identified first
with the literal background-dependent equation-(80) potential and then
with its radial Taylor quadratic form.  This is an equality of complete
sums.  No termwise identification with the separate Faà di Bruno
connected-domain activities is asserted.
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

/-- The source-faithful activity attached to one finite domain is the
complete outer Neumann sum of the literal FTC coefficient of that domain.

This is the summand that occurs in the physical reassembly theorem.  It is
not identified post hoc with the separate recursive connected-domain
activity. -/
noncomputable def
    cmp102Eq80CorrectedPhysicalCompleteDomainFTCActivity
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
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q))) : ℝ :=
  let K := interactingPhysicalBasePrecisionCLM U a
  let hc := sub_pos.mpr hbudget
  let hK := isCoerciveCLM_interactingPhysicalBasePrecision
    U ha hP hε hsmall
  let baseCoarseCovariance :=
    cmp99SourcePi4WeakenedCoarseCovariance
      (R := R) anchor K hc hmass hK (fun _ => 1)
      hcoarseRate hcoarse
  let D := cmp102Eq80PhysicalBackgroundCorrection
    U ha hP hε hsmall hbudget ρ radius
      (fun _ => r₀) (fun _ => s₀) S hcontract
  let term : ℕ → (CoarseField Q Nc →L[ℝ] FineField M Q Nc) :=
    fun n =>
      cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance (fun _ => 1) n
  ∑' n : ℕ,
    cmp102Eq80PhysicalNeumannDomainFTCContribution
      (R := R) (n := n) anchor K hc hmass hK
      baseCoarseCovariance (fun _ => 1) D D₃ V₀
      (cmp102Eq80MinimizerPartialSum term n) (term n)
      Δπ J A Y

/-- The literal complete-domain FTC series after specializing every
structural input to the corrected interacting-Wilson producer. -/
noncomputable def
    cmp102Eq80CorrectedPhysicalCompleteDomainFTCSeries
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
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J A : FineField M Q Nc) : ℝ :=
  ∑ Y : Finset (FinBox 4 (2 * Q)),
    cmp102Eq80CorrectedPhysicalCompleteDomainFTCActivity
      (R := R) U ha hP hε hsmall hbudget anchor
      hmass hcoarseRate hcoarse ρ radius r₀ s₀ S hcontract
      D₃ V₀ Δπ J A Y

/-- A source-specialized complete-domain activity vanishes outside the
nonempty face-connected physical localization domains. -/
theorem
    cmp102Eq80CorrectedPhysicalCompleteDomainFTCActivity_eq_zero_of_not_localizationDomain
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
    (ρ radius : FineField M Q Nc → ℝ)
    (r₀ s₀ : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r₀ s₀)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hY : ¬(Y.Nonempty ∧
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y)) :
    cmp102Eq80CorrectedPhysicalCompleteDomainFTCActivity
        (R := R) U ha hP hε hsmall hbudget anchor
        hmass hcoarseRate hcoarse ρ radius r₀ s₀ S hcontract
        D₃ V₀ Δπ J A Y = 0 := by
  unfold cmp102Eq80CorrectedPhysicalCompleteDomainFTCActivity
  calc
    (∑' n : ℕ,
      cmp102Eq80PhysicalNeumannDomainFTCContribution
        (R := R) (n := n) anchor
        (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
          (sub_pos.mpr hbudget) hmass
          (isCoerciveCLM_interactingPhysicalBasePrecision
            U ha hP hε hsmall)
          (fun _ => 1) hcoarseRate hcoarse)
        (fun _ => 1)
        (cmp102Eq80PhysicalBackgroundCorrection
          U ha hP hε hsmall hbudget ρ radius
            (fun _ => r₀) (fun _ => s₀) S hcontract)
        D₃ V₀
        (cmp102Eq80MinimizerPartialSum
          (fun n =>
            cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
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
              (fun _ => 1) n) n)
        (cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
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
          (fun _ => 1) n)
        Δπ J A Y) = ∑' _n : ℕ, 0 := by
      apply tsum_congr
      intro n
      exact
        cmp102Eq80PhysicalNeumannDomainFTCContribution_eq_zero_of_not_localizationDomain
          (M := M) (Q := Q) (Nc := Nc) (R := R) (n := n)
          anchor (interactingPhysicalBasePrecisionCLM U a)
          (sub_pos.mpr hbudget) hmass
          (isCoerciveCLM_interactingPhysicalBasePrecision
            U ha hP hε hsmall)
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
            (sub_pos.mpr hbudget) hmass
            (isCoerciveCLM_interactingPhysicalBasePrecision
              U ha hP hε hsmall)
            (fun _ => 1) hcoarseRate hcoarse)
          (fun _ => 1)
          (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius
              (fun _ => r₀) (fun _ => s₀) S hcontract)
          D₃ V₀
          (cmp102Eq80MinimizerPartialSum
            (fun n =>
              cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
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
                (fun _ => 1) n) n)
          (cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
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
            (fun _ => 1) n)
          Δπ J A Y hY
    _ = 0 := tsum_zero

set_option maxHeartbeats 8000000 in
/-- Every source-faithful corrected physical domain activity is absolutely
controlled by the complete source-metric outer-Neumann majorant.

Unlike an equality obtained only after summing over all domains, this bound
applies to the literal activity attached to the given physical localization
domain.  The constant is uniform in that domain and is generated by the
source walk estimates. -/
theorem
    exists_uniform_bound_cmp102Eq80CorrectedPhysicalCompleteDomainFTCActivity
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
    (hmass : 0 < mass)
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
    (hcontourRadius : 0 ≤ contourRadius)
    (hRweak : 1 ≤ Rweak)
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
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J A : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀)
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 ≤ κcard)
    (hκmetric : 0 ≤ κmetric)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M)
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
            (sub_pos.mpr hbudget) hmass
            (isCoerciveCLM_interactingPhysicalBasePrecision
              U ha hP hε hsmall)
            (fun _ => 1) hcoarseRate hcoarse)
          Ahead walkRho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hwalkSmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (houterSmall :
      cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
        (Q := Q) (Δ := Δ) summationRatio < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Y : CMP116LocalizationDomain M (2 * Q),
        ‖cmp102Eq80CorrectedPhysicalCompleteDomainFTCActivity
            (R := R) U ha hP hε hsmall hbudget anchor
            hmass hcoarseRate hcoarse ρ radius r₀ s₀ S hcontract
            D₃ V₀ Δπ J A Y.blocks‖ ≤
          cmp102Eq80PhysicalFTCSourceMetricDecayPrefactor
              (M := M)
              (cmp99SourcePi4WeakenedCoarseCovariance
                (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
                (sub_pos.mpr hbudget) hmass
                (isCoerciveCLM_interactingPhysicalBasePrecision
                  U ha hP hε hsmall)
                (fun _ => 1) hcoarseRate hcoarse)
              C κcard κmetric summationRatio Y Δ *
            (1 -
              cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
                (Q := Q) (Δ := Δ) summationRatio)⁻¹ := by
  let K := interactingPhysicalBasePrecisionCLM U a
  let hc := sub_pos.mpr hbudget
  let hK := isCoerciveCLM_interactingPhysicalBasePrecision
    U ha hP hε hsmall
  let D := cmp102Eq80PhysicalBackgroundCorrection
    U ha hP hε hsmall hbudget ρ radius
      (fun _ => r₀) (fun _ => s₀) S hcontract
  have hdiff : ∀ d : FinBox 4 (2 * Q),
      ‖(1 : ℂ) - 1‖ ≤ contourRadius := by
    intro d
    simp [hcontourRadius]
  have hcap : ∀ d : FinBox 4 (2 * Q), ‖(1 : ℂ)‖ ≤ Rweak := by
    intro d
    simpa using hRweak
  obtain ⟨C, hC0, hbound⟩ :=
    exists_uniform_bound_cmp102Eq80SourcePi4PhysicalCompleteDomainFTC
      (R := R) anchor K hsourceRange hc hmass hK
      hcoarseRate hcoarse hAhead hwalkRho hrate hgeom
      Cert htri hΔ hΔ1 (fun _ => 1)
      hcontourRadius hRweak hdiff hcap hcontourSmall hcoarseSmall
      D D₃ V₀ Δπ J A hV₀
      hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
      hsplit hcardDecay hmetricDecay hwalkSmall houterSmall
  refine ⟨C, hC0, ?_⟩
  intro Y
  simpa [
    cmp102Eq80CorrectedPhysicalCompleteDomainFTCActivity,
    K, hc, hK, D] using (hbound Y).2

set_option maxHeartbeats 12000000 in
/-- The complete corrected physical domain FTC series is exactly the
background-dependent part of the literal equation-(80) potential. -/
theorem
    cmp102Eq80CorrectedPhysicalBackgroundDependentPotential_eq_completeDomainFTC_of_source
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
    (hcontourRadius : 0 ≤ contourRadius)
    (hRweak : 1 ≤ Rweak)
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
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineEndomorphism M Q Nc)
    (J A : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀)
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 ≤ κcard)
    (hκmetric : 0 ≤ κmetric)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M)
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
            (sub_pos.mpr hbudget) hmass
            (isCoerciveCLM_interactingPhysicalBasePrecision
              U ha hP hε hsmall)
            (fun _ => 1) hcoarseRate hcoarse)
          Ahead walkRho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hwalkSmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (houterSmall :
      cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
        (Q := Q) (Δ := Δ) summationRatio < 1) :
    cmp102Eq80CorrectedPhysicalBackgroundDependentPotential
        U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hcontract
        D₃ V₀ Δπ J A =
      cmp102Eq80CorrectedPhysicalCompleteDomainFTCSeries
        (R := R) U ha hP hε hsmall hbudget anchor
        hmass hcoarseRate hcoarse ρ radius r₀ s₀ S hcontract
        D₃ V₀ Δπ J A := by
  let K := interactingPhysicalBasePrecisionCLM U a
  let hc := sub_pos.mpr hbudget
  let hK := isCoerciveCLM_interactingPhysicalBasePrecision
    U ha hP hε hsmall
  let D := cmp102Eq80PhysicalBackgroundCorrection
    U ha hP hε hsmall hbudget ρ radius
      (fun _ => r₀) (fun _ => s₀) S hcontract
  have hdiff : ∀ d : FinBox 4 (2 * Q),
      ‖(1 : ℂ) - 1‖ ≤ contourRadius := by
    intro d
    simp [hcontourRadius]
  have hcap : ∀ d : FinBox 4 (2 * Q), ‖(1 : ℂ)‖ ≤ Rweak := by
    intro d
    simpa using hRweak
  have hglobal :=
    cmp102Eq80SourcePi4PhysicalPotentialDifference_eq_sum_completeDomainFTC_of_source
      (R := R) (Δ := Δ) anchor K hsourceRange hfiniteRange
      hc hmass hK hD hcoarseRate hcoarse
      hAhead hwalkRho hrate hgeom Cert htri hΔ hΔ1
      (fun _ => 1) hcontourRadius hRweak hdiff hcap
      hcontourSmall hcoarseSmall D D₃ V₀ Δπ J A hV₀
      hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
      hsplit hcardDecay hmetricDecay hwalkSmall houterSmall
  rw [
    cmp99SourcePi4PhysicalFullBackgroundMinimizer_one_eq_physicalH
      U ha hP hε hsmall hbudget anchor hsourceRange hfiniteRange
      hmass hD hcoarseRate hcoarse] at hglobal
  simpa [
    cmp102Eq80CorrectedPhysicalBackgroundDependentPotential,
    cmp102Eq80CorrectedPhysicalCompleteDomainFTCSeries,
    cmp102Eq80CorrectedPhysicalGlobalPotential,
    cmp102Eq80PhysicalGlobalPotential,
    K, hc, hK, D] using hglobal

set_option maxHeartbeats 12000000 in
/-- The complete corrected physical domain FTC series is exactly the radial
quadratic form of the background-dependent equation-(80) sector. -/
theorem
    cmp102Eq80CorrectedPhysicalCompleteDomainFTCSeries_eq_radial
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
    (hcontourRadius : 0 ≤ contourRadius)
    (hRweak : 1 ≤ Rweak)
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
    (J A : FineField M Q Nc)
    (hD₃smooth : ContDiff ℝ ⊤ D₃)
    (hV₀smooth : ContDiff ℝ ⊤ V₀)
    (hD₃0 : D₃ 0 = 0)
    (hD₃ : HasFDerivAt D₃
      (0 : FineField M Q Nc →L[ℝ] CoarseField Q Nc) 0)
    (hV₀0 : V₀ 0 = 0)
    (hV₀ : HasFDerivAt V₀
      (0 : FineField M Q Nc →L[ℝ] ℝ) 0)
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 ≤ κcard)
    (hκmetric : 0 ≤ κmetric)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M)
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
            (sub_pos.mpr hbudget) hmass
            (isCoerciveCLM_interactingPhysicalBasePrecision
              U ha hP hε hsmall)
            (fun _ => 1) hcoarseRate hcoarse)
          Ahead walkRho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hwalkSmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (houterSmall :
      cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
        (Q := Q) (Δ := Δ) summationRatio < 1) :
    cmp102Eq80CorrectedPhysicalCompleteDomainFTCSeries
        (R := R) U ha hP hε hsmall hbudget anchor
        hmass hcoarseRate hcoarse ρ radius r₀ s₀ S hcontract
        D₃ V₀ Δπ J A =
      (1 / 2 : ℝ) * inner ℝ A
        (cmp102Eq80CorrectedPhysicalBackgroundDependentRadialOperator
          U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hρ hcontract
          D₃ V₀ Δπ J hD₃smooth hV₀smooth A A) := by
  calc
    cmp102Eq80CorrectedPhysicalCompleteDomainFTCSeries
        (R := R) U ha hP hε hsmall hbudget anchor
        hmass hcoarseRate hcoarse ρ radius r₀ s₀ S hcontract
        D₃ V₀ Δπ J A =
      cmp102Eq80CorrectedPhysicalBackgroundDependentPotential
        U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hcontract
        D₃ V₀ Δπ J A := by
          symm
          exact
            cmp102Eq80CorrectedPhysicalBackgroundDependentPotential_eq_completeDomainFTC_of_source
              (R := R) (Δ := Δ) U ha hP hε hsmall hbudget
              anchor hsourceRange hfiniteRange hmass hD
              hcoarseRate hcoarse hAhead hwalkRho hrate hgeom
              Cert htri hΔ hΔ1 hcontourRadius hRweak
              hcontourSmall hcoarseSmall ρ radius r₀ s₀ S hcontract
              D₃ V₀ Δπ J A (hV₀smooth.of_le le_top)
              hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
              hsplit hcardDecay hmetricDecay hwalkSmall houterSmall
    _ = _ :=
      cmp102Eq80CorrectedPhysicalBackgroundDependentPotential_eq_radial
        U ha hP hε hsmall hbudget ρ radius r₀ s₀ S hρ hcontract
        D₃ V₀ Δπ J hD₃smooth hV₀smooth
        hD₃0 hD₃ hV₀0 hV₀ A

end

end YangMills.RG

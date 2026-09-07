/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailSourceMetricFTC
import YangMills.RG.BalabanCMP102Eq80PhysicalOuterNeumannDirectionalBound

/-!
# One source-metric FTC bound for every outer Neumann length

The fixed-length domain theorem formerly required a directional constant
for the particular prefix and next Neumann layer.  Absolute summability
places all such affine segments in one compact ball.  This module consumes
that fact and produces a single constant, valid simultaneously for every
outer length and every physical localization domain.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

set_option maxHeartbeats 4000000 in
/-- One constant controls the literal fixed-domain FTC coefficient at
every physical outer Neumann length.  Both the layer-word summability and
the source-metric decay are produced internally. -/
theorem
    exists_uniform_bound_cmp102Eq80SourcePi4PhysicalOuterNeumannDomainFTC
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor K hc hmass hK (fun _ => 1)) coarseRate)
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
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
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse)
          Ahead rho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (Y : CMP116LocalizationDomain M (2 * Q)),
        let baseCoarseCovariance :=
          cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse
        let term : ℕ → (CoarseField Q Nc →L[ℝ] FineField M Q Nc) :=
          fun neumannLength =>
            cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
              (R := R) anchor K hc hmass hK
              baseCoarseCovariance sigma neumannLength
        let P := cmp102Eq80MinimizerPartialSum term n
        let T := term n
        Summable (fun layerWord : Fin n → ℕ =>
          cmp102Eq80PhysicalLayerWordDomainFTCContribution
            (R := R) anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord D D₃ V₀ P T Δπ J A Y.blocks) ∧
        ‖cmp102Eq80PhysicalNeumannDomainFTCContribution
            (R := R) (n := n) anchor K hc hmass hK
            baseCoarseCovariance sigma D D₃ V₀ P T Δπ J A Y.blocks‖ ≤
          cmp102Eq80PhysicalFTCSourceMetricDecayPrefactor
              (M := M) baseCoarseCovariance
              C κcard κmetric summationRatio Y Δ *
            (cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
              (Q := Q) (Δ := Δ) summationRatio) ^ n := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_uniform_bound_cmp102Eq80SourcePi4OuterNeumannDirectionalDerivative
      anchor K hsourceRange hc hmass hK hcoarseRate hcoarse
      hAhead hrho hrate hgeom Cert htri hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hcontourSmall hcoarseSmall
      D D₃ V₀ Δπ J A hV₀
  refine ⟨C, hC0, ?_⟩
  intro n Y
  let baseCoarseCovariance :=
    cmp99SourcePi4WeakenedCoarseCovariance
      (R := R) anchor K hc hmass hK (fun _ => 1)
      hcoarseRate hcoarse
  let term : ℕ → (CoarseField Q Nc →L[ℝ] FineField M Q Nc) :=
    fun neumannLength =>
      cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma neumannLength
  let P := cmp102Eq80MinimizerPartialSum term n
  let T := term n
  have hCn : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      cmp102Eq80PropagatorDirectionalDerivativeBound
        D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) ≤ C := by
    intro t ht
    simpa [baseCoarseCovariance, term, P, T] using hC n t ht
  simpa [baseCoarseCovariance, term, P, T] using
    (summable_and_norm_cmp102Eq80PhysicalNeumannDomainFTCContribution_le_sourceMetricDecay
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hsourceRange hΔ hΔ1
      sigma hRweak hcap hcontourSmall
      D D₃ V₀ P T Δπ J A Y (C := C) hC0 hCn
      hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
      hsplit hcardDecay hmetricDecay hsmall)

set_option maxHeartbeats 4000000 in
/-- The complete outer Neumann sum below every fixed physical source
domain is absolutely summable.  Its closed geometric bound uses the same
uniform directional constant for all outer lengths. -/
theorem
    exists_uniform_bound_cmp102Eq80SourcePi4PhysicalCompleteDomainFTC
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor K hc hmass hK (fun _ => 1)) coarseRate)
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
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
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse)
          Ahead rho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (houterSmall :
      cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
        (Q := Q) (Δ := Δ) summationRatio < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Y : CMP116LocalizationDomain M (2 * Q),
        let baseCoarseCovariance :=
          cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse
        let term : ℕ → (CoarseField Q Nc →L[ℝ] FineField M Q Nc) :=
          fun neumannLength =>
            cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
              (R := R) anchor K hc hmass hK
              baseCoarseCovariance sigma neumannLength
        let outerTerm := fun n : ℕ =>
          cmp102Eq80PhysicalNeumannDomainFTCContribution
            (R := R) (n := n) anchor K hc hmass hK
            baseCoarseCovariance sigma D D₃ V₀
            (cmp102Eq80MinimizerPartialSum term n) (term n)
            Δπ J A Y.blocks
        Summable outerTerm ∧
        ‖∑' n : ℕ, outerTerm n‖ ≤
          cmp102Eq80PhysicalFTCSourceMetricDecayPrefactor
              (M := M) baseCoarseCovariance
              C κcard κmetric summationRatio Y Δ *
            (1 -
              cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
                (Q := Q) (Δ := Δ) summationRatio)⁻¹ := by
  obtain ⟨C, hC0, hfixed⟩ :=
    exists_uniform_bound_cmp102Eq80SourcePi4PhysicalOuterNeumannDomainFTC
      anchor K hsourceRange hc hmass hK hcoarseRate hcoarse
      hAhead hrho hrate hgeom Cert htri hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hcontourSmall hcoarseSmall
      D D₃ V₀ Δπ J A hV₀
      hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
      hsplit hcardDecay hmetricDecay hsmall
  refine ⟨C, hC0, ?_⟩
  intro Y
  let baseCoarseCovariance :=
    cmp99SourcePi4WeakenedCoarseCovariance
      (R := R) anchor K hc hmass hK (fun _ => 1)
      hcoarseRate hcoarse
  let term : ℕ → (CoarseField Q Nc →L[ℝ] FineField M Q Nc) :=
    fun neumannLength =>
      cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma neumannLength
  let outerTerm := fun n : ℕ =>
    cmp102Eq80PhysicalNeumannDomainFTCContribution
      (R := R) (n := n) anchor K hc hmass hK
      baseCoarseCovariance sigma D D₃ V₀
      (cmp102Eq80MinimizerPartialSum term n) (term n)
      Δπ J A Y.blocks
  let prefactor :=
    cmp102Eq80PhysicalFTCSourceMetricDecayPrefactor
      (M := M) baseCoarseCovariance
      C κcard κmetric summationRatio Y Δ
  let q :=
    cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
      (Q := Q) (Δ := Δ) summationRatio
  have hinnerPos :
      0 < 1 -
        ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
          summationRatio :=
    sub_pos.mpr hsmall
  have hq0 : 0 ≤ q := by
    dsimp [q, cmp102Eq80PhysicalOuterNeumannSourceMetricRatio]
    positivity
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact houterSmall
  have hmajor : Summable fun n : ℕ => prefactor * q ^ n :=
    (summable_geometric_of_norm_lt_one hqnorm).mul_left prefactor
  have hterm (n : ℕ) : ‖outerTerm n‖ ≤ prefactor * q ^ n := by
    exact (hfixed n Y).2
  have hnorm : Summable fun n : ℕ => ‖outerTerm n‖ :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have houter : Summable outerTerm := Summable.of_norm hnorm
  refine ⟨houter, ?_⟩
  calc
    ‖∑' n : ℕ, outerTerm n‖ ≤ ∑' n : ℕ, ‖outerTerm n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, prefactor * q ^ n :=
      Summable.tsum_le_tsum hterm hnorm hmajor
    _ = prefactor * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 houterSmall]
    _ = _ := rfl

end

end YangMills.RG

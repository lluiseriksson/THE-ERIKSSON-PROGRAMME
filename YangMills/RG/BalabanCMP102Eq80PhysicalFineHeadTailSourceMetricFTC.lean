/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailSourceMetricLayerWordSum
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCContributionBound

/-!
# Source decay for the literal equation-(80) FTC contribution

The matrix expansion alone is not the localized activity.  This file
transports its cancellation-free source bound through the literal
equation-(80) functional, with the physical data `D`, `D₃`, `V₀`,
`Δπ`, `J`, and `A` still present.  The dependent choice and layer-word
sums are performed explicitly; no abstract activity bound is assumed.
-/

open scoped RealInnerProductSpace Matrix.Norms.Operator BigOperators

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- The source-decaying prefactor after the literal equation-(80)
functional and physical rectangular reconstruction are included. -/
noncomputable def cmp102Eq80PhysicalFTCSourceMetricDecayPrefactor
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (C κcard κmetric summationRatio : ℝ)
    (Y : CMP116LocalizationDomain M (2 * Q))
    (Δ : ℕ) : ℝ :=
  C *
    ContinuousLinearMap.opNorm
      (cmp99PhysicalRectangularOfComplexMatrixContinuousLinearMap
        (d := 4) (N₁ := 2 * Q) (N₂ := M * (2 * Q)) (Nc := Nc)) *
    cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
      baseCoarseCovariance κcard κmetric summationRatio Y Δ

/-- One literal layer-word FTC contribution is bounded by the same
product-geometric source majorant as the cancellation-free matrix
choice sum. -/
theorem
    norm_cmp102Eq80PhysicalLayerWordDomainFTCContribution_le_sourceMetricProduct
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmallContour :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : CMP116LocalizationDomain M (2 * Q))
    {C cardRatio metricRatio summationRatio κcard κmetric : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      cmp102Eq80PropagatorDirectionalDerivativeBound
        D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) ≤ C)
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 ≤ κcard)
    (hκmetric : 0 ≤ κmetric)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1) :
    ‖cmp102Eq80PhysicalLayerWordDomainFTCContribution
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord D D₃ V₀ P T Δπ J A Y.blocks‖ ≤
      cmp102Eq80PhysicalFTCSourceMetricDecayPrefactor
          (M := M) baseCoarseCovariance
          C κcard κmetric summationRatio Y Δ *
        ∏ i : Fin n,
          (((cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
            summationRatio *
            ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
              summationRatio) ^ layerWord i)) := by
  classical
  let L :=
    cmp99PhysicalRectangularOfComplexMatrixContinuousLinearMap
      (d := 4) (N₁ := 2 * Q) (N₂ := M * (2 * Q)) (Nc := Nc)
  let matrixMajorant : ℝ :=
    cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
        (M := M) baseCoarseCovariance
        κcard κmetric summationRatio Y Δ *
      ∏ i : Fin n,
        (((cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
          summationRatio *
          ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio) ^ layerWord i))
  have hmatrix :
      (∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice Y.blocks‖) ≤ matrixMajorant := by
    simpa [matrixMajorant] using
      sum_norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient_le_sourceMetricProduct
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap layerWord Y
        hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
        hsplit hcardDecay hmetricDecay hsmall
  unfold cmp102Eq80PhysicalLayerWordDomainFTCContribution
  calc
    ‖∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J A Y.blocks‖ ≤
      ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        ‖cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J A Y.blocks‖ :=
      norm_sum_le _ _
    _ ≤
      ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        C * ContinuousLinearMap.opNorm L *
          ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y.blocks‖ := by
      apply Finset.sum_le_sum
      intro choice _hchoice
      calc
        ‖cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ V₀ P T Δπ J A Y.blocks‖ ≤
          C *
            ‖cmp99PhysicalRectangularOfComplexMatrix
              (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
                anchor K hc hmass hK baseCoarseCovariance
                sigma layerWord choice Y.blocks)‖ :=
          norm_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_le
            anchor K hc hmass hK baseCoarseCovariance
            hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
            sigma hRweak hcap hsmallContour layerWord choice
            D D₃ V₀ P T Δπ J A Y.blocks hC
        _ ≤ C * (ContinuousLinearMap.opNorm L *
            ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y.blocks‖) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          simpa [L] using
            L.le_opNorm
              (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
                anchor K hc hmass hK baseCoarseCovariance
                sigma layerWord choice Y.blocks)
        _ = C * ContinuousLinearMap.opNorm L *
            ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y.blocks‖ := by ring
    _ = C * ContinuousLinearMap.opNorm L *
        (∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
          ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y.blocks‖) := by
      rw [Finset.mul_sum]
    _ ≤ C * ContinuousLinearMap.opNorm L * matrixMajorant :=
      mul_le_mul_of_nonneg_left hmatrix
        (mul_nonneg hC0 L.opNorm_nonneg)
    _ = _ := by
      dsimp [matrixMajorant,
        cmp102Eq80PhysicalFTCSourceMetricDecayPrefactor, L]
      ring

/-- Literal fixed-domain FTC coefficient after all dependent coarse
layer words of one outer Neumann length have been summed. -/
noncomputable def cmp102Eq80PhysicalNeumannDomainFTCContribution
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q))) : ℝ :=
  ∑' layerWord : Fin n → ℕ,
    cmp102Eq80PhysicalLayerWordDomainFTCContribution
      (R := R) anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord D D₃ V₀ P T Δπ J A Y

/-- Absolute summability and the closed source-metric bound for the
literal fixed-domain FTC coefficient at one outer Neumann length. -/
theorem
    summable_and_norm_cmp102Eq80PhysicalNeumannDomainFTCContribution_le_sourceMetricDecay
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmallContour :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : CMP116LocalizationDomain M (2 * Q))
    {C cardRatio metricRatio summationRatio κcard κmetric : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      cmp102Eq80PropagatorDirectionalDerivativeBound
        D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) ≤ C)
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 ≤ κcard)
    (hκmetric : 0 ≤ κmetric)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1) :
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
  let prefactor :=
    cmp102Eq80PhysicalFTCSourceMetricDecayPrefactor
      (M := M) baseCoarseCovariance
      C κcard κmetric summationRatio Y Δ
  let productMajorant := fun layerWord : Fin n → ℕ =>
    ∏ i : Fin n,
      (((cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
        summationRatio *
        ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
          summationRatio) ^ layerWord i))
  have hprefactor0 : 0 ≤ prefactor := by
    have hinnerPos :
        0 < 1 -
          ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio :=
      sub_pos.mpr hsmall
    have hlayer0 :
        0 ≤ cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
          (M := M) baseCoarseCovariance
          κcard κmetric summationRatio Y Δ := by
      unfold cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
        cmp102Eq80PhysicalFineHeadTailEndpointMajorant
      positivity
    dsimp [prefactor, cmp102Eq80PhysicalFTCSourceMetricDecayPrefactor]
    exact mul_nonneg
      (mul_nonneg hC0
        (ContinuousLinearMap.opNorm_nonneg
          (cmp99PhysicalRectangularOfComplexMatrixContinuousLinearMap
            (d := 4) (N₁ := 2 * Q) (N₂ := M * (2 * Q))
            (Nc := Nc))))
      hlayer0
  have hproduct : Summable productMajorant := by
    simpa [productMajorant] using
      summable_cmp102Eq80PhysicalLayerWordSourceMetricProduct
        (Q := Q) hsummation0 hsmall
  have hmajor :
      Summable fun layerWord : Fin n → ℕ =>
        prefactor * productMajorant layerWord :=
    hproduct.mul_left prefactor
  have hterm : ∀ layerWord : Fin n → ℕ,
      ‖cmp102Eq80PhysicalLayerWordDomainFTCContribution
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord D D₃ V₀ P T Δπ J A Y.blocks‖ ≤
        prefactor * productMajorant layerWord := by
    intro layerWord
    simpa [prefactor, productMajorant] using
      norm_cmp102Eq80PhysicalLayerWordDomainFTCContribution_le_sourceMetricProduct
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmallContour layerWord
        D D₃ V₀ P T Δπ J A Y hC0 hC
        hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
        hsplit hcardDecay hmetricDecay hsmall
  have hnorm :
      Summable fun layerWord : Fin n → ℕ =>
        ‖cmp102Eq80PhysicalLayerWordDomainFTCContribution
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord D D₃ V₀ P T Δπ J A Y.blocks‖ :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have hscalar :
      Summable fun layerWord : Fin n → ℕ =>
        cmp102Eq80PhysicalLayerWordDomainFTCContribution
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord D D₃ V₀ P T Δπ J A Y.blocks :=
    Summable.of_norm hnorm
  refine ⟨hscalar, ?_⟩
  unfold cmp102Eq80PhysicalNeumannDomainFTCContribution
  calc
    ‖∑' layerWord : Fin n → ℕ,
        cmp102Eq80PhysicalLayerWordDomainFTCContribution
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord D D₃ V₀ P T Δπ J A Y.blocks‖ ≤
      ∑' layerWord : Fin n → ℕ,
        ‖cmp102Eq80PhysicalLayerWordDomainFTCContribution
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord D D₃ V₀ P T Δπ J A Y.blocks‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' layerWord : Fin n → ℕ,
        prefactor * productMajorant layerWord :=
      Summable.tsum_le_tsum hterm hnorm hmajor
    _ = prefactor *
        (cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
          (Q := Q) (Δ := Δ) summationRatio) ^ n := by
      rw [tsum_mul_left]
      dsimp [productMajorant,
        cmp102Eq80PhysicalOuterNeumannSourceMetricRatio]
      rw [tsum_cmp102Eq80PhysicalLayerWordSourceMetricProduct
        (Q := Q) hsummation0 hsmall]
    _ = _ := rfl

end

end YangMills.RG

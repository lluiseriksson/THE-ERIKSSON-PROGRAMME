/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailSourceMetricChoiceSum
import YangMills.L1_GibbsMeasure.ExpActivityExpansion

/-!
# Source decay after the complete coarse layer-word sum

The remaining index below one outer Neumann layer is
`layerWord : Fin n → ℕ`.  After the literal fine-walk choice count, every
coordinate contributes the geometric factor

`|charts| * summationRatio *
  (branching * summationRatio) ^ layerWord i`.

This file performs that genuine multidimensional `tsum`.  Both source
weights remain outside it, and the only convergence condition is the
already visible physical ratio `branching * summationRatio < 1`.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator BigOperators

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- The factor independent of the coarse layer-word coordinates. -/
noncomputable def
    cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (κcard κmetric summationRatio : ℝ)
    (Y : CMP116LocalizationDomain M (2 * Q))
    (Δ : ℕ) : ℝ :=
  ((cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
    cmp102Eq80PhysicalFineHeadTailEndpointMajorant
      (M := M) baseCoarseCovariance *
    Real.exp (κcard * 10000) *
    Real.exp (-(κcard * (Y.blocks.card : ℝ))) *
    Real.exp (κmetric * 10000) *
    Real.exp (-(κmetric *
      (cmp116CubeEdgeTreeMetric Y : ℝ))) *
    summationRatio *
    (1 -
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio)⁻¹

/-- The choice-summed coefficient is a product-geometric majorant in the
coarse layer-word coordinates. -/
theorem
    norm_cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient_le_sourceMetricProduct
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
    (layerWord : Fin n → ℕ)
    (Y : CMP116LocalizationDomain M (2 * Q))
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
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
    ‖cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord Y.blocks‖ ≤
      cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
          (M := M) baseCoarseCovariance
          κcard κmetric summationRatio Y Δ *
        ∏ i : Fin n,
          (((cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
            summationRatio *
            ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
              summationRatio) ^ layerWord i)) := by
  have h :=
    norm_cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient_le_sourceMetricDecay
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap layerWord Y
      hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
      hsplit hcardDecay hmetricDecay hsmall
  calc
    ‖cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord Y.blocks‖ ≤ _ := h
    _ =
      cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
          (M := M) baseCoarseCovariance
          κcard κmetric summationRatio Y Δ *
        ∏ i : Fin n,
          (((cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
            summationRatio *
            ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
              summationRatio) ^ layerWord i)) := by
      unfold
        cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
        cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
      push_cast
      have hsum :
          1 + ∑ i : Fin n, (layerWord i + 1) =
            (1 + n) + ∑ i : Fin n, layerWord i := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_fin, smul_eq_mul]
        omega
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_fin, hsum, pow_add, pow_add]
      simp only [mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
      rw [Finset.prod_const, Finset.prod_const]
      simp only [Finset.card_fin]
      ring

/-- Cancellation-free choice sum in the same product-geometric normal
form.  This is the exact input required by the scalar FTC track. -/
theorem
    sum_norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient_le_sourceMetricProduct
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
    (layerWord : Fin n → ℕ)
    (Y : CMP116LocalizationDomain M (2 * Q))
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
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
    (∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
      ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y.blocks‖) ≤
      cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
          (M := M) baseCoarseCovariance
          κcard κmetric summationRatio Y Δ *
        ∏ i : Fin n,
          (((cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
            summationRatio *
            ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
              summationRatio) ^ layerWord i)) := by
  have h :=
    sum_norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient_le_sourceMetricDecay
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap layerWord Y
      hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
      hsplit hcardDecay hmetricDecay hsmall
  calc
    (∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
      ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y.blocks‖) ≤ _ := h
    _ =
      cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
          (M := M) baseCoarseCovariance
          κcard κmetric summationRatio Y Δ *
        ∏ i : Fin n,
          (((cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
            summationRatio *
            ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
              summationRatio) ^ layerWord i)) := by
      unfold
        cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
        cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
      push_cast
      have hsum :
          1 + ∑ i : Fin n, (layerWord i + 1) =
            (1 + n) + ∑ i : Fin n, layerWord i := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_fin, smul_eq_mul]
        omega
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_fin, hsum, pow_add, pow_add]
      simp only [mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
      rw [Finset.prod_const, Finset.prod_const]
      simp only [Finset.card_fin]
      ring

/-- The product-geometric majorant is summable over every finite coarse
layer-word index set. -/
theorem summable_cmp102Eq80PhysicalLayerWordSourceMetricProduct
    {Q Δ n : ℕ} [NeZero Q]
    {summationRatio : ℝ}
    (hsummation0 : 0 ≤ summationRatio)
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1) :
    Summable fun layerWord : Fin n → ℕ =>
      ∏ i : Fin n,
        (((cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
          summationRatio *
          ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio) ^ layerWord i)) := by
  let charts : ℝ :=
    ((cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ)
  let q : ℝ :=
    ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
      summationRatio
  have hcharts0 : 0 ≤ charts := by
    dsimp [charts]
    positivity
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hsmall
  let a : Fin n → ℕ → ℂ :=
    fun _ k => (charts * summationRatio * q ^ k : ℝ)
  have ha : ∀ i, Summable fun k => ‖a i k‖ := by
    intro i
    have hgeom : Summable fun k : ℕ => q ^ k :=
      summable_geometric_of_norm_lt_one hqnorm
    have hcoeff0 : 0 ≤ charts * summationRatio := by
      dsimp [charts]
      positivity
    refine (hgeom.mul_left (charts * summationRatio)).congr ?_
    intro k
    simp [a, Complex.norm_real, abs_of_nonneg,
      hcharts0, hsummation0, hq0]
  have hprod := YangMills.summable_norm_pi_prod a ha
  refine hprod.congr ?_
  intro layerWord
  simp [a, charts, q, Complex.norm_real, abs_of_nonneg,
    hsummation0]

/-- The complete coarse layer-word majorant has the expected finite
product of scalar geometric sums.  In particular, no cardinality of the
ambient volume enters the result. -/
theorem tsum_cmp102Eq80PhysicalLayerWordSourceMetricProduct
    {Q Δ n : ℕ} [NeZero Q]
    {summationRatio : ℝ}
    (hsummation0 : 0 ≤ summationRatio)
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1) :
    (∑' layerWord : Fin n → ℕ,
      ∏ i : Fin n,
        (((cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
          summationRatio *
          ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio) ^ layerWord i))) =
      ((((cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
        summationRatio *
        (1 -
          ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio)⁻¹) ^ n) := by
  let charts : ℝ :=
    ((cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ)
  let q : ℝ :=
    ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
      summationRatio
  have hcharts0 : 0 ≤ charts := by
    dsimp [charts]
    positivity
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hgeom : Summable fun k : ℕ => q ^ k := by
    have hqnorm : ‖q‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hq0]
      exact hsmall
    exact summable_geometric_of_norm_lt_one hqnorm
  rw [← YangMills.tsum_pi_prod_nonneg
    (fun (_ : Fin n) k => charts * summationRatio * q ^ k)
    (fun _ _ => by positivity)
    (fun _ => hgeom.mul_left (charts * summationRatio))]
  have hscalar :
      (∑' k : ℕ, charts * summationRatio * q ^ k) =
        charts * summationRatio * (1 - q)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hsmall]
  rw [Finset.prod_congr rfl (fun _ _ => hscalar),
    Finset.prod_const, Finset.card_fin]

/-- Complete fixed-domain matrix coefficient after summing all coarse
layer words of one outer Neumann length. -/
noncomputable def
    cmp102Eq80PhysicalNeumannDomainMatrixCoefficient
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
    (Y : Finset (FinBox 4 (2 * Q))) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc) ℂ :=
  ∑' layerWord : Fin n → ℕ,
    cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient
      (R := R) anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord Y

/-- The matrix-valued layer-word series is genuinely summable and retains
both source decays. -/
theorem
    summable_cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient_of_sourceMetricSplit
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
    (Y : CMP116LocalizationDomain M (2 * Q))
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
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
    Summable fun layerWord : Fin n → ℕ =>
      cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord Y.blocks := by
  let prefactor :=
    cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
      (M := M) baseCoarseCovariance
      κcard κmetric summationRatio Y Δ
  have hmajor :
      Summable fun layerWord : Fin n → ℕ =>
        prefactor *
          ∏ i : Fin n,
            (((cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
              summationRatio *
              ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
                summationRatio) ^ layerWord i)) :=
    (summable_cmp102Eq80PhysicalLayerWordSourceMetricProduct
      (Q := Q) hsummation0 hsmall).mul_left prefactor
  apply Summable.of_norm_bounded hmajor
  intro layerWord
  exact
    norm_cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient_le_sourceMetricProduct
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap layerWord Y
      hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
      hsplit hcardDecay hmetricDecay hsmall

/-- The complete fixed-domain coefficient has an explicit closed bound
after every coarse layer-word has been summed.  The two physical source
weights survive unchanged, while the remaining cost is precisely the
finite product of scalar geometric sums. -/
theorem
    norm_cmp102Eq80PhysicalNeumannDomainMatrixCoefficient_le_sourceMetricDecay
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
    (Y : CMP116LocalizationDomain M (2 * Q))
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
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
    ‖cmp102Eq80PhysicalNeumannDomainMatrixCoefficient
        (R := R) (n := n) anchor K hc hmass hK
        baseCoarseCovariance sigma Y.blocks‖ ≤
      cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
          (M := M) baseCoarseCovariance
          κcard κmetric summationRatio Y Δ *
        ((((cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
          summationRatio *
          (1 -
            ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
              summationRatio)⁻¹) ^ n) := by
  let prefactor :=
    cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
      (M := M) baseCoarseCovariance
      κcard κmetric summationRatio Y Δ
  let majorant := fun layerWord : Fin n → ℕ =>
    prefactor *
      ∏ i : Fin n,
        (((cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
          summationRatio *
          ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio) ^ layerWord i))
  have hmajor : Summable majorant := by
    dsimp [majorant]
    exact
      (summable_cmp102Eq80PhysicalLayerWordSourceMetricProduct
        (Q := Q) hsummation0 hsmall).mul_left prefactor
  have hterm : ∀ layerWord : Fin n → ℕ,
      ‖cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord Y.blocks‖ ≤ majorant layerWord := by
    intro layerWord
    exact
      norm_cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient_le_sourceMetricProduct
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap layerWord Y
        hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
        hsplit hcardDecay hmetricDecay hsmall
  have hnorm :
      Summable fun layerWord : Fin n → ℕ =>
        ‖cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord Y.blocks‖ :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  unfold cmp102Eq80PhysicalNeumannDomainMatrixCoefficient
  calc
    ‖∑' layerWord : Fin n → ℕ,
        cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord Y.blocks‖ ≤
        ∑' layerWord : Fin n → ℕ,
          ‖cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient
            (R := R) anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord Y.blocks‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' layerWord : Fin n → ℕ, majorant layerWord := by
      exact Summable.tsum_le_tsum hterm hnorm hmajor
    _ =
        prefactor *
          ((((cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
            summationRatio *
            (1 -
              ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
                summationRatio)⁻¹) ^ n) := by
      dsimp [majorant]
      rw [tsum_mul_left,
        tsum_cmp102Eq80PhysicalLayerWordSourceMetricProduct
          (Q := Q) hsummation0 hsmall]
    _ = _ := rfl

/-- The scalar ratio left after the complete dependent coarse
layer-word sum. -/
noncomputable def cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
    {Q Δ : ℕ} [NeZero Q] (summationRatio : ℝ) : ℝ :=
  ((cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
    summationRatio *
    (1 -
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio)⁻¹

/-- Complete source-domain matrix coefficient after the outer Neumann
length has also been summed. -/
noncomputable def cmp102Eq80PhysicalSourceDomainMatrixCoefficient
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (Y : Finset (FinBox 4 (2 * Q))) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc) ℂ :=
  ∑' n : ℕ,
    cmp102Eq80PhysicalNeumannDomainMatrixCoefficient
      (R := R) (n := n) anchor K hc hmass hK
      baseCoarseCovariance sigma Y

/-- The entire dependent expansion below a fixed source domain is
absolutely summable.  Its closed bound retains both `|Y|` and
`d_k(Y)` decay and contains no ambient-volume cardinality. -/
theorem
    summable_and_norm_cmp102Eq80PhysicalSourceDomainMatrixCoefficient_le_sourceMetricDecay
    {M Q Nc R Δ : ℕ}
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
    (Y : CMP116LocalizationDomain M (2 * Q))
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
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
        summationRatio < 1)
    (houterSmall :
      cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
        (Q := Q) (Δ := Δ) summationRatio < 1) :
    Summable (fun n : ℕ =>
      cmp102Eq80PhysicalNeumannDomainMatrixCoefficient
        (R := R) (n := n) anchor K hc hmass hK
        baseCoarseCovariance sigma Y.blocks) ∧
    ‖cmp102Eq80PhysicalSourceDomainMatrixCoefficient
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma Y.blocks‖ ≤
      cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
          (M := M) baseCoarseCovariance
          κcard κmetric summationRatio Y Δ *
        (1 -
          cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
            (Q := Q) (Δ := Δ) summationRatio)⁻¹ := by
  let prefactor :=
    cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor
      (M := M) baseCoarseCovariance
      κcard κmetric summationRatio Y Δ
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
  have hprefactor0 : 0 ≤ prefactor := by
    dsimp [prefactor,
      cmp102Eq80PhysicalLayerWordSourceMetricDecayPrefactor,
      cmp102Eq80PhysicalFineHeadTailEndpointMajorant]
    positivity
  have hmajor :
      Summable fun n : ℕ => prefactor * q ^ n :=
    (summable_geometric_of_norm_lt_one hqnorm).mul_left prefactor
  have hterm : ∀ n : ℕ,
      ‖cmp102Eq80PhysicalNeumannDomainMatrixCoefficient
          (R := R) (n := n) anchor K hc hmass hK
          baseCoarseCovariance sigma Y.blocks‖ ≤
        prefactor * q ^ n := by
    intro n
    simpa [q, cmp102Eq80PhysicalOuterNeumannSourceMetricRatio] using
      norm_cmp102Eq80PhysicalNeumannDomainMatrixCoefficient_le_sourceMetricDecay
        (n := n) anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap Y
        hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
        hsplit hcardDecay hmetricDecay hsmall
  have hnorm :
      Summable fun n : ℕ =>
        ‖cmp102Eq80PhysicalNeumannDomainMatrixCoefficient
          (R := R) (n := n) anchor K hc hmass hK
          baseCoarseCovariance sigma Y.blocks‖ :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have hmatrix :
      Summable fun n : ℕ =>
        cmp102Eq80PhysicalNeumannDomainMatrixCoefficient
          (R := R) (n := n) anchor K hc hmass hK
          baseCoarseCovariance sigma Y.blocks :=
    Summable.of_norm hnorm
  refine ⟨hmatrix, ?_⟩
  unfold cmp102Eq80PhysicalSourceDomainMatrixCoefficient
  calc
    ‖∑' n : ℕ,
        cmp102Eq80PhysicalNeumannDomainMatrixCoefficient
          (R := R) (n := n) anchor K hc hmass hK
          baseCoarseCovariance sigma Y.blocks‖ ≤
        ∑' n : ℕ,
          ‖cmp102Eq80PhysicalNeumannDomainMatrixCoefficient
            (R := R) (n := n) anchor K hc hmass hK
            baseCoarseCovariance sigma Y.blocks‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, prefactor * q ^ n :=
      Summable.tsum_le_tsum hterm hnorm hmajor
    _ = prefactor * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 houterSmall]
    _ = _ := rfl

end

end YangMills.RG

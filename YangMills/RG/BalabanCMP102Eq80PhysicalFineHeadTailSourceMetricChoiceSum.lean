/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailSourceMetricEntry

/-!
# Source decay after the literal dependent fine-walk choice sum

For one fixed coarse layer word, the equation-(80) FTC expansion sums over
one fine walk at every coarse position.  The number of such dependent
choices is bounded by the product of the already proved physical
chart/branching bounds.  This file performs that finite sum while retaining
the source-cardinality and source-tree-metric decay.

No ambient set of all maps or all charts is counted.
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

/-- The literal dependent choice count is the product of the physical
fine-walk counts and hence has an explicit volume-independent bound. -/
theorem card_cmp99SourcePi4CoarseFineWalkChoice_le
    {M Q R Δ n : ℕ}
    [NeZero M] [NeZero Q]
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (layerWord : Fin n → ℕ) :
    Fintype.card
        (CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) ≤
      ∏ i : Fin n,
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)).card *
          cmp116SourcePi4TerminalBranching Δ ^ layerWord i := by
  rw [Fintype.card_pi]
  apply Finset.prod_le_prod'
  intro i _hi
  exact
    card_cmp99SourcePi4FineWalkIndex_le_chart_mul_branch_pow
      (headLength := layerWord i) hrange hΔ hΔ1

/-- Complete fixed-domain matrix coefficient after the literal finite sum
over all dependent fine-walk choices below one coarse layer word. -/
noncomputable def
    cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient
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
    (layerWord : Fin n → ℕ)
    (Y : Finset (FinBox 4 (2 * Q))) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc) ℂ :=
  ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
    cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice Y

/-- The dependent choice sum retains both source decays.  Its only
multiplicity is the explicit product of physical chart/branching counts. -/
theorem
    norm_cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient_le_sourceMetricDecay
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
      ((∏ i : Fin n,
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)).card *
          cmp116SourcePi4TerminalBranching Δ ^ layerWord i : ℕ) : ℝ) *
        (cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
            (M := M) baseCoarseCovariance
            κcard κmetric summationRatio layerWord Y *
          (1 -
            ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
              summationRatio)⁻¹) := by
  classical
  let choiceBound : ℕ :=
    ∏ i : Fin n,
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)).card *
        cmp116SourcePi4TerminalBranching Δ ^ layerWord i
  let bound : ℝ :=
    cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
        (M := M) baseCoarseCovariance
        κcard κmetric summationRatio layerWord Y *
      (1 -
        ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
          summationRatio)⁻¹
  have hbound0 : 0 ≤ bound := by
    have hprefactor :
        0 ≤ cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
          (M := M) baseCoarseCovariance
          κcard κmetric summationRatio layerWord Y := by
      unfold
        cmp102Eq80PhysicalFineHeadTailSourceMetricDecayPrefactor
        cmp102Eq80PhysicalFineHeadTailEndpointMajorant
      positivity
    have hinv :
        0 ≤ (1 -
          ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio)⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr hsmall.le)
    exact mul_nonneg hprefactor hinv
  have hchoice :
      Fintype.card
          (CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) ≤
        choiceBound := by
    simpa [choiceBound] using
      card_cmp99SourcePi4CoarseFineWalkChoice_le
        hrange hΔ hΔ1 layerWord
  have hchoiceReal :
      (Fintype.card
          (CMP99SourcePi4CoarseFineWalkChoice
            M Q R layerWord) : ℝ) ≤ (choiceBound : ℝ) := by
    exact_mod_cast hchoice
  unfold cmp102Eq80PhysicalLayerWordDomainMatrixCoefficient
  calc
    ‖∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice Y.blocks‖ ≤
      ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice Y.blocks‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _choice :
        CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        bound := by
      apply Finset.sum_le_sum
      intro choice _hchoice
      exact
        norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient_le_sourceMetricDecay
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          sigma hRweak hcap layerWord choice Y
          hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
          hsplit hcardDecay hmetricDecay hsmall
    _ =
      (Fintype.card
          (CMP99SourcePi4CoarseFineWalkChoice
            M Q R layerWord) : ℝ) * bound := by simp
    _ ≤ (choiceBound : ℝ) * bound :=
      mul_le_mul_of_nonneg_right hchoiceReal hbound0
    _ = _ := rfl

end

end YangMills.RG

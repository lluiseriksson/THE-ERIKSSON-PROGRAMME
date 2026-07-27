/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailDomainDecay
import YangMills.RG.BalabanCMP116Eq230TreeMetric

/-!
# Source-tree-metric decay of literal CMP102 equation-(80) words

The canonical carrier-anchored head/tail domain is nonempty and
face-connected.  It therefore defines the literal CMP116 localization
domain on which the already constructed cube-edge tree metric realizes
`d_k(Y)`.

The physical common walk ratio is split into three visible factors:

* a factor paying `exp (-κcard * |Y|)`;
* a factor paying `exp (-κmetric * d_k(Y))`;
* a residual factor retained for the geometric walk sums.

Both decay factors are produced from the same exact literal walk budget.
No domain metric or domain-decay estimate is supplied by the caller.
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

/-- The canonical literal head/tail domain as a source-faithful nonempty
face-connected CMP116 localization domain. -/
noncomputable def cmp102Eq80SourcePi4FineHeadTailLocalizationSourceDomain
    {M Q R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    CMP116LocalizationDomain M (2 * Q) where
  blocks :=
    cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
      anchor head choice
  nonempty := by
    obtain ⟨x, hx⟩ := cmp102Eq80SourcePi4AnchorCarrier_nonempty anchor
    exact ⟨x,
      cmp102Eq80SourcePi4AnchorCarrier_subset_fineHeadTailLocalizationDomain
        anchor head choice hx⟩
  connected :=
    walkConnected_cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
      anchor head choice

@[simp]
theorem
    cmp102Eq80SourcePi4FineHeadTailLocalizationSourceDomain_blocks
    {M Q R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    (cmp102Eq80SourcePi4FineHeadTailLocalizationSourceDomain
      anchor head choice).blocks =
      cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
        anchor head choice := rfl

/-- Literal `d_k(Y)` for a canonical equation-(80) head/tail domain. -/
noncomputable def cmp102Eq80SourcePi4FineHeadTailTreeMetric
    {M Q R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) : ℕ :=
  cmp116CubeEdgeTreeMetric
    (cmp102Eq80SourcePi4FineHeadTailLocalizationSourceDomain
      anchor head choice)

/-- The literal source tree metric is no larger than the cardinality of
the canonical block domain. -/
theorem cmp102Eq80SourcePi4FineHeadTailTreeMetric_le_domainCard
    {M Q R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    cmp102Eq80SourcePi4FineHeadTailTreeMetric anchor head choice ≤
      (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
        anchor head choice).card := by
  have h :=
    cmp116CubeEdgeTreeMetric_le_blockCard_sub_one
      (cmp102Eq80SourcePi4FineHeadTailLocalizationSourceDomain
        anchor head choice)
  change
    cmp102Eq80SourcePi4FineHeadTailTreeMetric anchor head choice ≤
      (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
        anchor head choice).card
  exact h.trans (Nat.sub_le _ _)

/-- A generic quantity below the canonical literal walk budget receives
the corresponding exponential decay, with one fixed anchor cost. -/
theorem cmp102Eq80_walkBudgetDecay_of_measure_le
    {budget measure : ℕ}
    {ratio κ : ℝ}
    (hratio0 : 0 ≤ ratio)
    (hκ : 0 ≤ κ)
    (hmeasure : measure ≤ 10000 * (1 + budget))
    (hdecay : ratio ≤ Real.exp (-(κ * 10000))) :
    ratio ^ budget ≤
      Real.exp (κ * 10000) *
        Real.exp (-(κ * (measure : ℝ))) := by
  have hmeasureReal :
      (measure : ℝ) ≤ 10000 * (1 + (budget : ℝ)) := by
    exact_mod_cast hmeasure
  have hexponent :
      -(κ * 10000) * (budget : ℝ) ≤
        κ * 10000 - κ * (measure : ℝ) := by
    nlinarith
  calc
    ratio ^ budget ≤
        (Real.exp (-(κ * 10000))) ^ budget :=
      pow_le_pow_left₀ hratio0 hdecay budget
    _ = Real.exp (-(κ * 10000) * (budget : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (κ * 10000 - κ * (measure : ℝ)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (κ * 10000) *
        Real.exp (-(κ * (measure : ℝ))) := by
      rw [← Real.exp_add]
      congr 1

/-- Three-way split of the common physical ratio into cardinality decay,
source-tree-metric decay and a residual summation ratio. -/
theorem cmp102Eq80_splitWalkBudgetDecay_of_domainCard_and_treeMetric
    {M Q R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    (anchor : FinBox 4 Q)
    (hrange : R + 1 ≤ 4 * M)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    {physicalRatio cardRatio metricRatio summationRatio
      κcard κmetric : ℝ}
    (hphysical0 : 0 ≤ physicalRatio)
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 ≤ κcard)
    (hκmetric : 0 ≤ κmetric)
    (hsplit :
      physicalRatio ≤ cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000))) :
    physicalRatio ^
        cmp102Eq80PhysicalFineHeadTailWalkBudget headLength layerWord ≤
      Real.exp (κcard * 10000) *
        Real.exp (-(κcard *
          (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
            anchor head choice).card)) *
        Real.exp (κmetric * 10000) *
        Real.exp (-(κmetric *
          (cmp102Eq80SourcePi4FineHeadTailTreeMetric
            anchor head choice : ℝ))) *
        summationRatio ^
          cmp102Eq80PhysicalFineHeadTailWalkBudget
            headLength layerWord := by
  let budget :=
    cmp102Eq80PhysicalFineHeadTailWalkBudget headLength layerWord
  let Y :=
    cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
      anchor head choice
  let metric :=
    cmp102Eq80SourcePi4FineHeadTailTreeMetric anchor head choice
  have hcardBudget : Y.card ≤ 10000 * (1 + budget) := by
    simpa [Y, budget, cmp102Eq80PhysicalFineHeadTailWalkBudget,
      Nat.add_assoc] using
      (card_cmp102Eq80SourcePi4FineHeadTailLocalizationDomain_le
        anchor hrange head choice)
  have hmetricBudget : metric ≤ 10000 * (1 + budget) := by
    exact
      (cmp102Eq80SourcePi4FineHeadTailTreeMetric_le_domainCard
        anchor head choice).trans hcardBudget
  have hcardPow :
      cardRatio ^ budget ≤
        Real.exp (κcard * 10000) *
          Real.exp (-(κcard * (Y.card : ℝ))) :=
    cmp102Eq80_walkBudgetDecay_of_measure_le
      hcardRatio0 hκcard hcardBudget hcardDecay
  have hmetricPow :
      metricRatio ^ budget ≤
        Real.exp (κmetric * 10000) *
          Real.exp (-(κmetric * (metric : ℝ))) :=
    cmp102Eq80_walkBudgetDecay_of_measure_le
      hmetricRatio0 hκmetric hmetricBudget hmetricDecay
  have hproduct0 :
      0 ≤ cardRatio * (metricRatio * summationRatio) :=
    mul_nonneg hcardRatio0
      (mul_nonneg hmetricRatio0 hsummation0)
  calc
    physicalRatio ^ budget ≤
        (cardRatio * (metricRatio * summationRatio)) ^ budget :=
      pow_le_pow_left₀ hphysical0 hsplit budget
    _ =
        cardRatio ^ budget *
          metricRatio ^ budget *
          summationRatio ^ budget := by
      rw [mul_pow, mul_pow]
      ring
    _ ≤
        (Real.exp (κcard * 10000) *
          Real.exp (-(κcard * (Y.card : ℝ)))) *
        (Real.exp (κmetric * 10000) *
          Real.exp (-(κmetric * (metric : ℝ)))) *
        summationRatio ^ budget := by
      gcongr
    _ =
      Real.exp (κcard * 10000) *
        Real.exp (-(κcard * (Y.card : ℝ))) *
        Real.exp (κmetric * 10000) *
        Real.exp (-(κmetric * (metric : ℝ))) *
        summationRatio ^ budget := by ring

/-- Literal word estimate with both source cardinality and source-tree
metric decay, before any fiber or Neumann summation. -/
theorem
    norm_cmp99SourcePi4ComplexFineHeadTailWordTerm_le_sourceMetricDecay
    {M Q Nc R headLength n : ℕ}
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
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
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
      metricRatio ≤ Real.exp (-(κmetric * 10000))) :
    ‖cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma head layerWord choice‖ ≤
      cmp102Eq80PhysicalFineHeadTailEndpointMajorant
          (M := M) baseCoarseCovariance *
        Real.exp (κcard * 10000) *
        Real.exp (-(κcard *
          (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
            anchor head choice).card)) *
        Real.exp (κmetric * 10000) *
        Real.exp (-(κmetric *
          (cmp102Eq80SourcePi4FineHeadTailTreeMetric
            anchor head choice : ℝ))) *
        summationRatio ^
          cmp102Eq80PhysicalFineHeadTailWalkBudget
            headLength layerWord := by
  let physicalRatio :=
    cmp102Eq80PhysicalFineHeadTailWalkRatio
      (M := M) baseCoarseCovariance Ahead rho rate Rweak
  let endpoint :=
    cmp102Eq80PhysicalFineHeadTailEndpointMajorant
      (M := M) baseCoarseCovariance
  have hphysical0 : 0 ≤ physicalRatio := by
    dsimp [physicalRatio, cmp102Eq80PhysicalFineHeadTailWalkRatio]
    have hRweak0 : 0 ≤ Rweak := le_trans zero_le_one hRweak
    have hbase0 :
        0 ≤ cmp102Eq80PhysicalFineWalkBase
          (Nc := Nc) Ahead rate Rweak := by
      unfold cmp102Eq80PhysicalFineWalkBase
      exact mul_nonneg (pow_nonneg hRweak0 _)
        (mul_nonneg hAhead
          (mul_nonneg (Nat.cast_nonneg _)
            (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)))
    exact hbase0.trans (le_max_left _ _)
  have hword :=
    norm_cmp99SourcePi4ComplexFineHeadTailWordTerm_le_commonRatio_pow
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange sigma hRweak hcap
      head layerWord choice
  have hsplitDecay :=
    cmp102Eq80_splitWalkBudgetDecay_of_domainCard_and_treeMetric
      anchor hrange head choice
      hphysical0 hcardRatio0 hmetricRatio0 hsummation0
      hκcard hκmetric hsplit hcardDecay hmetricDecay
  have hendpoint0 : 0 ≤ endpoint := by
    dsimp [endpoint,
      cmp102Eq80PhysicalFineHeadTailEndpointMajorant]
    positivity
  calc
    ‖cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma head layerWord choice‖ ≤
      endpoint *
        physicalRatio ^
          cmp102Eq80PhysicalFineHeadTailWalkBudget
            headLength layerWord := by
      simpa [endpoint, physicalRatio,
        cmp102Eq80PhysicalFineHeadTailWalkBudget] using hword
    _ ≤ endpoint *
        (Real.exp (κcard * 10000) *
          Real.exp (-(κcard *
            (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
              anchor head choice).card)) *
          Real.exp (κmetric * 10000) *
          Real.exp (-(κmetric *
            (cmp102Eq80SourcePi4FineHeadTailTreeMetric
              anchor head choice : ℝ))) *
          summationRatio ^
            cmp102Eq80PhysicalFineHeadTailWalkBudget
              headLength layerWord) :=
      mul_le_mul_of_nonneg_left hsplitDecay hendpoint0
    _ = _ := by ring

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailFixedRightBound

/-!
# Domain-cardinality decay of literal CMP102 equation-(80) words

The common physical walk ratio is split into two explicit nonnegative
factors.  The first pays one `10000`-block decay unit for every literal
head/tail walk unit and therefore yields `exp (-κ * |Y|)`.  The second is
retained as the geometric ratio needed to sum walk lengths.  This avoids
spending the same smallness twice.

Only the canonical literal equation-(80) domain is treated here.  The
result is not the full source estimate (1.43): the remaining domain metric
factor and the other fluctuation-action sectors remain separate.
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

/-- The literal head/tail walk budget, excluding the distinguished
`Pi^4` anchor whose fixed cardinality is paid by `exp (κ * 10000)`. -/
def cmp102Eq80PhysicalFineHeadTailWalkBudget
    {n : ℕ} (headLength : ℕ) (layerWord : Fin n → ℕ) : ℕ :=
  (headLength + 1) + ∑ i : Fin n, (layerWord i + 1)

/-- Split a source-produced walk ratio into a domain-decay ratio and a
residual summation ratio.  The fixed `Pi^4` anchor costs one explicit
factor `exp (κ * 10000)`. -/
theorem cmp102Eq80_splitWalkBudgetDecay_of_domainCard
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (hrange : R + 1 ≤ 4 * M)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    {physicalRatio domainRatio summationRatio κ : ℝ}
    (hphysical0 : 0 ≤ physicalRatio)
    (hdomain0 : 0 ≤ domainRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκ : 0 ≤ κ)
    (hsplit : physicalRatio ≤ domainRatio * summationRatio)
    (hdecay : domainRatio ≤ Real.exp (-(κ * 10000))) :
    physicalRatio ^
        cmp102Eq80PhysicalFineHeadTailWalkBudget headLength layerWord ≤
      Real.exp (κ * 10000) *
        Real.exp (-(κ *
          (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
            anchor head choice).card)) *
        summationRatio ^
          cmp102Eq80PhysicalFineHeadTailWalkBudget
            headLength layerWord := by
  let budget :=
    cmp102Eq80PhysicalFineHeadTailWalkBudget headLength layerWord
  let Y :=
    cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
      anchor head choice
  have hproduct0 : 0 ≤ domainRatio * summationRatio :=
    mul_nonneg hdomain0 hsummation0
  have hsplitPow :
      physicalRatio ^ budget ≤
        (domainRatio * summationRatio) ^ budget :=
    pow_le_pow_left₀ hphysical0 hsplit budget
  have hdomainPow :
      domainRatio ^ budget ≤
        Real.exp (κ * 10000) *
          Real.exp (-(κ * (Y.card : ℝ))) := by
    have hcardNat : Y.card ≤ 10000 * (1 + budget) := by
      simpa [Y, budget, cmp102Eq80PhysicalFineHeadTailWalkBudget,
        Nat.add_assoc] using
        (card_cmp102Eq80SourcePi4FineHeadTailLocalizationDomain_le
          anchor hrange head choice)
    have hcard : (Y.card : ℝ) ≤ 10000 * (1 + (budget : ℝ)) := by
      exact_mod_cast hcardNat
    have hexponent :
        -(κ * 10000) * (budget : ℝ) ≤
          κ * 10000 - κ * (Y.card : ℝ) := by
      nlinarith
    calc
      domainRatio ^ budget ≤
          (Real.exp (-(κ * 10000))) ^ budget :=
        pow_le_pow_left₀ hdomain0 hdecay budget
      _ = Real.exp (-(κ * 10000) * (budget : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (κ * 10000 - κ * (Y.card : ℝ)) :=
        Real.exp_le_exp.mpr hexponent
      _ = Real.exp (κ * 10000) *
          Real.exp (-(κ * (Y.card : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
  calc
    physicalRatio ^ budget ≤
        (domainRatio * summationRatio) ^ budget :=
      hsplitPow
    _ = domainRatio ^ budget * summationRatio ^ budget := by
      rw [mul_pow]
    _ ≤
        (Real.exp (κ * 10000) *
          Real.exp (-(κ * (Y.card : ℝ)))) *
          summationRatio ^ budget :=
      mul_le_mul_of_nonneg_right hdomainPow
        (pow_nonneg hsummation0 _)
    _ = Real.exp (κ * 10000) *
        Real.exp (-(κ * (Y.card : ℝ))) *
        summationRatio ^ budget := by ring

/-- A literal physical fine-head/tail word has explicit exponential decay
in the cardinality of its own canonical domain, while retaining the
residual walk ratio required by later sums. -/
theorem
    norm_cmp99SourcePi4ComplexFineHeadTailWordTerm_le_domainCardDecay
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
    {domainRatio summationRatio κ : ℝ}
    (hdomain0 : 0 ≤ domainRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκ : 0 ≤ κ)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        domainRatio * summationRatio)
    (hdecay : domainRatio ≤ Real.exp (-(κ * 10000))) :
    ‖cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma head layerWord choice‖ ≤
      cmp102Eq80PhysicalFineHeadTailEndpointMajorant
          (M := M) baseCoarseCovariance *
        Real.exp (κ * 10000) *
        Real.exp (-(κ *
          (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
            anchor head choice).card)) *
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
    cmp102Eq80_splitWalkBudgetDecay_of_domainCard
      anchor hrange head choice hphysical0 hdomain0 hsummation0 hκ
      hsplit hdecay
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
        (Real.exp (κ * 10000) *
          Real.exp (-(κ *
            (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
              anchor head choice).card)) *
          summationRatio ^
            cmp102Eq80PhysicalFineHeadTailWalkBudget
              headLength layerWord) :=
      mul_le_mul_of_nonneg_left hsplitDecay hendpoint0
    _ = endpoint *
        Real.exp (κ * 10000) *
        Real.exp (-(κ *
          (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
            anchor head choice).card)) *
        summationRatio ^
          cmp102Eq80PhysicalFineHeadTailWalkBudget
            headLength layerWord := by ring

private theorem sourcePi4UnitDomain_injective_for_domain_decay
    {Q : ℕ} [NeZero Q] :
    Function.Injective
      (fun chart : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) => chart.1.domain) := by
  rintro ⟨⟨leftLabel, leftDomain⟩, hleft⟩
    ⟨⟨rightLabel, rightDomain⟩, hright⟩ hEq
  cases leftLabel
  cases rightLabel
  apply Subtype.ext
  cases hEq
  rfl

/-- The number of literal fine walks of a fixed length is bounded by the
source chart count times the physical simple-domain branching. -/
theorem card_cmp99SourcePi4FineWalkIndex_le_chart_mul_branch_pow
    {M Q R Δ headLength : ℕ}
    [NeZero M] [NeZero Q]
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ) :
    Fintype.card (CMP99SourcePi4FineWalkIndex M Q R headLength) ≤
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)).card *
        cmp116SourcePi4TerminalBranching Δ ^ headLength := by
  rw [Fintype.card_sigma]
  calc
    (∑ head : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        Fintype.card ↥(cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          head headLength)) ≤
      ∑ _head : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        cmp116SourcePi4TerminalBranching Δ ^ headLength := by
      apply Finset.sum_le_sum
      intro head _hhead
      simpa only [Fintype.card_coe] using
        (card_cmp99PhysicalPatchAdmissibleTails_le_pow_simpleDomainBound
          (cmp116CoarseFaceAdj 4 Q)
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R
          625 Δ hΔ hΔ1
          (fun chart => chart.1.domain)
          sourcePi4UnitDomain_injective_for_domain_decay
          (fun left next hfollow =>
            cmp99SourcePi4ChartCanFollow_implies_domainsMeet
              (M := M) (Rrange := R) hrange
              left.1 next.1 hfollow)
          headLength head)
    _ =
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)).card *
        cmp116SourcePi4TerminalBranching Δ ^ headLength := by
      simp

/-- A fixed physical-domain matrix layer inherits the domain decay of
every literal term.  The only multiplicity is the explicit physical chart
count and branching bound. -/
theorem
    norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer_le_domainCardDecay
    {M Q Nc R Δ headLength n : ℕ}
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
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (Y : Finset (FinBox 4 (2 * Q)))
    {domainRatio summationRatio κ : ℝ}
    (hdomain0 : 0 ≤ domainRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκ : 0 ≤ κ)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        domainRatio * summationRatio)
    (hdecay : domainRatio ≤ Real.exp (-(κ * 10000))) :
    ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y‖ ≤
      (((cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)).card *
        cmp116SourcePi4TerminalBranching Δ ^ headLength : ℕ) : ℝ) *
        (cmp102Eq80PhysicalFineHeadTailEndpointMajorant
            (M := M) baseCoarseCovariance *
          Real.exp (κ * 10000) *
          Real.exp (-(κ * (Y.card : ℝ))) *
          summationRatio ^
            cmp102Eq80PhysicalFineHeadTailWalkBudget
              headLength layerWord) := by
  classical
  let source : Finset
      (CMP99SourcePi4FineWalkIndex M Q R headLength) :=
    Finset.univ
  let good := source.filter fun head =>
    cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
      anchor head choice = Y
  let bound : ℝ :=
    cmp102Eq80PhysicalFineHeadTailEndpointMajorant
        (M := M) baseCoarseCovariance *
      Real.exp (κ * 10000) *
      Real.exp (-(κ * (Y.card : ℝ))) *
      summationRatio ^
        cmp102Eq80PhysicalFineHeadTailWalkBudget
          headLength layerWord
  have hbound0 : 0 ≤ bound := by
    dsimp [bound,
      cmp102Eq80PhysicalFineHeadTailEndpointMajorant]
    positivity
  have hterm :
      ∀ head ∈ good,
        ‖cmp99SourcePi4ComplexFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice‖ ≤ bound := by
    intro head hhead
    have hdomain : cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
        anchor head choice = Y :=
      (Finset.mem_filter.mp hhead).2
    have h :=
      norm_cmp99SourcePi4ComplexFineHeadTailWordTerm_le_domainCardDecay
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange sigma hRweak hcap
        head layerWord choice hdomain0 hsummation0 hκ hsplit hdecay
    simpa [bound, hdomain] using h
  have hcard :
      good.card ≤
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)).card *
          cmp116SourcePi4TerminalBranching Δ ^ headLength := by
    calc
      good.card ≤ Fintype.card
          (CMP99SourcePi4FineWalkIndex M Q R headLength) := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)).card *
            cmp116SourcePi4TerminalBranching Δ ^ headLength :=
        card_cmp99SourcePi4FineWalkIndex_le_chart_mul_branch_pow
          hrange hΔ hΔ1
  have hcardReal :
      (good.card : ℝ) ≤
        (((cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)).card *
          cmp116SourcePi4TerminalBranching Δ ^ headLength : ℕ) : ℝ) := by
    exact_mod_cast hcard
  change ‖∑ head ∈ good,
      cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma head layerWord choice‖ ≤ _
  calc
    ‖∑ head ∈ good,
        cmp99SourcePi4ComplexFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice‖ ≤
      ∑ head ∈ good,
        ‖cmp99SourcePi4ComplexFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _head ∈ good, bound :=
      Finset.sum_le_sum fun head hhead => hterm head hhead
    _ = (good.card : ℝ) * bound := by simp
    _ ≤
        (((cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)).card *
          cmp116SourcePi4TerminalBranching Δ ^ headLength : ℕ) : ℝ) *
          bound :=
      mul_le_mul_of_nonneg_right hcardReal hbound0
    _ = _ := rfl

/-- The length-zero prefactor of the fixed-domain geometric majorant after
the domain-decay/summation split. -/
noncomputable def cmp102Eq80PhysicalFineHeadTailDomainDecayPrefactor
    {M Q Nc n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (κ summationRatio : ℝ)
    (layerWord : Fin n → ℕ)
    (Y : Finset (FinBox 4 (2 * Q))) : ℝ :=
  ((cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
    cmp102Eq80PhysicalFineHeadTailEndpointMajorant
      (M := M) baseCoarseCovariance *
    Real.exp (κ * 10000) *
    Real.exp (-(κ * (Y.card : ℝ))) *
    summationRatio ^
      (1 + ∑ i : Fin n, (layerWord i + 1))

/-- The preceding layer bound is literally a geometric sequence in the
fine-head length. -/
theorem
    norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer_le_geometric
    {M Q Nc R Δ headLength n : ℕ}
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
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (Y : Finset (FinBox 4 (2 * Q)))
    {domainRatio summationRatio κ : ℝ}
    (hdomain0 : 0 ≤ domainRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκ : 0 ≤ κ)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        domainRatio * summationRatio)
    (hdecay : domainRatio ≤ Real.exp (-(κ * 10000))) :
    ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y‖ ≤
      cmp102Eq80PhysicalFineHeadTailDomainDecayPrefactor
          (M := M) baseCoarseCovariance κ summationRatio layerWord Y *
        ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
          summationRatio) ^ headLength) := by
  have h :=
    norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer_le_domainCardDecay
      (headLength := headLength)
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap layerWord choice Y
      hdomain0 hsummation0 hκ hsplit hdecay
  calc
    ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y‖ ≤ _ := h
    _ =
      cmp102Eq80PhysicalFineHeadTailDomainDecayPrefactor
          (M := M) baseCoarseCovariance κ summationRatio layerWord Y *
        ((((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
          summationRatio) ^ headLength) := by
      unfold cmp102Eq80PhysicalFineHeadTailDomainDecayPrefactor
        cmp102Eq80PhysicalFineHeadTailWalkBudget
      push_cast
      rw [pow_add, pow_succ, mul_pow]
      ring

/-- Absolute summability of every fixed-domain matrix series with domain
decay retained in the common prefactor. -/
theorem
    summable_norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer_of_split
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
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (Y : Finset (FinBox 4 (2 * Q)))
    {domainRatio summationRatio κ : ℝ}
    (hdomain0 : 0 ≤ domainRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκ : 0 ≤ κ)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        domainRatio * summationRatio)
    (hdecay : domainRatio ≤ Real.exp (-(κ * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1) :
    Summable fun headLength : ℕ =>
      ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y‖ := by
  let q : ℝ :=
    ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
      summationRatio
  let prefactor :=
    cmp102Eq80PhysicalFineHeadTailDomainDecayPrefactor
      (M := M) baseCoarseCovariance κ summationRatio layerWord Y
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hsmall
  have hmajor : Summable fun headLength : ℕ =>
      prefactor * q ^ headLength :=
    (summable_geometric_of_norm_lt_one hqnorm).mul_left prefactor
  apply Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun headLength =>
      norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer_le_geometric
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap layerWord choice Y
        hdomain0 hsummation0 hκ hsplit hdecay)
    hmajor

/-- The complete fixed-domain matrix coefficient has the exact geometric
resolvent prefactor and retains `exp (-κ * |Y|)`. -/
theorem
    norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient_le_domainCardDecay
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
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (Y : Finset (FinBox 4 (2 * Q)))
    {domainRatio summationRatio κ : ℝ}
    (hdomain0 : 0 ≤ domainRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκ : 0 ≤ κ)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate Rweak ≤
        domainRatio * summationRatio)
    (hdecay : domainRatio ≤ Real.exp (-(κ * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1) :
    ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y‖ ≤
      cmp102Eq80PhysicalFineHeadTailDomainDecayPrefactor
          (M := M) baseCoarseCovariance κ summationRatio layerWord Y *
        (1 -
          ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
            summationRatio)⁻¹ := by
  let layer := fun headLength : ℕ =>
    cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
      (headLength := headLength)
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice Y
  let q : ℝ :=
    ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
      summationRatio
  let prefactor :=
    cmp102Eq80PhysicalFineHeadTailDomainDecayPrefactor
      (M := M) baseCoarseCovariance κ summationRatio layerWord Y
  have hnorm :
      Summable fun headLength : ℕ => ‖layer headLength‖ :=
    summable_norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer_of_split
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap layerWord choice Y
      hdomain0 hsummation0 hκ hsplit hdecay hsmall
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hsmall
  have hmajor :
      HasSum (fun headLength : ℕ => prefactor * q ^ headLength)
        (prefactor * (1 - q)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hqnorm).mul_left prefactor
  change ‖∑' headLength : ℕ, layer headLength‖ ≤ _
  calc
    ‖∑' headLength : ℕ, layer headLength‖ ≤
        ∑' headLength : ℕ, ‖layer headLength‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' headLength : ℕ, prefactor * q ^ headLength := by
      exact Summable.tsum_le_tsum
        (fun headLength =>
          norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer_le_geometric
            anchor K hc hmass hK baseCoarseCovariance
            hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
            sigma hRweak hcap layerWord choice Y
            hdomain0 hsummation0 hκ hsplit hdecay)
        hnorm hmajor.summable
    _ = prefactor * (1 - q)⁻¹ := hmajor.tsum_eq
    _ = _ := rfl

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4TerminalMixedDerivativeDomainLayer
import YangMills.RG.BalabanCMP116SourcePi4TerminalGroupedPhysicalWeightedRow
import YangMills.RG.BalabanCMP116SourceSigmaZeroActiveCarrier
import YangMills.RG.PhysicalWeightedRowKernelMatrix

/-!
# Uniform bounds for terminal mixed connected-domain layers

The literal mixed weakening monomial is bounded by the source active-carrier
budget, while the ordered physical walk retains the fixed exponential kernel
rate.  Reverse terminal counting contributes only the local `Pi^4` branching
power.  Exact source-core partitioning then removes the number of terminal
charts from the connected-domain coefficient.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private theorem sourcePi4UnitDomain_injective_for_mixed_domain
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

/-- Scalar amplitude of a length-`n` mixed connected-domain layer before
the fixed spatial exponential is inserted. -/
noncomputable def cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
    (Δ : ℕ) (Ahead rho Rweak : ℝ) (n : ℕ) : ℝ :=
  (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
    (Rweak ^ (10000 * (n + 1)) * (Ahead * rho ^ n))

/-- A single terminal-chart contribution to a fixed connected mixed domain
has a volume-uniform, fixed-rate entrywise bound. -/
theorem norm_cmp116SourcePi4TerminalMixedDerivativeDomainLayer_le
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
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
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (Y : Finset (FinBox 4 (2 * Q)))
    (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    ‖cmp116SourcePi4TerminalMixedDerivativeDomainLayer
        (R := R) anchor K hc hmass hK sigma S root Y n
        terminal row col‖ ≤
      (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
        (Rweak ^ (10000 * (n + 1)) *
          ((Ahead * rho ^ n) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ))))) := by
  classical
  let walks := cmp99PhysicalPatchForwardTerminalWalks
    (cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))
    (cmp99SourcePi4ChartCore (M := M))
    cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal
  have hRweak0 : 0 ≤ Rweak := le_trans zero_le_one hRweak
  have hactive :
      ∀ chart : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
        (cmp99SourceDomainLargeBlocks chart.1.domain ∩
          cmp116SourceSigmaZero anchor).card ≤ 10000 := by
    intro chart
    have hcard :=
      (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
        (Label := Unit) anchor hrange).active_card_le chart
    simpa using hcard
  have hterm :
      ∀ walk ∈ walks,
        ‖cmp116SourcePi4ForwardWalkMixedDerivativeDomainTerm
            anchor K hc hmass hK sigma S root Y row col walk‖ ≤
          Rweak ^ (10000 * (n + 1)) *
            ((Ahead * rho ^ n) *
              Real.exp (-(rate *
                (physicalBondDist row.1 col.1 : ℝ)))) := by
    intro walk hwalk
    have hmem :=
      (mem_cmp99PhysicalPatchForwardTerminalWalks_iff
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal walk).1
        hwalk
    have hlen :=
      length_eq_of_mem_cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        hmem.1
    have hweighted :
        PhysicalCovarianceWeightedRowKernelBound
          (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
          physicalBondDist (Ahead * rho ^ n) rate := by
      rw [cmp116SourcePi4ForwardWalkOperator,
        cmp99PhysicalWalkTerm_eq_orderedProduct]
      simpa only [List.length_map, List.map_map, Function.comp_apply, hlen]
        using
          (Cert.orderedProduct_weightedRow htri walk.1
            (walk.2.map CMP99WalkStep.domain))
    have hExp :=
      physicalCovarianceExponentialKernelBound_of_weightedRow
        (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
        physicalBondDist hrate hweighted
    have hcoeff :
        ‖cmp116ComplexPhysicalOperatorCoefficient
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
            col.1 row.1 col.2 row.2‖ ≤
          (Ahead * rho ^ n) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ))) := by
      calc
        ‖cmp116ComplexPhysicalOperatorCoefficient
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
            col.1 row.1 col.2 row.2‖ ≤
            ‖cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk
              (singlePhysicalBondCochain col.1
                (EuclideanSpace.single col.2 (1 : ℝ))) row.1‖ :=
          norm_cmp116ComplexPhysicalOperatorCoefficient_le_targetValue
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
            col.1 row.1 col.2 row.2
        _ ≤ (Ahead * rho ^ n) *
              Real.exp (-(rate *
                (physicalBondDist row.1 col.1 : ℝ))) *
              ‖EuclideanSpace.single col.2 (1 : ℝ)‖ :=
          hExp.2.2 col.1 row.1
            (EuclideanSpace.single col.2 (1 : ℝ))
        _ = (Ahead * rho ^ n) *
              Real.exp (-(rate *
                (physicalBondDist row.1 col.1 : ℝ))) := by
          rw [EuclideanSpace.norm_single]
          simp
    have hwalkActive :
        (cmp116SourcePi4ForwardWalkActive anchor walk).card ≤
          10000 * (n + 1) := by
      have hbase :=
        (⟨walk.1, walk.2⟩ :
          CMP99GeneralizedWalk Unit
            ↥(cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))).card_active_le_mul_length_add_one
          (fun chart =>
            cmp99SourceDomainLargeBlocks chart.1.domain ∩
              cmp116SourceSigmaZero anchor)
          10000 hactive
      simpa only [cmp116SourcePi4ForwardWalkActive,
        CMP99GeneralizedWalk.length, hlen] using hbase
    have hcarrier :
        (cmp116SourcePi4ForwardWalkActive anchor walk \ S).card ≤
          10000 * (n + 1) :=
      (Finset.card_le_card Finset.sdiff_subset).trans hwalkActive
    have hmonomial :
        ‖cmp116ComplexWeakeningMonomial
            (cmp116SourcePi4ForwardWalkActive anchor walk \ S) sigma‖ ≤
          Rweak ^ (10000 * (n + 1)) := by
      have hbase :=
        norm_cmp116ComplexWeakeningMonomial_le_pow_card
          (cmp116SourcePi4ForwardWalkActive anchor walk \ S)
          sigma (fun _ => Rweak - 1) Rweak hRweak0
          (by
            intro d _hd
            convert hcap d using 1
            ring)
          (by
            intro d _hd
            convert le_rfl using 1
            ring)
      exact hbase.trans (pow_le_pow_right₀ hRweak hcarrier)
    unfold cmp116SourcePi4ForwardWalkMixedDerivativeDomainTerm
    by_cases hdomain :
        cmp116AnchoredLocalizationDomain
            (cmp116CoarseFaceAdj 4 (2 * Q))
            (fun _ : CMP99PhysicalPatchForwardWalkIndex
              (cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q)) => root)
            (cmp116SourcePi4ForwardWalkActive anchor) walk = Y
    · rw [if_pos hdomain]
      by_cases hsubset :
          S ⊆ cmp116SourcePi4ForwardWalkActive anchor walk
      · rw [if_pos hsubset, norm_mul]
        exact mul_le_mul hmonomial hcoeff (norm_nonneg _)
          (pow_nonneg hRweak0 _)
      · rw [if_neg hsubset]
        simp only [zero_mul, norm_zero]
        exact mul_nonneg (pow_nonneg hRweak0 _)
          (mul_nonneg
            (mul_nonneg hAhead (pow_nonneg hrho n))
            (Real.exp_pos _).le)
    · rw [if_neg hdomain]
      simp only [norm_zero]
      exact mul_nonneg (pow_nonneg hRweak0 _)
        (mul_nonneg
          (mul_nonneg hAhead (pow_nonneg hrho n))
          (Real.exp_pos _).le)
  have hcard :
      walks.card ≤ (cmp116SourcePi4TerminalBranching Δ) ^ n := by
    dsimp [walks]
    change _ ≤ (625 * 626 * Δ ^ (2 * 625)) ^ n
    exact card_cmp99PhysicalPatchForwardTerminalWalks_le_pow_simpleDomainBound
      (cmp116CoarseFaceAdj 4 Q)
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (cmp99SourcePi4ChartCore (M := M))
      cmp99SourcePi4ChartEnlarged physicalBondDist R 625 Δ
      hΔ hΔ1
      (fun chart => chart.1.domain)
      sourcePi4UnitDomain_injective_for_mixed_domain
      (fun left right hfollow =>
        cmp99SourcePi4ChartCanFollow_implies_domainsMeet
          (M := M) (Rrange := R) hrange left.1 right.1 hfollow)
      n terminal
  have hcardReal :
      (walks.card : ℝ) ≤
        (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) := by
    exact_mod_cast hcard
  rw [cmp116SourcePi4TerminalMixedDerivativeDomainLayer]
  change ‖∑ walk ∈ walks,
      cmp116SourcePi4ForwardWalkMixedDerivativeDomainTerm
        anchor K hc hmass hK sigma S root Y row col walk‖ ≤ _
  calc
    ‖∑ walk ∈ walks,
        cmp116SourcePi4ForwardWalkMixedDerivativeDomainTerm
          anchor K hc hmass hK sigma S root Y row col walk‖ ≤
        ∑ walk ∈ walks,
          ‖cmp116SourcePi4ForwardWalkMixedDerivativeDomainTerm
            anchor K hc hmass hK sigma S root Y row col walk‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _walk ∈ walks,
          Rweak ^ (10000 * (n + 1)) *
            ((Ahead * rho ^ n) *
              Real.exp (-(rate *
                (physicalBondDist row.1 col.1 : ℝ)))) :=
      Finset.sum_le_sum fun walk hwalk => hterm walk hwalk
    _ = (walks.card : ℝ) *
          (Rweak ^ (10000 * (n + 1)) *
            ((Ahead * rho ^ n) *
              Real.exp (-(rate *
                (physicalBondDist row.1 col.1 : ℝ))))) := by
      simp
    _ ≤ (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
          (Rweak ^ (10000 * (n + 1)) *
            ((Ahead * rho ^ n) *
              Real.exp (-(rate *
                (physicalBondDist row.1 col.1 : ℝ))))) := by
      exact mul_le_mul_of_nonneg_right hcardReal
        (mul_nonneg
          (pow_nonneg hRweak0 _)
          (mul_nonneg
            (mul_nonneg hAhead (pow_nonneg hrho n))
            (Real.exp_pos _).le))

/-- Exact source-core partitioning removes the terminal-chart count from a
fixed connected-domain coefficient. -/
theorem norm_cmp116SourcePi4MixedDerivativeDomainLayerCoefficient_le
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
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
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (Y : Finset (FinBox 4 (2 * Q)))
    (n : ℕ)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    ‖cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
        (R := R) (n := n) anchor K hc hmass hK
        sigma S root row col Y‖ ≤
      (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
        (Rweak ^ (10000 * (n + 1)) *
          ((Ahead * rho ^ n) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ))))) := by
  classical
  obtain ⟨terminal, hterminal, hsource, hunique⟩ :=
    cmp99SourcePi4UnitChartCore_corePartition col.1
  let selected : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)) := ⟨terminal, hterminal⟩
  have hterminalSum :
      (∑ next : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        cmp116SourcePi4TerminalMixedDerivativeDomainLayer
          (R := R) anchor K hc hmass hK sigma S root Y n
          next row col) =
        cmp116SourcePi4TerminalMixedDerivativeDomainLayer
          (R := R) anchor K hc hmass hK sigma S root Y n
          selected row col := by
    rw [Finset.sum_eq_single selected]
    · intro other _hother hne
      apply
        cmp116SourcePi4TerminalMixedDerivativeDomainLayer_eq_zero_of_not_mem_core
          (R := R) anchor K hc hmass hK sigma S root Y n other row col
      intro hotherSource
      apply hne
      exact Subtype.ext (hunique other.1 other.2 hotherSource)
    · intro hnot
      exact (hnot (Finset.mem_univ selected)).elim
  rw [← sum_cmp116SourcePi4TerminalMixedDerivativeDomainLayer
    (R := R) (n := n) anchor K hc hmass hK sigma S root Y row col,
    hterminalSum]
  exact
    norm_cmp116SourcePi4TerminalMixedDerivativeDomainLayer_le
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hRweak hcap S root Y n selected row col

/-- Named-amplitude form of the complete connected-domain layer estimate. -/
theorem norm_cmp116SourcePi4MixedDerivativeDomainLayerCoefficient_le'
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
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
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (Y : Finset (FinBox 4 (2 * Q)))
    (n : ℕ)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    ‖cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
        (R := R) (n := n) anchor K hc hmass hK
        sigma S root row col Y‖ ≤
      cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
          Δ Ahead rho Rweak n *
        Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))) := by
  simpa [cmp116SourcePi4MixedDerivativeDomainLayerAmplitude, mul_assoc]
    using
      norm_cmp116SourcePi4MixedDerivativeDomainLayerCoefficient_le
        anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
        sigma hRweak hcap S root Y n row col

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredLocalizationPartial
import YangMills.RG.BalabanCMP116SourcePi4TerminalMixedDerivativeDomainBound

/-!
# Uniform bounds for equation-(80) coefficients anchored at the whole `Pi^4`

The source-correct domain selector is inserted only as a zero-one mask on
each literal patched-walk term.  The physical weighted-row estimate and the
terminal-chart core partition therefore give the same volume-uniform
geometric majorant as before, now for the coefficient indexed by the entire
distinguished `Pi^4` carrier.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- One forward walk term masked by its literal full-`Pi^4` source domain. -/
noncomputable def cmp102Eq80SourcePi4CarrierAnchoredForwardWalkTerm
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))) : ℂ :=
  let active := cmp116SourcePi4ForwardWalkActive anchor walk
  if cmp116CarrierAnchoredLocalizationDomain
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4AnchorCarrier anchor)
      (cmp116SourcePi4ForwardWalkActive anchor) walk = Y then
    (if S ⊆ active then
      cmp116ComplexWeakeningMonomial (active \ S) sigma
    else 0) *
      cmp116ComplexPhysicalOperatorCoefficient
        (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
        col.1 row.1 col.2 row.2
  else 0

/-- Terminal-chart group of one full-carrier source-domain layer. -/
noncomputable def
    cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) : ℂ :=
  ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (cmp99SourcePi4ChartCore (M := M))
      cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal,
    cmp102Eq80SourcePi4CarrierAnchoredForwardWalkTerm
      anchor K hc hmass hK sigma S Y row col walk

/-- A terminal group is zero when the source coordinate is outside its
physical terminal core. -/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer_eq_zero_of_not_mem_core
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (hsource :
      col.1 ∉ cmp99SourcePi4ChartCore (M := M) terminal.1) :
    cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer
      (R := R) anchor K hc hmass hK sigma S Y n terminal row col = 0 := by
  classical
  simp only [cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer]
  apply Finset.sum_eq_zero
  intro walk hwalk
  have hterminal :=
    terminalDomain_eq_of_mem_cmp99PhysicalPatchForwardTerminalWalks
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (cmp99SourcePi4ChartCore (M := M))
      cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal walk hwalk
  have hzero :
      cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk
          (singlePhysicalBondCochain col.1
            (EuclideanSpace.single col.2 (1 : ℝ))) = 0 :=
    cmp99PhysicalPatchWalk_term_apply_eq_zero_of_not_mem_terminalCore
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK
      (⟨walk.1, walk.2⟩ :
        CMP99GeneralizedWalk Unit
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)))
      col.1 (EuclideanSpace.single col.2 (1 : ℝ))
      (by simpa [hterminal] using hsource)
  have hcoeff :
      cmp116ComplexPhysicalOperatorCoefficient
          (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
          col.1 row.1 col.2 row.2 = 0 := by
    simp [cmp116ComplexPhysicalOperatorCoefficient,
      cmp116PhysicalOperatorCoefficient, hzero]
  unfold cmp102Eq80SourcePi4CarrierAnchoredForwardWalkTerm
  split_ifs <;> simp [hcoeff]

/-- Summing terminal groups reconstructs the full-carrier layer
coefficient. -/
theorem
    sum_cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    (∑ terminal : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
      cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer
        (R := R) anchor K hc hmass hK sigma S Y n terminal row col) =
      cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
        (R := R) (n := n) anchor K hc hmass hK sigma S row col Y := by
  classical
  simp only [cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer]
  simp_rw [sum_cmp99PhysicalPatchForwardTerminalWalks]
  unfold cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
    cmp116CarrierAnchoredFiberCoefficient
  rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tail _htail
  simp [cmp102Eq80SourcePi4CarrierAnchoredForwardWalkTerm,
    cmp116CarrierAnchoredLocalizationDomain,
    cmp116SourcePi4MixedDerivativeLayerWalkTerm,
    cmp116SourcePi4ForwardWalkActive,
    cmp116SourcePi4LayerWalkActive,
    cmp116SourcePi4QuotientWalkActive,
    cmp116SourcePi4ForwardWalkOperator,
    CMP116SourcePi4LayerWalkIndex.walk,
    CMP99AnchoredWalk.active,
    CMP99AnchoredWalk.term,
    CMP99AnchoredWalk.toGeneralizedWalk]

private theorem sourcePi4UnitDomain_injective_for_carrier_domain
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

/-- One masked terminal contribution has the same physical fixed-rate
majorant as the unmasked walk family. -/
theorem
    norm_cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer_le
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
    (Y : Finset (FinBox 4 (2 * Q)))
    (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    ‖cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer
        (R := R) anchor K hc hmass hK sigma S Y n terminal row col‖ ≤
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
    simpa using
      (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
        (Label := Unit) anchor hrange).active_card_le chart
  have hterm :
      ∀ walk ∈ walks,
        ‖cmp102Eq80SourcePi4CarrierAnchoredForwardWalkTerm
            anchor K hc hmass hK sigma S Y row col walk‖ ≤
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
    unfold cmp102Eq80SourcePi4CarrierAnchoredForwardWalkTerm
    by_cases hdomain :
        cmp116CarrierAnchoredLocalizationDomain
            (cmp116CoarseFaceAdj 4 (2 * Q))
            (cmp102Eq80SourcePi4AnchorCarrier anchor)
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
      sourcePi4UnitDomain_injective_for_carrier_domain
      (fun left right hfollow =>
        cmp99SourcePi4ChartCanFollow_implies_domainsMeet
          (M := M) (Rrange := R) hrange left.1 right.1 hfollow)
      n terminal
  have hcardReal :
      (walks.card : ℝ) ≤
        (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) := by
    exact_mod_cast hcard
  rw [cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer]
  change ‖∑ walk ∈ walks,
      cmp102Eq80SourcePi4CarrierAnchoredForwardWalkTerm
        anchor K hc hmass hK sigma S Y row col walk‖ ≤ _
  calc
    ‖∑ walk ∈ walks,
        cmp102Eq80SourcePi4CarrierAnchoredForwardWalkTerm
          anchor K hc hmass hK sigma S Y row col walk‖ ≤
        ∑ walk ∈ walks,
          ‖cmp102Eq80SourcePi4CarrierAnchoredForwardWalkTerm
            anchor K hc hmass hK sigma S Y row col walk‖ :=
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

/-- The source-core partition removes the terminal-chart count from a fixed
full-carrier domain coefficient. -/
theorem
    norm_cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_le
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
    (Y : Finset (FinBox 4 (2 * Q)))
    (n : ℕ)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    ‖cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
        (R := R) (n := n) anchor K hc hmass hK sigma S row col Y‖ ≤
      cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
          Δ Ahead rho Rweak n *
        Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))) := by
  classical
  obtain ⟨terminal, hterminal, hsource, hunique⟩ :=
    cmp99SourcePi4UnitChartCore_corePartition col.1
  let selected : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)) := ⟨terminal, hterminal⟩
  have hterminalSum :
      (∑ next : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer
          (R := R) anchor K hc hmass hK sigma S Y n next row col) =
        cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer
          (R := R) anchor K hc hmass hK sigma S Y n selected row col := by
    rw [Finset.sum_eq_single selected]
    · intro other _hother hne
      apply
        cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer_eq_zero_of_not_mem_core
          (R := R) anchor K hc hmass hK sigma S Y n other row col
      intro hotherSource
      apply hne
      exact Subtype.ext (hunique other.1 other.2 hotherSource)
    · intro hnot
      exact (hnot (Finset.mem_univ selected)).elim
  rw [← sum_cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer
    (R := R) (n := n) anchor K hc hmass hK sigma S Y row col,
    hterminalSum]
  simpa [cmp116SourcePi4MixedDerivativeDomainLayerAmplitude, mul_assoc] using
    (norm_cmp102Eq80SourcePi4CarrierAnchoredTerminalDomainLayer_le
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hRweak hcap S Y n selected row col)

end

end YangMills.RG

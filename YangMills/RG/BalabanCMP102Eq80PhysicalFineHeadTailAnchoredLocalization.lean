/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailDirectionExpansion
import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredLocalization

/-!
# Carrier-anchored localization of literal CMP99 minimizer walks

An isolated head-tail walk need not be connected to the distinguished
source. The physical localization domain is instead the canonical
component of `Pi^4 ∪ active(walk)` which meets `Pi^4`. This module performs
the exact finite fiber regrouping at every fixed head length and then
retains the original length-ordered `tsum`.
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

/-- Canonical `Pi^4`-anchored domain of one literal head-tail walk term. -/
noncomputable def cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp116CarrierAnchoredLocalizationDomain
    (cmp116CoarseFaceAdj 4 (2 * Q))
    (cmp102Eq80SourcePi4AnchorCarrier anchor)
    (fun h : CMP99SourcePi4FineWalkIndex M Q R headLength =>
      cmp99SourcePi4FineHeadTailActive anchor h choice)
    head

/-- Every literal head-tail localization domain retains the complete
distinguished `Pi^4` carrier. -/
theorem cmp102Eq80SourcePi4AnchorCarrier_subset_fineHeadTailLocalizationDomain
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    cmp102Eq80SourcePi4AnchorCarrier anchor ⊆
      cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
        anchor head choice := by
  exact
    cmp116Carrier_subset_carrierAnchoredLocalizationDomain
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4AnchorCarrier anchor)
      (fun h : CMP99SourcePi4FineWalkIndex M Q R headLength =>
        cmp99SourcePi4FineHeadTailActive anchor h choice)
      head

/-- No block outside `Pi^4` and the literal head-tail carrier is introduced.
-/
theorem cmp102Eq80SourcePi4FineHeadTailLocalizationDomain_subset
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
        anchor head choice ⊆
      cmp102Eq80SourcePi4AnchorCarrier anchor ∪
        cmp99SourcePi4FineHeadTailActive anchor head choice := by
  exact
    cmp116CarrierAnchoredLocalizationDomain_subset
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4AnchorCarrier anchor)
      (fun h : CMP99SourcePi4FineWalkIndex M Q R headLength =>
        cmp99SourcePi4FineHeadTailActive anchor h choice)
      head

/-- Every literal head-tail domain anchored at `Pi^4` is face-connected. -/
theorem walkConnected_cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    walkConnected (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4FineHeadTailLocalizationDomain
        anchor head choice) := by
  exact
    cmp116CarrierAnchoredLocalizationDomain_walkConnected
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4AnchorCarrier anchor)
      (fun h : CMP99SourcePi4FineWalkIndex M Q R headLength =>
        cmp99SourcePi4FineHeadTailActive anchor h choice)
      head
      (cmp102Eq80SourcePi4AnchorCarrier_nonempty anchor)
      (walkConnected_cmp102Eq80SourcePi4AnchorCarrier anchor)

/-- At a fixed head length, the finite sum of literal equation-(80)
contributions regroups exactly by its canonical `Pi^4`-anchored domain. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDerivative_sum_eq_sum_carrierAnchoredFibers
    {M Q Nc R headLength n : ℕ}
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
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ) :
    (∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
      cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (cmp99SourcePi4PhysicalFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice)
        Δπ J A V₀') =
      ∑ Y ∈ cmp116CarrierAnchoredLocalizationDomains
          (cmp116CoarseFaceAdj 4 (2 * Q))
          (Finset.univ :
            Finset (CMP99SourcePi4FineWalkIndex M Q R headLength))
          (cmp102Eq80SourcePi4AnchorCarrier anchor)
          (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
            cmp99SourcePi4FineHeadTailActive anchor head choice),
        cmp116CarrierAnchoredFiberCoefficient
          (cmp116CoarseFaceAdj 4 (2 * Q))
          (Finset.univ :
            Finset (CMP99SourcePi4FineWalkIndex M Q R headLength))
          (cmp102Eq80SourcePi4AnchorCarrier anchor)
          (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
            cmp99SourcePi4FineHeadTailActive anchor head choice)
          (fun head =>
            cmp102Eq80PropagatorDirectionalDerivative D D₃ H
              (cmp99SourcePi4PhysicalFineHeadTailWordTerm
                anchor K hc hmass hK baseCoarseCovariance
                sigma head layerWord choice)
              Δπ J A V₀')
          Y := by
  simpa using
    cmp116_sum_eq_sum_carrierAnchoredFiberCoefficient
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (Finset.univ :
        Finset (CMP99SourcePi4FineWalkIndex M Q R headLength))
      (cmp102Eq80SourcePi4AnchorCarrier anchor)
      (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
        cmp99SourcePi4FineHeadTailActive anchor head choice)
      (fun head =>
        cmp102Eq80PropagatorDirectionalDerivative D D₃ H
          (cmp99SourcePi4PhysicalFineHeadTailWordTerm
            anchor K hc hmass hK baseCoarseCovariance
            sigma head layerWord choice)
          Δπ J A V₀')

/-- End-to-end, one complete coarse-choice contribution to equation (80)
is the original length-ordered `tsum`, with every finite head layer
regrouped by its literal connected `Pi^4`-anchored physical domain. -/
theorem
    cmp102Eq80PropagatorDirectionalDerivative_physicalChoiceWord_eq_tsum_carrierAnchoredFibers
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
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
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ) :
    cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (cmp99SourcePi4PhysicalBackgroundMinimizerChoiceWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice)
        Δπ J A V₀' =
      ∑' headLength : ℕ,
        ∑ Y ∈ cmp116CarrierAnchoredLocalizationDomains
            (cmp116CoarseFaceAdj 4 (2 * Q))
            (Finset.univ :
              Finset (CMP99SourcePi4FineWalkIndex M Q R headLength))
            (cmp102Eq80SourcePi4AnchorCarrier anchor)
            (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
              cmp99SourcePi4FineHeadTailActive anchor head choice),
          cmp116CarrierAnchoredFiberCoefficient
            (cmp116CoarseFaceAdj 4 (2 * Q))
            (Finset.univ :
              Finset (CMP99SourcePi4FineWalkIndex M Q R headLength))
            (cmp102Eq80SourcePi4AnchorCarrier anchor)
            (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
              cmp99SourcePi4FineHeadTailActive anchor head choice)
            (fun head =>
              cmp102Eq80PropagatorDirectionalDerivative D D₃ H
                (cmp99SourcePi4PhysicalFineHeadTailWordTerm
                  anchor K hc hmass hK baseCoarseCovariance
                  sigma head layerWord choice)
                Δπ J A V₀')
            Y := by
  rw [
    cmp102Eq80PropagatorDirectionalDerivative_physicalChoiceWord_eq_tsum_headWalks
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap hsmall layerWord choice
      D D₃ H Δπ J A V₀']
  apply tsum_congr
  intro headLength
  exact
    cmp102Eq80PhysicalFineHeadTailDerivative_sum_eq_sum_carrierAnchoredFibers
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ H Δπ J A V₀'

/-- Named carrier-anchored derivative series of one dependent coarse fine
walk choice. -/
noncomputable def cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries
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
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ) : ℝ :=
  ∑' headLength : ℕ,
    ∑ Y ∈ cmp116CarrierAnchoredLocalizationDomains
        (cmp116CoarseFaceAdj 4 (2 * Q))
        (Finset.univ :
          Finset (CMP99SourcePi4FineWalkIndex M Q R headLength))
        (cmp102Eq80SourcePi4AnchorCarrier anchor)
        (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
          cmp99SourcePi4FineHeadTailActive anchor head choice),
      cmp116CarrierAnchoredFiberCoefficient
        (cmp116CoarseFaceAdj 4 (2 * Q))
        (Finset.univ :
          Finset (CMP99SourcePi4FineWalkIndex M Q R headLength))
        (cmp102Eq80SourcePi4AnchorCarrier anchor)
        (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
          cmp99SourcePi4FineHeadTailActive anchor head choice)
        (fun head =>
          cmp102Eq80PropagatorDirectionalDerivative D D₃ H
            (cmp99SourcePi4PhysicalFineHeadTailWordTerm
              anchor K hc hmass hK baseCoarseCovariance
              sigma head layerWord choice)
            Δπ J A V₀')
        Y

/-- A complete physical coarse word contributes as the finite sum of the
already localized, length-ordered series of its dependent fine-walk
choices. -/
theorem
    cmp102Eq80PropagatorDirectionalDerivative_physicalWord_eq_sum_choiceAnchoredSeries
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
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
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ) :
    cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord)
        Δπ J A V₀' =
      ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ H Δπ J A V₀' := by
  rw [
    cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm_eq_sum_fineWalkChoices,
    cmp102Eq80PropagatorDirectionalDerivative_fintypeSum]
  apply Finset.sum_congr rfl
  intro choice _hchoice
  unfold cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries
  exact
    cmp102Eq80PropagatorDirectionalDerivative_physicalChoiceWord_eq_tsum_carrierAnchoredFibers
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap hsmall layerWord choice
      D D₃ H Δπ J A V₀'

/-- One complete outer Neumann layer contributes to equation (80) as its
source-ordered `tsum` of coarse words, each already refined and localized
by `Pi^4`-anchored physical domains. -/
theorem
    cmp102Eq80PropagatorDirectionalDerivative_physicalNeumannLayer_eq_tsum_localizedWords
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
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
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (neumannLength : ℕ)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ) :
    cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma neumannLength)
        Δπ J A V₀' =
      ∑' layerWord : Fin neumannLength → ℕ,
        ∑ choice :
            CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
          cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ H Δπ J A V₀' := by
  have hsummable :=
    summable_cmp99SourcePi4PhysicalBackgroundMinimizerWordTerms_of_source
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hsmall neumannLength
  rw [
    cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer_eq_tsum_words_of_source
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hsmall neumannLength,
    cmp102Eq80PropagatorDirectionalDerivative_tsum
      D D₃ H _ Δπ J A V₀' hsummable]
  apply tsum_congr
  intro layerWord
  exact
    cmp102Eq80PropagatorDirectionalDerivative_physicalWord_eq_sum_choiceAnchoredSeries
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap hsmall layerWord
      D D₃ H Δπ J A V₀'

end

end YangMills.RG

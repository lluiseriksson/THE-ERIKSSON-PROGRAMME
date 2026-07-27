/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailDomainCoefficient

/-!
# Reassembly of the complete physical-domain coefficients

At every head length, fibers outside the finite image of the canonical
carrier-anchored domain map vanish.  Consequently the literal finite
regrouping may be written as a sum over all finite domains.  The
domain-by-domain absolute summability theorem then justifies commuting this
finite domain sum with the head-length `tsum`.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- A carrier-anchored fiber outside the finite image of the domain map is
literally zero. -/
theorem cmp116CarrierAnchoredFiberCoefficient_eq_zero_of_not_mem_domains
    {ι α E : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    [AddCommMonoid E]
    (G : SimpleGraph ι) (source : Finset α)
    (anchorCarrier : Finset ι) (active : α → Finset ι)
    (term : α → E) (Y : Finset ι)
    (hY : Y ∉ cmp116CarrierAnchoredLocalizationDomains
      G source anchorCarrier active) :
    cmp116CarrierAnchoredFiberCoefficient
        G source anchorCarrier active term Y = 0 := by
  classical
  unfold cmp116CarrierAnchoredFiberCoefficient
  apply Finset.sum_eq_zero
  intro a ha
  have ha' := Finset.mem_filter.mp ha
  exfalso
  apply hY
  exact Finset.mem_image.mpr ⟨a, ha'.1, ha'.2⟩

/-- Summing the fibers over every finite domain is exactly the original
finite sum.  Domains outside the canonical finite image contribute zero. -/
theorem sum_cmp116CarrierAnchoredFiberCoefficient_univ_eq
    {ι α E : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    [AddCommMonoid E]
    (G : SimpleGraph ι) (source : Finset α)
    (anchorCarrier : Finset ι) (active : α → Finset ι)
    (term : α → E) :
    (∑ Y : Finset ι,
      cmp116CarrierAnchoredFiberCoefficient
        G source anchorCarrier active term Y) =
      ∑ a ∈ source, term a := by
  classical
  calc
    (∑ Y : Finset ι,
        cmp116CarrierAnchoredFiberCoefficient
          G source anchorCarrier active term Y) =
        ∑ Y ∈ cmp116CarrierAnchoredLocalizationDomains
            G source anchorCarrier active,
          cmp116CarrierAnchoredFiberCoefficient
            G source anchorCarrier active term Y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro Y _hY hYnot
      exact
        cmp116CarrierAnchoredFiberCoefficient_eq_zero_of_not_mem_domains
          G source anchorCarrier active term Y hYnot
    _ = ∑ a ∈ source, term a :=
      (cmp116_sum_eq_sum_carrierAnchoredFiberCoefficient
        G source anchorCarrier active term).symm

/-- At each head length, the finite image regrouping is the sum over all
physical domains of the literal equation-(80) derivative layer. -/
theorem
    sum_cmp102Eq80PhysicalFineHeadTail_carrierAnchoredFibers_eq_sum_domainLayers
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
    (∑ Y ∈ cmp116CarrierAnchoredLocalizationDomains
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
        Y) =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
          (headLength := headLength)
          anchor K hc hmass hK baseCoarseCovariance sigma
          layerWord choice D D₃ H Δπ J A V₀' Y := by
  have hregroup :=
    cmp102Eq80PhysicalFineHeadTailDerivative_sum_eq_sum_carrierAnchoredFibers
      (headLength := headLength)
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ H Δπ J A V₀'
  have hall :=
    sum_cmp116CarrierAnchoredFiberCoefficient_univ_eq
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
  calc
    _ = ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp102Eq80PropagatorDirectionalDerivative D D₃ H
            (cmp99SourcePi4PhysicalFineHeadTailWordTerm
              anchor K hc hmass hK baseCoarseCovariance
              sigma head layerWord choice)
            Δπ J A V₀' := hregroup.symm
    _ = ∑ Y : Finset (FinBox 4 (2 * Q)),
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
            Y := hall.symm
    _ = ∑ Y : Finset (FinBox 4 (2 * Q)),
          cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
            (headLength := headLength)
            anchor K hc hmass hK baseCoarseCovariance sigma
            layerWord choice D D₃ H Δπ J A V₀' Y := by
      apply Finset.sum_congr rfl
      intro Y _hY
      exact
        (cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer_eq_fiberCoefficient
          (headLength := headLength)
          anchor K hc hmass hK baseCoarseCovariance sigma
          layerWord choice D D₃ H Δπ J A V₀' Y).symm

/-- One dependent coarse/fine choice is exactly the finite sum of its
complete physical-domain coefficients.  The exchange of finite domain sum
and head-length `tsum` is justified by domainwise summability. -/
theorem
    cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries_eq_sum_domainCoefficients
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
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ) :
    cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ H Δπ J A V₀' =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalFineHeadTailDomainCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ H Δπ J A V₀' Y := by
  unfold cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries
  calc
    (∑' headLength : ℕ,
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
            Y) =
        ∑' headLength : ℕ,
          ∑ Y : Finset (FinBox 4 (2 * Q)),
            cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
              (headLength := headLength)
              anchor K hc hmass hK baseCoarseCovariance sigma
              layerWord choice D D₃ H Δπ J A V₀' Y := by
      apply tsum_congr
      intro headLength
      exact
        sum_cmp102Eq80PhysicalFineHeadTail_carrierAnchoredFibers_eq_sum_domainLayers
          (headLength := headLength)
          anchor K hc hmass hK baseCoarseCovariance sigma
          layerWord choice D D₃ H Δπ J A V₀'
    _ = ∑ Y : Finset (FinBox 4 (2 * Q)),
          ∑' headLength : ℕ,
            cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
              (headLength := headLength)
              anchor K hc hmass hK baseCoarseCovariance sigma
              layerWord choice D D₃ H Δπ J A V₀' Y := by
      rw [Summable.tsum_finsetSum]
      intro Y _hY
      exact
        summable_cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          sigma hRweak hcap hsmall layerWord choice
          D D₃ H Δπ J A V₀' Y
    _ = ∑ Y : Finset (FinBox 4 (2 * Q)),
          cmp102Eq80PhysicalFineHeadTailDomainCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ H Δπ J A V₀' Y := by
      rfl

/-- Terminal fixed-choice statement: the original physical minimizer word
contributes to equation (80) as the finite sum of the complete coefficients
of all literal physical domains. -/
theorem
    cmp102Eq80PropagatorDirectionalDerivative_physicalChoiceWord_eq_sum_domainCoefficients
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
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalFineHeadTailDomainCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ H Δπ J A V₀' Y := by
  rw [
    cmp102Eq80PropagatorDirectionalDerivative_physicalChoiceWord_eq_tsum_carrierAnchoredFibers
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap hsmall layerWord choice
      D D₃ H Δπ J A V₀']
  change
    cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ H Δπ J A V₀' =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalFineHeadTailDomainCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ H Δπ J A V₀' Y
  exact
    cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries_eq_sum_domainCoefficients
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice
      D D₃ H Δπ J A V₀'

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailAbsoluteBound

/-!
# Absolutely convergent physical-domain fibers of the CMP99 minimizer

At each head length the literal rectangular fine-head/tail terms are grouped
by their canonical `Pi^4`-anchored physical domain.  The preceding absolute
walk majorant dominates every such fiber.  Hence each fixed-domain series is
genuinely summable; no cancellation between different domains is used.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- Restricting a finite family to one carrier-anchored fiber cannot
increase the sum of the norms of its terms. -/
theorem norm_cmp116CarrierAnchoredFiberCoefficient_le_sum_norm
    {ι α E : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    [SeminormedAddCommGroup E]
    (G : SimpleGraph ι) (source : Finset α)
    (anchorCarrier : Finset ι) (active : α → Finset ι)
    (term : α → E) (Y : Finset ι) :
    ‖cmp116CarrierAnchoredFiberCoefficient
        G source anchorCarrier active term Y‖ ≤
      ∑ a ∈ source, ‖term a‖ := by
  classical
  unfold cmp116CarrierAnchoredFiberCoefficient
  calc
    ‖∑ a ∈ source.filter (fun a =>
        cmp116CarrierAnchoredLocalizationDomain
          G anchorCarrier active a = Y), term a‖ ≤
      ∑ a ∈ source.filter (fun a =>
        cmp116CarrierAnchoredLocalizationDomain
          G anchorCarrier active a = Y), ‖term a‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ source, ‖term a‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun a _ha _hout => norm_nonneg (term a))

/-- The rectangular matrix coefficient at one head length and one literal
carrier-anchored physical domain. -/
noncomputable def
    cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
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
    (Y : Finset (FinBox 4 (2 * Q))) :
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  cmp116CarrierAnchoredFiberCoefficient
    (cmp116CoarseFaceAdj 4 (2 * Q))
    (Finset.univ :
      Finset (CMP99SourcePi4FineWalkIndex M Q R headLength))
    (cmp102Eq80SourcePi4AnchorCarrier anchor)
    (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
      cmp99SourcePi4FineHeadTailActive anchor head choice)
    (fun head =>
      cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma head layerWord choice)
    Y

/-- A fixed physical-domain matrix layer is dominated by the sum of the
norms of all literal terms at that head length. -/
theorem norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer_le
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
    (Y : Finset (FinBox 4 (2 * Q))) :
    ‖cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y‖ ≤
      ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
        ‖cmp99SourcePi4ComplexFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice‖ := by
  classical
  simpa [cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer] using
    (norm_cmp116CarrierAnchoredFiberCoefficient_le_sum_norm
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (Finset.univ :
        Finset (CMP99SourcePi4FineWalkIndex M Q R headLength))
      (cmp102Eq80SourcePi4AnchorCarrier anchor)
      (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
        cmp99SourcePi4FineHeadTailActive anchor head choice)
      (fun head =>
        cmp99SourcePi4ComplexFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice)
      Y)

/-- Every fixed physical-domain rectangular matrix series is absolutely
summable over the head length. -/
theorem summable_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
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
    (Y : Finset (FinBox 4 (2 * Q))) :
    Summable fun headLength : ℕ =>
      cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y := by
  apply Summable.of_norm_bounded
    (summable_sum_norm_cmp99SourcePi4ComplexFineHeadTailWordTerm
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1 sigma
      hRweak hcap hsmall layerWord choice)
  intro headLength
  exact
    norm_cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer_le
      (headLength := headLength)
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice Y

/-- Complete rectangular coefficient of one literal physical domain. -/
noncomputable def cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
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
    (Y : Finset (FinBox 4 (2 * Q))) :
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  ∑' headLength : ℕ,
    cmp102Eq80PhysicalFineHeadTailDomainMatrixLayer
      (headLength := headLength)
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice Y

end

end YangMills.RG

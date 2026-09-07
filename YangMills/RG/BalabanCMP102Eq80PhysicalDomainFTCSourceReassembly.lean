/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCMinimizerIncrement
import YangMills.RG.BalabanCMP102Eq80PhysicalOuterNeumannSourceMetricFTC

/-!
# Source-ordered reassembly of the complete physical-domain FTC coefficients

At one fixed outer Neumann length, the physical equation-(80) increment was
already identified with a `tsum` of finite domain sums.  This file justifies
the converse source-facing presentation: the finite domain sum may be moved
outside the absolutely summable layer-word series.

The support argument is literal.  Every nonzero fiber is the canonical
carrier-anchored localization domain of a physical fine walk, hence is
nonempty and face-connected.  Empty or disconnected finite sets therefore
contribute zero at every subsequent FTC level.

This result does not identify these patched-walk coefficients term by term
with the separate recursive Faa di Bruno connected-domain activities.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- A scalar physical-domain derivative layer vanishes unless its finite
carrier is a nonempty face-connected localization domain. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer_eq_zero_of_not_localizationDomain
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
    (V₀' : FineField M Q Nc →L[ℝ] ℝ)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hY : ¬(Y.Nonempty ∧
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y)) :
    cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance sigma
        layerWord choice D D₃ H Δπ J A V₀' Y = 0 := by
  classical
  rw [
    cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer_eq_fiberCoefficient]
  apply cmp116CarrierAnchoredFiberCoefficient_eq_zero_of_not_mem_domains
  intro hmem
  apply hY
  obtain ⟨head, _hhead, rfl⟩ := Finset.mem_image.mp hmem
  constructor
  · exact
      (cmp102Eq80SourcePi4AnchorCarrier_nonempty anchor).mono
        (cmp116Carrier_subset_carrierAnchoredLocalizationDomain
          (cmp116CoarseFaceAdj 4 (2 * Q))
          (cmp102Eq80SourcePi4AnchorCarrier anchor)
          (fun h : CMP99SourcePi4FineWalkIndex M Q R headLength =>
            cmp99SourcePi4FineHeadTailActive anchor h choice)
          head)
  · exact
      cmp116CarrierAnchoredLocalizationDomain_walkConnected
        (cmp116CoarseFaceAdj 4 (2 * Q))
        (cmp102Eq80SourcePi4AnchorCarrier anchor)
        (fun h : CMP99SourcePi4FineWalkIndex M Q R headLength =>
          cmp99SourcePi4FineHeadTailActive anchor h choice)
        head
        (cmp102Eq80SourcePi4AnchorCarrier_nonempty anchor)
        (walkConnected_cmp102Eq80SourcePi4AnchorCarrier anchor)

/-- The complete fine-head coefficient inherits the exact support of every
one of its absolutely summable head-length layers. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_zero_of_not_localizationDomain
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
    (V₀' : FineField M Q Nc →L[ℝ] ℝ)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hY : ¬(Y.Nonempty ∧
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y)) :
    cmp102Eq80PhysicalFineHeadTailDomainCoefficient
        anchor K hc hmass hK baseCoarseCovariance sigma
        layerWord choice D D₃ H Δπ J A V₀' Y = 0 := by
  unfold cmp102Eq80PhysicalFineHeadTailDomainCoefficient
  calc
    (∑' headLength : ℕ,
      cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer
        (headLength := headLength)
        anchor K hc hmass hK baseCoarseCovariance sigma
        layerWord choice D D₃ H Δπ J A V₀' Y) =
        ∑' _headLength : ℕ, 0 := by
      apply tsum_congr
      intro headLength
      exact
        cmp102Eq80PhysicalFineHeadTailDomainDerivativeLayer_eq_zero_of_not_localizationDomain
          anchor K hc hmass hK baseCoarseCovariance sigma
          layerWord choice D D₃ H Δπ J A V₀' Y hY
    _ = 0 := tsum_zero

/-- One literal radial FTC contribution is zero outside the physical
localization-domain support. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_eq_zero_of_not_localizationDomain
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
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hY : ¬(Y.Nonempty ∧
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y)) :
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance sigma
        layerWord choice D D₃ V₀ P T Δπ J A Y = 0 := by
  unfold cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
  have hzero :
      (fun t : ℝ =>
        cmp102Eq80PhysicalFineHeadTailDomainCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) Y) =
        fun _t : ℝ => 0 := by
    funext t
    exact
      cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_zero_of_not_localizationDomain
        anchor K hc hmass hK baseCoarseCovariance sigma
        layerWord choice D D₃ (P + t • T) Δπ J A
        (fderiv ℝ V₀ (A - (P + t • T) (D A))) Y hY
  rw [hzero]
  simp

/-- The finite dependent-choice sum remains exactly supported on nonempty
face-connected domains. -/
theorem
    cmp102Eq80PhysicalLayerWordDomainFTCContribution_eq_zero_of_not_localizationDomain
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
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hY : ¬(Y.Nonempty ∧
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y)) :
    cmp102Eq80PhysicalLayerWordDomainFTCContribution
        (R := R) anchor K hc hmass hK baseCoarseCovariance sigma
        layerWord D D₃ V₀ P T Δπ J A Y = 0 := by
  classical
  unfold cmp102Eq80PhysicalLayerWordDomainFTCContribution
  apply Finset.sum_eq_zero
  intro choice _hchoice
  exact
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_eq_zero_of_not_localizationDomain
      anchor K hc hmass hK baseCoarseCovariance sigma
      layerWord choice D D₃ V₀ P T Δπ J A Y hY

/-- At one fixed outer length, the complete physical-domain FTC increment is
exactly the finite sum of its fixed-domain layer-word `tsum`s.  Summability is
required only for genuine physical localization domains; every other finite
set vanishes literally by the preceding support theorem. -/
theorem
    cmp102Eq80SourcePi4PhysicalDomainFTCMinimizerIncrement_eq_sum_neumannDomainFTC
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
    (hsummable :
      ∀ Y : CMP116LocalizationDomain M (2 * Q),
        Summable (fun layerWord : Fin n → ℕ =>
          cmp102Eq80PhysicalLayerWordDomainFTCContribution
            (R := R) anchor K hc hmass hK baseCoarseCovariance sigma
            layerWord D D₃ V₀ P T Δπ J A Y.blocks)) :
    (∑' layerWord : Fin n → ℕ,
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalLayerWordDomainFTCContribution
          (R := R) anchor K hc hmass hK baseCoarseCovariance sigma
          layerWord D D₃ V₀ P T Δπ J A Y) =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalNeumannDomainFTCContribution
          (R := R) (n := n) anchor K hc hmass hK
          baseCoarseCovariance sigma D D₃ V₀ P T Δπ J A Y := by
  classical
  unfold cmp102Eq80PhysicalNeumannDomainFTCContribution
  rw [Summable.tsum_finsetSum]
  intro Y _hYmem
  by_cases hY : Y.Nonempty ∧
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y
  · let Yphys : CMP116LocalizationDomain M (2 * Q) :=
      { blocks := Y
        nonempty := hY.1
        connected := hY.2 }
    simpa [Yphys] using hsummable Yphys
  · have hzero :
        (fun layerWord : Fin n → ℕ =>
          cmp102Eq80PhysicalLayerWordDomainFTCContribution
            (R := R) anchor K hc hmass hK baseCoarseCovariance sigma
            layerWord D D₃ V₀ P T Δπ J A Y) =
          fun _layerWord : Fin n → ℕ => 0 := by
      funext layerWord
      exact
        cmp102Eq80PhysicalLayerWordDomainFTCContribution_eq_zero_of_not_localizationDomain
          anchor K hc hmass hK baseCoarseCovariance sigma
          layerWord D D₃ V₀ P T Δπ J A Y hY
    rw [hzero]
    exact summable_zero

set_option maxHeartbeats 4000000 in
/-- Source-specialized fixed-layer reassembly.  The layer-word summability
premise of the abstract interchange is generated by the physical
source-metric theorem, so no summability binder remains in this endpoint. -/
theorem
    cmp102Eq80SourcePi4PhysicalDomainFTCMinimizerIncrement_eq_sum_neumannDomainFTC_of_source
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor K hc hmass hK (fun _ => 1)) coarseRate)
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀)
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 ≤ κcard)
    (hκmetric : 0 ≤ κmetric)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M)
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse)
          Ahead rho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (n : ℕ) :
    let baseCoarseCovariance :=
      cmp99SourcePi4WeakenedCoarseCovariance
        (R := R) anchor K hc hmass hK (fun _ => 1)
        hcoarseRate hcoarse
    let term : ℕ → (CoarseField Q Nc →L[ℝ] FineField M Q Nc) :=
      fun neumannLength =>
        cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
          (R := R) anchor K hc hmass hK
          baseCoarseCovariance sigma neumannLength
    let P := cmp102Eq80MinimizerPartialSum term n
    let T := term n
    cmp102Eq80SourcePi4PhysicalDomainFTCMinimizerIncrement
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma n D D₃ V₀ Δπ J A =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalNeumannDomainFTCContribution
          (R := R) (n := n) anchor K hc hmass hK
          baseCoarseCovariance sigma D D₃ V₀ P T Δπ J A Y := by
  obtain ⟨C, hC0, hfixed⟩ :=
    exists_uniform_bound_cmp102Eq80SourcePi4PhysicalOuterNeumannDomainFTC
      anchor K hsourceRange hc hmass hK hcoarseRate hcoarse
      hAhead hrho hrate hgeom Cert htri hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hcontourSmall hcoarseSmall
      D D₃ V₀ Δπ J A hV₀
      hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
      hsplit hcardDecay hmetricDecay hsmall
  let baseCoarseCovariance :=
    cmp99SourcePi4WeakenedCoarseCovariance
      (R := R) anchor K hc hmass hK (fun _ => 1)
      hcoarseRate hcoarse
  let term : ℕ → (CoarseField Q Nc →L[ℝ] FineField M Q Nc) :=
    fun neumannLength =>
      cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma neumannLength
  let P := cmp102Eq80MinimizerPartialSum term n
  let T := term n
  unfold cmp102Eq80SourcePi4PhysicalDomainFTCMinimizerIncrement
  exact
    cmp102Eq80SourcePi4PhysicalDomainFTCMinimizerIncrement_eq_sum_neumannDomainFTC
      anchor K hc hmass hK baseCoarseCovariance sigma
      D D₃ V₀ P T Δπ J A
      (fun Y => by
        simpa [baseCoarseCovariance, term, P, T] using
          (hfixed n Y).1)

end

end YangMills.RG

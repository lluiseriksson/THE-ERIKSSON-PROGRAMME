/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalFineHeadTailAbsoluteSummability
import YangMills.RG.BalabanCMP102Eq80PropagatorDerivativeUniform
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCContribution

/-!
# Dominated interchange of physical words and the equation-(80) FTC integral

For one fixed outer Neumann length, the physical coarse words are
absolutely summable.  The equation-(80) derivative has a common bound on
the compact radial segment.  These facts justify the actual interchange
of the infinite word sum with the FTC integral and retain the finite
localization sum over physical domains.
-/

open scoped RealInnerProductSpace
open MeasureTheory TopologicalSpace

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- For a fixed Neumann length, the physical word `tsum` commutes with the
literal radial FTC integral. -/
theorem
    tsum_integral_cmp102Eq80PhysicalWordAffineDerivative_eq_integral_tsum
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
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀) :
    (∑' layerWord : Fin neumannLength → ℕ,
      ∫ t in (0 : ℝ)..1,
        cmp102Eq80PropagatorDirectionalDerivative D D₃
          (P + t • T)
          (cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm
            (R := R) anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord)
          Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A)))) =
      ∫ t in (0 : ℝ)..1,
        ∑' layerWord : Fin neumannLength → ℕ,
          cmp102Eq80PropagatorDirectionalDerivative D D₃
            (P + t • T)
            (cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm
              (R := R) anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord)
            Δπ J A
            (fderiv ℝ V₀ (A - (P + t • T) (D A))) := by
  let direction := fun layerWord : Fin neumannLength → ℕ =>
    cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm
      (R := R) anchor K hc hmass hK baseCoarseCovariance sigma layerWord
  let f := fun layerWord : Fin neumannLength → ℕ =>
    (⟨fun t : ℝ =>
        cmp102Eq80AffinePropagatorDirectionalDerivativeCLM
          D D₃ V₀ P T Δπ J A t (direction layerWord),
      continuous_cmp102Eq80PropagatorDirectionalDerivative
        D D₃ V₀ (fun t : ℝ => P + t • T) (direction layerWord)
        Δπ J A (by fun_prop)
        (hV₀.continuous_fderiv one_ne_zero)⟩ : C(ℝ, ℝ))
  have hdirection : Summable fun layerWord : Fin neumannLength → ℕ =>
      ‖direction layerWord‖ := by
    exact
      summable_norm_cmp99SourcePi4PhysicalBackgroundMinimizerWordTerms_of_source
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1 sigma
        hradius hRweak hdiff hcap hsmall neumannLength
  have hf :
      Summable fun layerWord : Fin neumannLength → ℕ =>
        ‖(f layerWord).restrict
          (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
    simpa [f, direction] using
      summable_norm_restrict_cmp102Eq80AffinePropagatorDirectionalDerivative
        D D₃ V₀ P T Δπ J A direction hdirection hV₀
  simpa [f, direction,
    cmp102Eq80AffinePropagatorDirectionalDerivativeCLM,
    cmp102Eq80PropagatorDirectionalDerivativeCLM_apply] using
    intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hf

/-- For a fixed outer Neumann layer, the finite-domain FTC contributions
sum to the radial integral of the literal physical layer derivative.  The
infinite word/integral interchange is justified by absolute summability,
not by a formal rearrangement. -/
theorem
    tsum_cmp102Eq80PhysicalLayerWordDomainFTCContribution_eq_integral_neumannLayer
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
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀) :
    (∑' layerWord : Fin neumannLength → ℕ,
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalLayerWordDomainFTCContribution
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord D D₃ V₀ P T Δπ J A Y) =
      ∫ t in (0 : ℝ)..1,
        cmp102Eq80PropagatorDirectionalDerivative D D₃
          (P + t • T)
          (cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
            (R := R) anchor K hc hmass hK baseCoarseCovariance
            sigma neumannLength)
          Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) := by
  calc
    (∑' layerWord : Fin neumannLength → ℕ,
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PhysicalLayerWordDomainFTCContribution
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord D D₃ V₀ P T Δπ J A Y) =
      ∑' layerWord : Fin neumannLength → ℕ,
        ∫ t in (0 : ℝ)..1,
          cmp102Eq80PropagatorDirectionalDerivative D D₃
            (P + t • T)
            (cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm
              (R := R) anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord)
            Δπ J A
            (fderiv ℝ V₀ (A - (P + t • T) (D A))) := by
      apply tsum_congr
      intro layerWord
      rw [
        ← integral_sum_cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries_eq_sum_layerWordDomainFTCContributions
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          sigma hRweak hcap hsmall layerWord
          D D₃ V₀ P T Δπ J A hV₀]
      apply intervalIntegral.integral_congr
      intro t _ht
      exact
        (cmp102Eq80PropagatorDirectionalDerivative_physicalWord_eq_sum_choiceAnchoredSeries
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
          sigma hradius hRweak hdiff hcap hsmall layerWord
          D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A)))).symm
    _ =
      ∫ t in (0 : ℝ)..1,
        ∑' layerWord : Fin neumannLength → ℕ,
          cmp102Eq80PropagatorDirectionalDerivative D D₃
            (P + t • T)
            (cmp99SourcePi4PhysicalBackgroundMinimizerWordTerm
              (R := R) anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord)
            Δπ J A
            (fderiv ℝ V₀ (A - (P + t • T) (D A))) :=
      tsum_integral_cmp102Eq80PhysicalWordAffineDerivative_eq_integral_tsum
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
        sigma hradius hRweak hdiff hcap hsmall neumannLength
        D D₃ V₀ P T Δπ J A hV₀
    _ =
      ∫ t in (0 : ℝ)..1,
        cmp102Eq80PropagatorDirectionalDerivative D D₃
          (P + t • T)
          (cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
            (R := R) anchor K hc hmass hK baseCoarseCovariance
            sigma neumannLength)
          Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      have hsummable :=
        summable_cmp99SourcePi4PhysicalBackgroundMinimizerWordTerms_of_source
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1 sigma
          hradius hRweak hdiff hcap hsmall neumannLength
      rw [
        cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer_eq_tsum_words_of_source
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1 sigma
          hradius hRweak hdiff hcap hsmall neumannLength]
      exact
        (cmp102Eq80PropagatorDirectionalDerivative_tsum
          D D₃ (P + t • T) _ Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) hsummable).symm

end

end YangMills.RG

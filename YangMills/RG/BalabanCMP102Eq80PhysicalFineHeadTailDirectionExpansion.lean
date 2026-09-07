/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalFineHeadTailWordExpansion
import YangMills.RG.BalabanCMP102Eq80PropagatorDerivativeDirectionSeries

/-!
# Literal CMP99 walks inside the CMP102 equation-(80) derivative

The nonlinear equation-(80) potential is telescoped only in its original
outer minimizer order. Inside one exact increment, its propagator
derivative is linear in the direction. This module inserts one complete
source-produced coarse-choice direction as the genuinely summable series
of its reconstructed literal head-tail walks.
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

/-- A complete reconstructed coarse-choice direction contributes to the
literal equation-(80) derivative as the length-ordered sum of its literal
physical head-tail walk contributions. -/
theorem
    cmp102Eq80PropagatorDirectionalDerivative_physicalChoiceWord_eq_tsum_headWalks
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
        ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
          cmp102Eq80PropagatorDirectionalDerivative D D₃ H
            (cmp99SourcePi4PhysicalFineHeadTailWordTerm
              anchor K hc hmass hK baseCoarseCovariance
              sigma head layerWord choice)
            Δπ J A V₀' := by
  have hsummable :=
    summable_cmp99SourcePi4PhysicalFineHeadTailWordTerms_of_source
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap hsmall layerWord choice
  rw [
    cmp99SourcePi4PhysicalBackgroundMinimizerChoiceWordTerm_eq_tsum_headWalks_of_source
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap hsmall layerWord choice,
    cmp102Eq80PropagatorDirectionalDerivative_tsum
      D D₃ H _ Δπ J A V₀' hsummable]
  apply tsum_congr
  intro headLength
  exact
    cmp102Eq80PropagatorDirectionalDerivative_fintypeSum
      D D₃ H
      (fun head : CMP99SourcePi4FineWalkIndex M Q R headLength =>
        cmp99SourcePi4PhysicalFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice)
      Δπ J A V₀'

/-- For a fixed base propagator and physical field, one literal walk
contribution to equation (80) reads only its exact weakening carrier. -/
theorem
    cmp102Eq80PropagatorDirectionalDerivative_physicalFineHeadTail_eq_of_eqOn_active
    {M Q Nc R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma tau : FinBox 4 (2 * Q) → ℂ)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (H : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (V₀' : FineField M Q Nc →L[ℝ] ℝ)
    (h : ∀ d ∈ cmp99SourcePi4FineHeadTailActive
      anchor head choice, sigma d = tau d) :
    cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (cmp99SourcePi4PhysicalFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice)
        Δπ J A V₀' =
      cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (cmp99SourcePi4PhysicalFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          tau head layerWord choice)
        Δπ J A V₀' := by
  rw [
    cmp99SourcePi4PhysicalFineHeadTailWordTerm_eq_of_eqOn_active
      anchor K hc hmass hK baseCoarseCovariance
      sigma tau head layerWord choice h]

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredLocalizationSeries

/-!
# Continuity of complete physical source-domain coefficients

The repeated FTC expansion evaluates the localized equation-(80) jets along
a variable weakening contour.  This file proves that the complete physical
source-domain coefficient is continuous along every coordinatewise
continuous contour which remains in the same uniform complex polydisc.

The proof is source-faithful.  Every finite walk layer is a finite sum whose
only contour dependence is the literal weakening monomial.  The complete
coefficient is then continuous by the already proved, volume-uniform
geometric majorant and `continuous_tsum`.  No integrability or continuity
hypothesis on the completed coefficient is exposed to a caller.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- A literal finite complex weakening monomial is continuous along every
coordinatewise continuous contour. -/
theorem continuous_cmp116ComplexWeakeningMonomial_comp
    {Δ T : Type*} [TopologicalSpace T]
    (active : Finset Δ) (sigma : T → Δ → ℂ)
    (hsigma : ∀ d, Continuous fun t => sigma t d) :
    Continuous fun t =>
      cmp116ComplexWeakeningMonomial active (sigma t) := by
  classical
  unfold cmp116ComplexWeakeningMonomial
  fun_prop

/-- One literal physical mixed-derivative walk term is continuous along a
coordinatewise continuous weakening contour. -/
theorem continuous_cmp116SourcePi4MixedDerivativeLayerWalkTerm_comp
    {M Q Nc R n : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : T → FinBox 4 (2 * Q) → ℂ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (S : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n) :
    Continuous fun t =>
      cmp116SourcePi4MixedDerivativeLayerWalkTerm
        anchor K hc hmass hK (sigma t) S row col idx := by
  classical
  by_cases hS : S ⊆ cmp116SourcePi4LayerWalkActive anchor idx
  · simp only [cmp116SourcePi4MixedDerivativeLayerWalkTerm, hS, if_true]
    exact
      (continuous_cmp116ComplexWeakeningMonomial_comp
        _ sigma hsigma).mul continuous_const
  · simp only [cmp116SourcePi4MixedDerivativeLayerWalkTerm, hS, if_false,
      zero_mul]
    exact continuous_const

/-- Every fixed walk-length source-domain layer is continuous along the
physical weakening contour. -/
theorem
    continuous_cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_comp
    {M Q Nc R n : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : T → FinBox 4 (2 * Q) → ℂ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (S : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (Y : Finset (FinBox 4 (2 * Q))) :
    Continuous fun t =>
      cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
        (R := R) (n := n) anchor K hc hmass hK
        (sigma t) S row col Y := by
  classical
  unfold cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
    cmp116CarrierAnchoredFiberCoefficient
  apply continuous_finset_sum
  intro idx _hidx
  exact
    continuous_cmp116SourcePi4MixedDerivativeLayerWalkTerm_comp
      anchor K hc hmass hK sigma hsigma S row col idx

/-- The complete physical source-domain coefficient is continuous along
every coordinatewise continuous contour contained in a common uniform
complex polydisc. -/
theorem
    continuous_cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient_comp
    {M Q Nc R Δ : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T]
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
    (sigma : T → FinBox 4 (2 * Q) → ℂ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ t d, ‖sigma t d‖ ≤ Rweak)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    Continuous fun t =>
      cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
        (R := R) anchor K hc hmass hK (sigma t) S row col Y := by
  unfold cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
  apply continuous_tsum
  · intro n
    exact
      continuous_cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_comp
        anchor K hc hmass hK sigma hsigma S row col Y
  · exact
      (hasSum_cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
        Δ Ahead rho Rweak hsmall).summable
  · intro n t
    have hbound :=
      norm_cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_le
        anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
        (sigma t) hRweak (hcap t) S Y n row col
    have hamp :
        0 ≤ cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
          Δ Ahead rho Rweak n := by
      unfold cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
      positivity
    have hexp :
        Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr
        (mul_nonneg hrate.le (Nat.cast_nonneg _))
    exact hbound.trans (mul_le_of_le_one_right hamp hexp)

end

end YangMills.RG

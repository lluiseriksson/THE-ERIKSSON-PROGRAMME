/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FaaDiBrunoPhysicalDomainExpansionAt
import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredLocalizationContinuity

/-!
# Continuity of the localized equation-(80) Faà di Bruno coefficients

The physical FTC tree integrates derivatives while one weakening coordinate
varies.  The variable-point localization theorem expresses each such
derivative as a finite sum of physical domain coefficients.  Here we prove
that every individual coefficient is continuous along the contour, hence
interval integrable, from the actual regularity of `V₀` and the uniformly
convergent physical covariance series.

No continuity or integrability premise for a localized coefficient is added
to the public interface.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- One physical domain-choice term is continuous along every
coordinatewise continuous contour in the common physical polydisc. -/
theorem continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_comp
    {M Q Nc R Δ n : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
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
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (sigma : T → FinBox 4 (2 * Q) → ℝ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (choice : CMP102Eq80FaaDiBrunoDomainChoice
      (Q := Q) partition)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ t d, ‖(sigma t d : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ partition.length V₀) :
    Continuous fun t =>
      cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase (sigma t) L coordinates partition choice := by
  have hsigma' : Continuous sigma := continuous_pi hsigma
  have hbase :
      Continuous fun t =>
        cmp116FiniteMultiaffineInterpolation
          (fun u =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK u ∅)
          vertexBase L (sigma t) :=
    (contDiff_cmp116FiniteMultiaffineInterpolation
      0 _ vertexBase L).continuous.comp hsigma'
  have hVouter :
      ContDiff ℝ partition.length
        (cmp102Eq80PotentialAsFunctionOfPropagator
          D D₃ V₀ Δπ J A) :=
    contDiff_cmp102Eq80PotentialAsFunctionOfPropagator
      partition.length D D₃ V₀ Δπ J A
      hV₀
  have houter :
      Continuous fun t =>
        ftaylorSeries ℝ
          (cmp102Eq80PotentialAsFunctionOfPropagator
            D D₃ V₀ Δπ J A)
          (cmp116FiniteMultiaffineInterpolation
            (fun u =>
              cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                (R := R) anchor K hc hmass hK u ∅)
            vertexBase L (sigma t))
          partition.length :=
    hVouter.continuous_iteratedFDeriv'.comp hbase
  have hargs (block : Fin partition.length) :
      Continuous fun t =>
        cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
          (R := R) anchor K hc hmass hK (sigma t)
          (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
            partition coordinates block)
          (choice block) :=
    continuous_cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_comp
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hsigma hRweak hcap
      (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
        partition coordinates block)
      (choice block) hsmall
  unfold cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
  fun_prop

/-- The coefficient of one physical domain inside one ordered partition is
continuous along the contour. -/
theorem
    continuous_cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt_comp
    {M Q Nc R Δ n : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
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
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (sigma : T → FinBox 4 (2 * Q) → ℝ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (W : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ t d, ‖(sigma t d : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ n V₀) :
    Continuous fun t =>
      cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase (sigma t) L coordinates partition W := by
  classical
  unfold cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
  apply continuous_finset_sum
  intro choice _hchoice
  apply
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_comp
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      vertexBase sigma hsigma L coordinates partition choice
      hRweak hcap hsmall
  apply hV₀.of_le
  exact
    WithTop.coe_le_coe.mpr
      (ENat.coe_le_coe.mpr (OrderedFinpartition.length_le partition))

/-- The complete arbitrary-depth coefficient of one physical union label is
continuous along the contour. -/
theorem continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_comp
    {M Q Nc R Δ n : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
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
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (sigma : T → FinBox 4 (2 * Q) → ℝ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (W : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ t d, ‖(sigma t d : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ n V₀) :
    Continuous fun t =>
      cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase (sigma t) L coordinates W := by
  classical
  unfold cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
  apply continuous_finset_sum
  intro partition _hpartition
  exact
    continuous_cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt_comp
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      vertexBase sigma hsigma L coordinates partition W
      hRweak hcap hsmall hV₀

/-- In particular, every completed physical union-label coefficient is
Bochner integrable on every finite interval along such a contour. -/
theorem
    intervalIntegrable_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_comp
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
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
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (sigma : ℝ → FinBox 4 (2 * Q) → ℝ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (W : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ t d, ‖(sigma t d : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ n V₀)
    (a b : ℝ) :
    IntervalIntegrable
      (fun t =>
        cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase (sigma t) L coordinates W)
      MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_comp
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      vertexBase sigma hsigma L coordinates W
      hRweak hcap hsmall hV₀

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredLocalizationBound
import YangMills.RG.BalabanCMP116SourcePi4MixedDerivativeDomainSeries

/-!
# Complete equation-(80) coefficients anchored at the whole `Pi^4`

The volume-uniform terminal bound makes every fixed source-domain fiber
absolutely summable in walk length.  Passing the finite domain sum through
that limit yields an exact decomposition of the complete mixed covariance
derivative.  Every nonzero complete coefficient is indexed by a connected
domain containing the full literal `Pi^4` carrier.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Every fixed full-carrier source-domain fiber is absolutely summable in
walk length. -/
theorem
    summable_cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
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
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    Summable fun n : ℕ =>
      cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
        (R := R) (n := n) anchor K hc hmass hK sigma S row col Y := by
  have hmajor :
      Summable
        (cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
          Δ Ahead rho Rweak) :=
    (hasSum_cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
      Δ Ahead rho Rweak hsmall).summable
  apply Summable.of_norm_bounded hmajor
  intro n
  have hbound :=
    norm_cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_le
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hRweak hcap S Y n row col
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

/-- Complete equation-(80) covariance coefficient assigned to one literal
full-`Pi^4` source domain. -/
noncomputable def cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (Y : Finset (FinBox 4 (2 * Q))) : ℂ :=
  ∑' n : ℕ,
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
      (R := R) (n := n) anchor K hc hmass hK sigma S row col Y

/-- The completed full-carrier domain coefficient preserves the fixed
physical spatial decay of every walk layer.  The geometric series is summed
exactly, so the prefactor is uniform in the ambient volume and no
terminal-chart cardinality remains. -/
theorem norm_cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient_le
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
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ‖cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
        (R := R) anchor K hc hmass hK sigma S row col Y‖ ≤
      (cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
        (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹) *
        Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))) := by
  let layer := fun n : ℕ =>
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
      (R := R) (n := n) anchor K hc hmass hK sigma S row col Y
  let spatial : ℝ :=
    Real.exp (-(rate *
      (physicalBondDist row.1 col.1 : ℝ)))
  have hlayer : Summable layer :=
    summable_cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hRweak hcap S Y row col hsmall
  have hmajor :
      HasSum
        (fun n : ℕ =>
          cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
            Δ Ahead rho Rweak n * spatial)
        ((cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
          (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹) *
          spatial) :=
    (hasSum_cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
      Δ Ahead rho Rweak hsmall).mul_right spatial
  change ‖∑' n : ℕ, layer n‖ ≤ _
  calc
    ‖∑' n : ℕ, layer n‖ ≤ ∑' n : ℕ, ‖layer n‖ :=
      norm_tsum_le_tsum_norm hlayer.norm
    _ ≤ ∑' n : ℕ,
        cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
          Δ Ahead rho Rweak n * spatial := by
      exact Summable.tsum_le_tsum
        (fun n =>
          norm_cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_le
            anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
            sigma hRweak hcap S Y n row col)
        hlayer.norm hmajor.summable
    _ = (cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
          (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹) *
          spatial :=
      hmajor.tsum_eq

/-- Finite full-carrier source-domain coefficients converge to their complete
coefficients. -/
theorem tendsto_cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
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
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    Filter.Tendsto
      (fun N =>
        cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
          (R := R) anchor K hc hmass hK sigma S row col N Y)
      Filter.atTop
      (nhds
        (cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
          (R := R) anchor K hc hmass hK sigma S row col Y)) := by
  have hsum :=
    summable_cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hRweak hcap S Y row col hsmall
  simpa [cmp102Eq80SourcePi4CarrierAnchoredDomainPartial,
    cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient] using
    hsum.hasSum.tendsto_sum_nat

/-- The complete coefficient vanishes unless its domain contains the whole
literal `Pi^4` anchor carrier. -/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient_eq_zero_of_not_subset
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ Y) :
    cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
      (R := R) anchor K hc hmass hK sigma S row col Y = 0 := by
  simp [cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient,
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_eq_zero_of_not_subset
      anchor K hc hmass hK sigma S row col Y hanchor]

/-- The complete coefficient vanishes on every disconnected domain. -/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient_eq_zero_of_not_walkConnected
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y) :
    cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
      (R := R) anchor K hc hmass hK sigma S row col Y = 0 := by
  simp [cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient,
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_eq_zero_of_not_walkConnected
      anchor K hc hmass hK sigma S row col Y hconnected]

/-- The complete physical mixed covariance derivative is exactly the finite
sum of its complete source-correct full-carrier domain coefficients. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative_eq_sum_pi4CarrierAnchoredDomainCoefficient
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
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
    (S : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
        (R := R) anchor K hc hmass hK sigma S row col =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
          (R := R) anchor K hc hmass hK sigma S row col Y := by
  have hcollect :=
    tendsto_cmp116SourcePi4MixedDerivativePartial
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma S hRweak hsigma hcap hsmall row col
  have hindividual :
      Filter.Tendsto
        (fun N =>
          ∑ Y : Finset (FinBox 4 (2 * Q)),
            cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
              (R := R) anchor K hc hmass hK sigma S row col N Y)
        Filter.atTop
        (nhds
          (∑ Y : Finset (FinBox 4 (2 * Q)),
            cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
              (R := R) anchor K hc hmass hK sigma S row col Y)) := by
    refine tendsto_finset_sum Finset.univ (fun Y _hY => ?_)
    exact
      tendsto_cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
        anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
        sigma hRweak hcap S Y row col hsmall
  have hfinite :
      (fun N =>
        cmp116SourcePi4MixedDerivativePartial
          (R := R) anchor K hc hmass hK sigma S row col N) =
      (fun N =>
        ∑ Y : Finset (FinBox 4 (2 * Q)),
          cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
            (R := R) anchor K hc hmass hK sigma S row col N Y) := by
    funext N
    exact
      cmp116SourcePi4MixedDerivativePartial_eq_sum_pi4CarrierAnchoredPartial
        anchor K hc hmass hK sigma S row col N
  have hcollect' :
      Filter.Tendsto
        (fun N =>
          ∑ Y : Finset (FinBox 4 (2 * Q)),
            cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
              (R := R) anchor K hc hmass hK sigma S row col N Y)
        Filter.atTop
        (nhds
          (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
            (R := R) anchor K hc hmass hK sigma S row col)) := by
    rw [← hfinite]
    exact hcollect
  exact tendsto_nhds_unique hcollect' hindividual

end

end YangMills.RG

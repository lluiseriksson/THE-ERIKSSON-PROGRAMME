/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4TerminalMixedDerivativeDomainBound
import YangMills.RG.BalabanCMP116SourcePi4FullComplexContourDefect

/-!
# Complete mixed connected-domain derivative coefficients

The terminal-domain estimate is a genuine geometric majorant in walk length.
It therefore defines a complete coefficient for each fixed canonical
connected domain.  Since the ambient weakening lattice is finite, the
finite-domain sum may then be passed through the length limit, identifying
the complete physical mixed derivative with the sum of its individually
convergent connected coefficients.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Length-zero prefactor for a fixed mixed connected-domain series. -/
noncomputable def cmp116SourcePi4MixedDerivativeDomainPrefactor
    (Ahead Rweak : ℝ) : ℝ :=
  Rweak ^ 10000 * Ahead

/-- The mixed connected-domain layer amplitude is an exact geometric term
with the same physical contour ratio as the complete covariance series. -/
theorem cmp116SourcePi4MixedDerivativeDomainLayerAmplitude_eq_prefactor_mul
    (Δ : ℕ) (Ahead rho Rweak : ℝ) (n : ℕ) :
    cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
        Δ Ahead rho Rweak n =
      cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
        cmp116SourcePi4ComplexContourRatio Δ rho Rweak ^ n := by
  unfold cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
    cmp116SourcePi4MixedDerivativeDomainPrefactor
    cmp116SourcePi4ComplexContourRatio
  rw [Nat.cast_pow]
  rw [show 10000 * (n + 1) = 10000 + 10000 * n by omega]
  rw [pow_add, pow_mul, mul_pow, mul_pow]
  ring

/-- Exact scalar sum of the mixed connected-domain layer majorants. -/
theorem hasSum_cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
    (Δ : ℕ) (Ahead rho Rweak : ℝ)
    (hsmall : ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    HasSum
      (cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
        Δ Ahead rho Rweak)
      (cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
        (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹) := by
  have hgeom :=
    hasSum_geometric_of_norm_lt_one hsmall
  convert hgeom.mul_left
    (cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak) using 1
  ext n
  exact
    cmp116SourcePi4MixedDerivativeDomainLayerAmplitude_eq_prefactor_mul
      Δ Ahead rho Rweak n

/-- Every fixed physical connected-domain coefficient is absolutely
summable in walk length. -/
theorem summable_cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
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
    (root : FinBox 4 (2 * Q))
    (Y : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    Summable fun n : ℕ =>
      cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
        (R := R) (n := n) anchor K hc hmass hK
        sigma S root row col Y := by
  have hmajor :
      Summable
        (cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
          Δ Ahead rho Rweak) :=
    (hasSum_cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
      Δ Ahead rho Rweak hsmall).summable
  apply Summable.of_norm_bounded hmajor
  intro n
  have hbound :=
    norm_cmp116SourcePi4MixedDerivativeDomainLayerCoefficient_le'
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hRweak hcap S root Y n row col
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

/-- Complete physical coefficient assigned to one canonical connected
weakening domain. -/
noncomputable def cmp116SourcePi4MixedDerivativeDomainCoefficient
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (Y : Finset (FinBox 4 (2 * Q))) : ℂ :=
  ∑' n : ℕ,
    cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
      (R := R) (n := n) anchor K hc hmass hK
      sigma S root row col Y

/-- The finite length partial coefficient converges to the complete
coefficient of each fixed connected domain. -/
theorem tendsto_cmp116SourcePi4MixedDerivativeDomainPartial
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
    (root : FinBox 4 (2 * Q))
    (Y : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    Filter.Tendsto
      (fun N =>
        cmp116SourcePi4MixedDerivativeDomainPartial
          (R := R) anchor K hc hmass hK sigma S root row col N Y)
      Filter.atTop
      (nhds
        (cmp116SourcePi4MixedDerivativeDomainCoefficient
          (R := R) anchor K hc hmass hK sigma S root row col Y)) := by
  have hsum :=
    summable_cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hRweak hcap S root Y row col hsmall
  simpa [cmp116SourcePi4MixedDerivativeDomainPartial,
    cmp116SourcePi4MixedDerivativeDomainCoefficient] using
    hsum.hasSum.tendsto_sum_nat

/-- The complete physical mixed covariance derivative is exactly the finite
sum of its individually convergent canonical connected-domain coefficients. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative_eq_sum_domainCoefficient
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
    (root : FinBox 4 (2 * Q)) (hroot : root ∈ S)
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
        cmp116SourcePi4MixedDerivativeDomainCoefficient
          (R := R) anchor K hc hmass hK sigma S root row col Y := by
  have hcollect :=
    tendsto_sum_cmp116SourcePi4MixedDerivativeDomainPartial
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma S root hroot hRweak hsigma hcap hsmall row col
  have hindividual :
      Filter.Tendsto
        (fun N =>
          ∑ Y : Finset (FinBox 4 (2 * Q)),
            cmp116SourcePi4MixedDerivativeDomainPartial
              (R := R) anchor K hc hmass hK sigma S root row col N Y)
        Filter.atTop
        (nhds
          (∑ Y : Finset (FinBox 4 (2 * Q)),
            cmp116SourcePi4MixedDerivativeDomainCoefficient
              (R := R) anchor K hc hmass hK sigma S root row col Y)) := by
    refine tendsto_finset_sum Finset.univ (fun Y _hY => ?_)
    exact
      tendsto_cmp116SourcePi4MixedDerivativeDomainPartial
        anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
        sigma hRweak hcap S root Y row col hsmall
  exact tendsto_nhds_unique hcollect hindividual

end

end YangMills.RG

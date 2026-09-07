/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4MixedDerivativeLayerLocalization
import YangMills.RG.BalabanCMP116SourcePi4MixedWeakenedCovarianceDerivativeSeries

/-!
# Finite mixed-derivative localization and its physical limit

Localization is first performed at a finite walk-length cutoff.  The finite
sums can be rearranged without any hidden convergence assumption.  The total
sum over all connected domains is then proved to converge to the complete
physical mixed covariance derivative using the already established physical
contour majorant.

This module deliberately does not yet exchange the infinite length sum with
each individual domain fiber.  That stronger statement requires an absolute
source bound for every fiber and remains visible.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The literal connected-domain coefficient of one mixed derivative layer. -/
noncomputable def cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
    {M Q Nc R n : ℕ}
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
  cmp116AnchoredFiberCoefficient
    (cmp116CoarseFaceAdj 4 (2 * Q))
    (Finset.univ :
      Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
    (fun _ => root)
    (cmp116SourcePi4LayerWalkActive anchor)
    (cmp116SourcePi4MixedDerivativeLayerWalkTerm
      anchor K hc hmass hK sigma S row col) Y

/-- One finite walk-length truncation of the complete mixed derivative. -/
noncomputable def cmp116SourcePi4MixedDerivativePartial
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
    (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
      (R := R) anchor K hc hmass hK sigma S n row col

/-- The corresponding finite-cutoff coefficient of one connected domain. -/
noncomputable def cmp116SourcePi4MixedDerivativeDomainPartial
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
    (N : ℕ) (Y : Finset (FinBox 4 (2 * Q))) : ℂ :=
  ∑ n ∈ Finset.range N,
    cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
      (R := R) (n := n) anchor K hc hmass hK sigma S root row col Y

/-- At every finite cutoff, the physical mixed derivative is exactly the sum
of its canonical connected-domain coefficients. -/
theorem cmp116SourcePi4MixedDerivativePartial_eq_sum_domainPartial
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q)) (hroot : root ∈ S)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (N : ℕ) :
    cmp116SourcePi4MixedDerivativePartial
        (R := R) anchor K hc hmass hK sigma S row col N =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp116SourcePi4MixedDerivativeDomainPartial
          (R := R) anchor K hc hmass hK sigma S root row col N Y := by
  classical
  unfold cmp116SourcePi4MixedDerivativePartial
    cmp116SourcePi4MixedDerivativeDomainPartial
  calc
    (∑ n ∈ Finset.range N,
      cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma S n row col) =
        ∑ n ∈ Finset.range N,
          ∑ Y : Finset (FinBox 4 (2 * Q)),
            cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
              (R := R) (n := n) anchor K hc hmass hK
              sigma S root row col Y := by
      apply Finset.sum_congr rfl
      intro n hn
      exact
        cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_eq_sum_univ_anchoredFiber
          anchor K hc hmass hK sigma S root hroot row col
    _ = ∑ Y : Finset (FinBox 4 (2 * Q)),
          ∑ n ∈ Finset.range N,
            cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
              (R := R) (n := n) anchor K hc hmass hK
              sigma S root row col Y := by
      rw [Finset.sum_comm]

/-- The physical contour estimate makes the finite mixed-derivative
truncations converge to the complete length-ordered derivative. -/
theorem tendsto_cmp116SourcePi4MixedDerivativePartial
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
    Filter.Tendsto
      (cmp116SourcePi4MixedDerivativePartial
        (R := R) anchor K hc hmass hK sigma S row col)
      Filter.atTop
      (nhds
        (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
          (R := R) anchor K hc hmass hK sigma S row col)) := by
  have hmatrix :=
    summable_norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma S hRweak hsigma hcap hsmall
  have hnorm : Summable fun n : ℕ =>
      ‖cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma S n row col‖ := by
    apply Summable.of_nonneg_of_le
      (fun n => norm_nonneg
        (cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
          (R := R) anchor K hc hmass hK sigma S n row col))
      (fun n =>
        norm_matrix_entry_le_linfty_opNorm
          (cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
            (R := R) anchor K hc hmass hK sigma S n) row col)
    exact hmatrix
  have hsum : Summable fun n : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma S n row col :=
    Summable.of_norm hnorm
  simpa [cmp116SourcePi4MixedDerivativePartial,
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative] using
    hsum.hasSum.tendsto_sum_nat

/-- Consequently, the finite sum of physical connected-domain coefficients
converges collectively to the complete mixed covariance derivative. -/
theorem tendsto_sum_cmp116SourcePi4MixedDerivativeDomainPartial
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
    Filter.Tendsto
      (fun N =>
        ∑ Y : Finset (FinBox 4 (2 * Q)),
          cmp116SourcePi4MixedDerivativeDomainPartial
            (R := R) anchor K hc hmass hK sigma S root row col N Y)
      Filter.atTop
      (nhds
        (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
          (R := R) anchor K hc hmass hK sigma S row col)) := by
  apply
    (tendsto_cmp116SourcePi4MixedDerivativePartial
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma S hRweak hsigma hcap hsmall row col).congr'
  filter_upwards with N
  exact
    (cmp116SourcePi4MixedDerivativePartial_eq_sum_domainPartial
      anchor K hc hmass hK sigma S root hroot row col N)

end

end YangMills.RG

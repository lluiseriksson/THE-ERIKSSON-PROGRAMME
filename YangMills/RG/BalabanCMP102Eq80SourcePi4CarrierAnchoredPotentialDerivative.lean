/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredLocalizationSeries
import YangMills.RG.BalabanCMP102Eq80PropagatorDerivative
import YangMills.RG.BalabanCMP116SourcePi4RealMixedWeakenedCovariance

/-!
# Equation-(80) directional derivative localized at the physical `Pi^4`

The complete source-domain matrices are reconstructed as real physical
endomorphisms.  Their finite sum is exactly the real mixed covariance
operator.  Since the literal derivative of all four terms in equation (80)
is linear in its propagator direction, the complete directional derivative
is the exact sum of the corresponding source-domain derivatives.

This is a first-derivative localization theorem for the complete literal
equation-(80) functional.  It is not yet the arbitrary-depth FTC activity and
does not identify the covariance contribution alone with `V_k(Y, B)`.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Matrix of one complete full-`Pi^4` source-domain coefficient. -/
noncomputable def cmp102Eq80SourcePi4CarrierAnchoredDomainMatrix
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q))) :
    Matrix (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  fun row col =>
    cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
      (R := R) anchor K hc hmass hK (fun x => (s x : ℂ))
      S row col Y

/-- Real physical operator reconstructed from one source-domain matrix. -/
noncomputable def cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q))) :
    PhysicalEndomorphism M Q Nc :=
  cmp116PhysicalEndomorphismOfComplexMatrixCLM
    (cmp102Eq80SourcePi4CarrierAnchoredDomainMatrix
      (R := R) anchor K hc hmass hK s S Y)

/-- Reconstructing and summing all full-carrier source-domain matrices gives
the complete real mixed covariance operator. -/
theorem
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
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
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
        (R := R) anchor K hc hmass hK s S =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
          (R := R) anchor K hc hmass hK s S Y := by
  have hmatrix :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
          (R := R) anchor K hc hmass hK (fun x => (s x : ℂ)) S =
        ∑ Y : Finset (FinBox 4 (2 * Q)),
          cmp102Eq80SourcePi4CarrierAnchoredDomainMatrix
            (R := R) anchor K hc hmass hK s S Y := by
    ext row col
    rw [Matrix.sum_apply]
    change
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
          (R := R) anchor K hc hmass hK (fun x => (s x : ℂ)) S row col =
        ∑ Y : Finset (FinBox 4 (2 * Q)),
          cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient
            (R := R) anchor K hc hmass hK (fun x => (s x : ℂ))
            S row col Y
    exact
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative_eq_sum_pi4CarrierAnchoredDomainCoefficient
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 (fun x => (s x : ℂ)) S hRweak hs hcap hsmall row col
  unfold cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
  rw [hmatrix, map_sum]

/-- The literal equation-(80) propagator derivative is additive in its
direction. -/
theorem cmp102Eq80PropagatorDirectionalDerivative_add
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (H K₁ K₂ : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J A : E)
    (V₀' : E →L[ℝ] ℝ) :
    cmp102Eq80PropagatorDirectionalDerivative
        D D₃ H (K₁ + K₂) Δπ J A V₀' =
      cmp102Eq80PropagatorDirectionalDerivative
          D D₃ H K₁ Δπ J A V₀' +
        cmp102Eq80PropagatorDirectionalDerivative
          D D₃ H K₂ Δπ J A V₀' := by
  simp only [cmp102Eq80PropagatorDirectionalDerivative,
    ContinuousLinearMap.add_apply, map_add, inner_add_left, inner_add_right]
  ring

/-- The literal equation-(80) propagator derivative vanishes in the zero
direction. -/
theorem cmp102Eq80PropagatorDirectionalDerivative_zero
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (H : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J A : E)
    (V₀' : E →L[ℝ] ℝ) :
    cmp102Eq80PropagatorDirectionalDerivative
        D D₃ H (0 : F →L[ℝ] E) Δπ J A V₀' = 0 := by
  simp [cmp102Eq80PropagatorDirectionalDerivative]

/-- Finite additivity in the propagator direction. -/
theorem cmp102Eq80PropagatorDirectionalDerivative_sum
    {E F ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [DecidableEq ι]
    (D D₃ : E → F)
    (H : F →L[ℝ] E) (Kdir : ι → F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (J A : E)
    (V₀' : E →L[ℝ] ℝ) (T : Finset ι) :
    cmp102Eq80PropagatorDirectionalDerivative
        D D₃ H (∑ i ∈ T, Kdir i) Δπ J A V₀' =
      ∑ i ∈ T,
        cmp102Eq80PropagatorDirectionalDerivative
          D D₃ H (Kdir i) Δπ J A V₀' := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simp [cmp102Eq80PropagatorDirectionalDerivative_zero]
  | @insert i T hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        cmp102Eq80PropagatorDirectionalDerivative_add, ih]

/-- The first literal equation-(80) mixed propagator derivative is exactly
the sum of its source-correct full-`Pi^4` domain derivatives. -/
theorem
    cmp102Eq80PropagatorDirectionalDerivative_fullRealMixed_eq_sum_pi4CarrierAnchoredDomains
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
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (H : PhysicalEndomorphism M Q Nc)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ) :
    cmp102Eq80PropagatorDirectionalDerivative D D₃ H
        (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK s S)
        Δπ J A V₀' =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80PropagatorDirectionalDerivative D D₃ H
          (cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
            (R := R) anchor K hc hmass hK s S Y)
          Δπ J A V₀' := by
  rw [
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 s S hRweak hs hcap hsmall]
  exact
    cmp102Eq80PropagatorDirectionalDerivative_sum
      D D₃ H
      (cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
        (R := R) anchor K hc hmass hK s S)
      Δπ J A V₀' Finset.univ

end

end YangMills.RG

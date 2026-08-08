/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondMixedDerivativeValue

/-!
# Complete source localization at the second equation-(80) FTC node

The literal second mixed derivative consists of three source families:

1. the first equation-(80) directional expression in the next mixed
   propagator `H_de`;
2. the quadratic cross term between `H_e` and `H_d`;
3. the Hessian of `V₀` applied to `H_e (D A)` and `H_d (D A)`.

All three families have already been decomposed from their physical
propagators.  This file combines them into a single coefficient indexed by a
large-block domain.  Unsupported or disconnected labels vanish term by
term, so the resulting coefficient has the exact source support required by
the repeated FTC expansion.
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

/-- One complete second-node coefficient on a physical source domain. -/
noncomputable def cmp102Eq80SourcePi4SecondMixedDomainCoefficient
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (Kbase : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM Kbase c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (Sde Se Sd : Finset (FinBox 4 (2 * Q)))
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (H Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (W : Finset (FinBox 4 (2 * Q))) : ℝ :=
  cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative
      (R := R) anchor Kbase hc hmass hK s Sde W
      D D₃ H Δπ J A V₀'
    + cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient
      (R := R) anchor Kbase hc hmass hK s Se Sd Δπ (D A) W
    + cmp102Eq80SourcePi4V0BilinearDomainCoefficient
      (R := R) anchor Kbase hc hmass hK s Se Sd V₀'' (D A) W

/-- Every complete second-node coefficient contains the whole literal
`Pi^4` source carrier. -/
theorem
    cmp102Eq80SourcePi4SecondMixedDomainCoefficient_eq_zero_of_not_subset
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (Kbase : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM Kbase c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (Sde Se Sd : Finset (FinBox 4 (2 * Q)))
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (H Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (W : Finset (FinBox 4 (2 * Q)))
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ W) :
    cmp102Eq80SourcePi4SecondMixedDomainCoefficient
      (R := R) anchor Kbase hc hmass hK s Sde Se Sd
      D D₃ H Δπ J A V₀' V₀'' W = 0 := by
  unfold cmp102Eq80SourcePi4SecondMixedDomainCoefficient
  rw [
    cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative_eq_zero_of_not_subset
      anchor Kbase hc hmass hK s Sde W D D₃ H Δπ J A V₀' hanchor,
    cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient_eq_zero_of_not_subset
      anchor Kbase hc hmass hK s Se Sd Δπ (D A) W hanchor,
    cmp102Eq80SourcePi4V0BilinearDomainCoefficient_eq_zero_of_not_subset
      anchor Kbase hc hmass hK s Se Sd V₀'' (D A) W hanchor]
  simp

/-- Every complete second-node coefficient is supported on a face-connected
source domain. -/
theorem
    cmp102Eq80SourcePi4SecondMixedDomainCoefficient_eq_zero_of_not_walkConnected
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (Kbase : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM Kbase c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (Sde Se Sd : Finset (FinBox 4 (2 * Q)))
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (H Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (W : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) W) :
    cmp102Eq80SourcePi4SecondMixedDomainCoefficient
      (R := R) anchor Kbase hc hmass hK s Sde Se Sd
      D D₃ H Δπ J A V₀' V₀'' W = 0 := by
  unfold cmp102Eq80SourcePi4SecondMixedDomainCoefficient
  rw [
    cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative_eq_zero_of_not_walkConnected
      anchor Kbase hc hmass hK s Sde W D D₃ H Δπ J A V₀' hconnected,
    cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient_eq_zero_of_not_walkConnected
      anchor Kbase hc hmass hK s Se Sd Δπ (D A) W hconnected,
    cmp102Eq80SourcePi4V0BilinearDomainCoefficient_eq_zero_of_not_walkConnected
      anchor Kbase hc hmass hK s Se Sd V₀'' (D A) W hconnected]
  simp

/-- Exact finite source decomposition of the complete literal second mixed
equation-(80) derivative. -/
theorem
    cmp102Eq80SecondPropagatorMixedDerivative_fullRealMixed_eq_sum_pi4Domains
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (Kbase : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM Kbase c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      Kbase cmp99SourcePi4ChartEnlarged
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
    (Sde Se Sd : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (H Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ) :
    cmp102Eq80SecondPropagatorMixedDerivative D D₃ H
        (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor Kbase hc hmass hK s Sd)
        (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor Kbase hc hmass hK s Se)
        (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor Kbase hc hmass hK s Sde)
        Δπ J A V₀' V₀'' =
      ∑ W : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4SecondMixedDomainCoefficient
          (R := R) anchor Kbase hc hmass hK s Sde Se Sd
          D D₃ H Δπ J A V₀' V₀'' W := by
  unfold cmp102Eq80SecondPropagatorMixedDerivative
  rw [
    cmp102Eq80PropagatorDirectionalDerivative_fullRealMixed_eq_sum_pi4CarrierAnchoredDomains
      anchor Kbase hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 s Sde hRweak hs hcap hsmall
      D D₃ H Δπ J A V₀',
    cmp102Eq80QuadraticMixedPairTerm_fullRealMixed_eq_sum_pi4Domains
      anchor Kbase hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 s Se Sd hRweak hs hcap hsmall Δπ (D A)]
  have hV0pair :
      V₀''
          (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor Kbase hc hmass hK s Se (D A))
          (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor Kbase hc hmass hK s Sd (D A)) =
        ∑ W : Finset (FinBox 4 (2 * Q)),
          cmp102Eq80SourcePi4V0BilinearDomainCoefficient
            (R := R) anchor Kbase hc hmass hK s Se Sd V₀'' (D A) W := by
    rw [
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
        anchor Kbase hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 s Se hRweak hs hcap hsmall,
      cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
        anchor Kbase hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 s Sd hRweak hs hcap hsmall,
      cmp102Eq80V0BilinearTerm_sum_sum,
      sum_cmp102Eq80SourcePi4AnchoredPairFiber]
    rfl
  rw [hV0pair, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  rfl

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredLocalization
import YangMills.RG.BalabanCMP116SourcePi4MixedDerivativeLocalizationPartial

/-!
# Finite physical localization anchored at the whole source `Pi^4`

At every finite walk-length cutoff, this file packages the equation-(80)
covariance contribution by the canonical component meeting the complete
literal `Pi^4` carrier.  This removes the earlier artificial choice of a
single differentiated coordinate.

Every nonzero coefficient is indexed by a face-connected domain containing
all of `Pi^4`.  The decomposition is finite and exact; no convergence or
decay assumption is used here.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- One mixed covariance layer coefficient indexed by the physical
`Pi^4`-anchored source domain. -/
noncomputable def
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
    {M Q Nc R n : ℕ}
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
  cmp116CarrierAnchoredFiberCoefficient
    (cmp116CoarseFaceAdj 4 (2 * Q))
    (Finset.univ :
      Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
    (cmp102Eq80SourcePi4AnchorCarrier anchor)
    (cmp116SourcePi4LayerWalkActive anchor)
    (cmp116SourcePi4MixedDerivativeLayerWalkTerm
      anchor K hc hmass hK sigma S row col) Y

/-- Finite walk-length partial coefficient of one physical source domain. -/
noncomputable def
    cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
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
    (N : ℕ) (Y : Finset (FinBox 4 (2 * Q))) : ℂ :=
  ∑ n ∈ Finset.range N,
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
      (R := R) (n := n) anchor K hc hmass hK sigma S row col Y

/-- At every finite cutoff, the literal physical mixed derivative is exactly
the sum of its `Pi^4`-anchored source-domain coefficients. -/
theorem cmp116SourcePi4MixedDerivativePartial_eq_sum_pi4CarrierAnchoredPartial
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
    (N : ℕ) :
    cmp116SourcePi4MixedDerivativePartial
        (R := R) anchor K hc hmass hK sigma S row col N =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
          (R := R) anchor K hc hmass hK sigma S row col N Y := by
  classical
  unfold cmp116SourcePi4MixedDerivativePartial
    cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
  calc
    (∑ n ∈ Finset.range N,
      cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma S n row col) =
        ∑ n ∈ Finset.range N,
          ∑ Y : Finset (FinBox 4 (2 * Q)),
            cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
              (R := R) (n := n) anchor K hc hmass hK
              sigma S row col Y := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact
        cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_eq_sum_univ_pi4CarrierAnchoredFiber
          anchor K hc hmass hK sigma S row col
    _ = ∑ Y : Finset (FinBox 4 (2 * Q)),
          ∑ n ∈ Finset.range N,
            cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
              (R := R) (n := n) anchor K hc hmass hK
              sigma S row col Y := by
      rw [Finset.sum_comm]

/-- A layer fiber vanishes if its claimed source domain omits any part of the
distinguished physical `Pi^4` carrier. -/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_eq_zero_of_not_subset
    {M Q Nc R n : ℕ}
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
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
      (R := R) (n := n) anchor K hc hmass hK sigma S row col Y = 0 := by
  classical
  unfold cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
    cmp116CarrierAnchoredFiberCoefficient
  apply Finset.sum_eq_zero
  intro idx hidx
  have hfiber := (Finset.mem_filter.mp hidx).2
  have hsub :=
    cmp116Carrier_subset_carrierAnchoredLocalizationDomain
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4AnchorCarrier anchor)
      (cmp116SourcePi4LayerWalkActive anchor) idx
  exact (hanchor (hfiber ▸ hsub)).elim

/-- A layer fiber vanishes if its claimed source domain is not face-connected.
-/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_eq_zero_of_not_walkConnected
    {M Q Nc R n : ℕ}
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
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
      (R := R) (n := n) anchor K hc hmass hK sigma S row col Y = 0 := by
  classical
  unfold cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient
    cmp116CarrierAnchoredFiberCoefficient
  apply Finset.sum_eq_zero
  intro idx hidx
  have hfiber := (Finset.mem_filter.mp hidx).2
  have hwalk :=
    walkConnected_cmp102Eq80SourcePi4WalkLocalizationDomain anchor idx
  exact (hconnected (hfiber ▸ hwalk)).elim

/-- The finite partial coefficient inherits the exact full-carrier support. -/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainPartial_eq_zero_of_not_subset
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
    (N : ℕ) (Y : Finset (FinBox 4 (2 * Q)))
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ Y) :
    cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
      (R := R) anchor K hc hmass hK sigma S row col N Y = 0 := by
  simp only [cmp102Eq80SourcePi4CarrierAnchoredDomainPartial,
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_eq_zero_of_not_subset
      anchor K hc hmass hK sigma S row col Y hanchor,
    Finset.sum_const_zero]

/-- The finite partial coefficient also vanishes off connected domains. -/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainPartial_eq_zero_of_not_walkConnected
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
    (N : ℕ) (Y : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y) :
    cmp102Eq80SourcePi4CarrierAnchoredDomainPartial
      (R := R) anchor K hc hmass hK sigma S row col N Y = 0 := by
  simp only [cmp102Eq80SourcePi4CarrierAnchoredDomainPartial,
    cmp102Eq80SourcePi4CarrierAnchoredDomainLayerCoefficient_eq_zero_of_not_walkConnected
      anchor K hc hmass hK sigma S row col Y hconnected,
    Finset.sum_const_zero]

end

end YangMills.RG

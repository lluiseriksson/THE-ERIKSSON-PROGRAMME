/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredPotentialDerivative

/-!
# Physical support of localized equation-(80) derivatives

The source-domain support proved entrywise survives reconstruction to the
physical operator and then the literal four-term equation-(80) directional
derivative.  Thus disconnected labels, or labels omitting any part of the
distinguished `Pi^4`, contribute definitionally zero.
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

/-- One literal equation-(80) directional-derivative contribution indexed by
a full-carrier physical source domain. -/
noncomputable def cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (H Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ) : ℝ :=
  cmp102Eq80PropagatorDirectionalDerivative D D₃ H
    (cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
      (R := R) anchor K hc hmass hK s S Y)
    Δπ J A V₀'

/-- The reconstructed source-domain matrix vanishes when its label omits
part of the literal `Pi^4` carrier. -/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainMatrix_eq_zero_of_not_subset
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ Y) :
    cmp102Eq80SourcePi4CarrierAnchoredDomainMatrix
      (R := R) anchor K hc hmass hK s S Y = 0 := by
  funext row col
  exact
    cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient_eq_zero_of_not_subset
      anchor K hc hmass hK (fun x => (s x : ℂ)) S row col Y hanchor

/-- The reconstructed source-domain matrix vanishes on disconnected labels.
-/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainMatrix_eq_zero_of_not_walkConnected
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y) :
    cmp102Eq80SourcePi4CarrierAnchoredDomainMatrix
      (R := R) anchor K hc hmass hK s S Y = 0 := by
  funext row col
  exact
    cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient_eq_zero_of_not_walkConnected
      anchor K hc hmass hK (fun x => (s x : ℂ)) S row col Y hconnected

/-- Physical reconstruction preserves the full-carrier support condition. -/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_subset
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ Y) :
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
      (R := R) anchor K hc hmass hK s S Y = 0 := by
  unfold cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
  rw [
    cmp102Eq80SourcePi4CarrierAnchoredDomainMatrix_eq_zero_of_not_subset
      anchor K hc hmass hK s S Y hanchor, map_zero]

/-- Physical reconstruction also preserves connected-domain support. -/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_walkConnected
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y) :
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
      (R := R) anchor K hc hmass hK s S Y = 0 := by
  unfold cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
  rw [
    cmp102Eq80SourcePi4CarrierAnchoredDomainMatrix_eq_zero_of_not_walkConnected
      anchor K hc hmass hK s S Y hconnected, map_zero]

/-- The literal equation-(80) contribution is zero if the domain omits any
part of `Pi^4`. -/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative_eq_zero_of_not_subset
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (H Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ Y) :
    cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative
      (R := R) anchor K hc hmass hK s S Y D D₃ H Δπ J A V₀' = 0 := by
  unfold cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative
  rw [
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_subset
      anchor K hc hmass hK s S Y hanchor,
    cmp102Eq80PropagatorDirectionalDerivative_zero]

/-- The literal equation-(80) contribution is zero on disconnected labels.
-/
theorem
    cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative_eq_zero_of_not_walkConnected
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (H Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y) :
    cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative
      (R := R) anchor K hc hmass hK s S Y D D₃ H Δπ J A V₀' = 0 := by
  unfold cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative
  rw [
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_walkConnected
      anchor K hc hmass hK s S Y hconnected,
    cmp102Eq80PropagatorDirectionalDerivative_zero]

end

end YangMills.RG

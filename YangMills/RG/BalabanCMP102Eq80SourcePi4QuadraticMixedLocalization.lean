/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4AnchoredDomainUnion
import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredPotentialDerivativeSupport

/-!
# Source localization of the quadratic mixed term in equation (80)

At depth two of the source weakening FTC expansion, differentiating

`(1 / 2) * inner (H (D A)) (DeltaPi (H (D A)))`

produces a bilinear cross term between two differentiated propagators.  Each
propagator already has an exact finite decomposition by a connected physical
source domain containing the literal `Pi^4` carrier.

This file expands the bilinear term exactly and regroups every pair
`(Y₁, Y₂)` by the physical source label `Pi^4 ∪ Y₁ ∪ Y₂`.  It therefore
closes the quadratic-product localization needed at the second FTC node.  It
does not yet differentiate the nonlinear `V₀` term.
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

/-- The symmetric bilinear cross term obtained from the quadratic part of
equation (80). -/
noncomputable def cmp102Eq80QuadraticMixedPairTerm
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K₁ K₂ : F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (v : F) : ℝ :=
  (1 / 2 : ℝ) *
    (inner ℝ (K₁ v) (Δπ (K₂ v)) +
      inner ℝ (K₂ v) (Δπ (K₁ v)))

@[simp] theorem cmp102Eq80QuadraticMixedPairTerm_zero_left
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (v : F) :
    cmp102Eq80QuadraticMixedPairTerm
      (0 : F →L[ℝ] E) K Δπ v = 0 := by
  simp [cmp102Eq80QuadraticMixedPairTerm]

@[simp] theorem cmp102Eq80QuadraticMixedPairTerm_zero_right
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (v : F) :
    cmp102Eq80QuadraticMixedPairTerm
      K (0 : F →L[ℝ] E) Δπ v = 0 := by
  simp [cmp102Eq80QuadraticMixedPairTerm]

/-- Bilinearity expands two finite operator sums into the exact sum over
ordered pairs. -/
theorem cmp102Eq80QuadraticMixedPairTerm_sum_sum
    {E F ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype ι] [Fintype κ]
    (K₁ : ι → F →L[ℝ] E) (K₂ : κ → F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (v : F) :
    cmp102Eq80QuadraticMixedPairTerm
        (∑ i, K₁ i) (∑ j, K₂ j) Δπ v =
      ∑ p : ι × κ,
        cmp102Eq80QuadraticMixedPairTerm
          (K₁ p.1) (K₂ p.2) Δπ v := by
  classical
  have hfirst :
      inner ℝ ((∑ i, K₁ i) v) (Δπ ((∑ j, K₂ j) v)) =
        ∑ i, ∑ j,
          inner ℝ ((K₁ i) v) (Δπ ((K₂ j) v)) := by
    simp only [ContinuousLinearMap.sum_apply, map_sum, sum_inner,
      inner_sum]
    exact Finset.sum_comm
  have hsecond :
      inner ℝ ((∑ j, K₂ j) v) (Δπ ((∑ i, K₁ i) v)) =
        ∑ i, ∑ j,
          inner ℝ ((K₂ j) v) (Δπ ((K₁ i) v)) := by
    simp only [ContinuousLinearMap.sum_apply, map_sum, sum_inner,
      inner_sum]
  rw [cmp102Eq80QuadraticMixedPairTerm, hfirst, hsecond,
    Fintype.sum_prod_type]
  rw [mul_add]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [cmp102Eq80QuadraticMixedPairTerm, mul_add]

/-- One ordered pair of physical source-domain propagators inserted into the
quadratic mixed term. -/
noncomputable def cmp102Eq80SourcePi4DomainQuadraticMixedPairTerm
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S₁ S₂ : Finset (FinBox 4 (2 * Q)))
    (Δπ : PhysicalEndomorphism M Q Nc)
    (v : PhysicalField M Q Nc)
    (YZ : Finset (FinBox 4 (2 * Q)) ×
      Finset (FinBox 4 (2 * Q))) : ℝ :=
  cmp102Eq80QuadraticMixedPairTerm
    (cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
      (R := R) anchor K hc hmass hK s S₁ YZ.1)
    (cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
      (R := R) anchor K hc hmass hK s S₂ YZ.2)
    Δπ v

/-- Coefficient of one physical union label in the quadratic mixed term. -/
noncomputable def cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S₁ S₂ : Finset (FinBox 4 (2 * Q)))
    (Δπ : PhysicalEndomorphism M Q Nc)
    (v : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q))) : ℝ :=
  cmp102Eq80SourcePi4AnchoredPairFiber anchor
    (cmp102Eq80SourcePi4DomainQuadraticMixedPairTerm
      (R := R) anchor K hc hmass hK s S₁ S₂ Δπ v) W

/-- The paired quadratic coefficient vanishes when its claimed label omits
any part of the literal `Pi^4` carrier. -/
theorem
    cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient_eq_zero_of_not_subset
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S₁ S₂ : Finset (FinBox 4 (2 * Q)))
    (Δπ : PhysicalEndomorphism M Q Nc)
    (v : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q)))
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ W) :
    cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient
      (R := R) anchor K hc hmass hK s S₁ S₂ Δπ v W = 0 := by
  classical
  unfold cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient
    cmp102Eq80SourcePi4AnchoredPairFiber
  apply Finset.sum_eq_zero
  intro YZ hYZ
  have hlabel :
      cmp102Eq80SourcePi4AnchoredPairDomain anchor YZ = W := by
    simpa using (Finset.mem_filter.mp hYZ).2
  exfalso
  apply hanchor
  intro x hx
  rw [← hlabel]
  exact
    cmp102Eq80SourcePi4AnchorCarrier_subset_anchoredPairDomain
      anchor YZ hx

/-- The paired quadratic coefficient also vanishes on disconnected labels.
Every potentially nonzero pair consists of two connected full-carrier
factors, whose union is connected by the common `Pi^4` anchor. -/
theorem
    cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient_eq_zero_of_not_walkConnected
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S₁ S₂ : Finset (FinBox 4 (2 * Q)))
    (Δπ : PhysicalEndomorphism M Q Nc)
    (v : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) W) :
    cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient
      (R := R) anchor K hc hmass hK s S₁ S₂ Δπ v W = 0 := by
  classical
  unfold cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient
    cmp102Eq80SourcePi4AnchoredPairFiber
  apply Finset.sum_eq_zero
  intro YZ hYZ
  have hlabel :
      cmp102Eq80SourcePi4AnchoredPairDomain anchor YZ = W := by
    simpa using (Finset.mem_filter.mp hYZ).2
  by_cases hsubset₁ :
      cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ YZ.1
  · by_cases hsubset₂ :
        cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ YZ.2
    · by_cases hconnected₁ :
          walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) YZ.1
      · by_cases hconnected₂ :
            walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) YZ.2
        · exfalso
          apply hconnected
          rw [← hlabel]
          exact walkConnected_cmp102Eq80SourcePi4AnchoredPairDomain
            anchor YZ hsubset₁ hsubset₂ hconnected₁ hconnected₂
        · unfold cmp102Eq80SourcePi4DomainQuadraticMixedPairTerm
          rw [
            cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_walkConnected
              anchor K hc hmass hK s S₂ YZ.2 hconnected₂]
          exact cmp102Eq80QuadraticMixedPairTerm_zero_right _ _ _
      · unfold cmp102Eq80SourcePi4DomainQuadraticMixedPairTerm
        rw [
          cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_walkConnected
            anchor K hc hmass hK s S₁ YZ.1 hconnected₁]
        exact cmp102Eq80QuadraticMixedPairTerm_zero_left _ _ _
    · unfold cmp102Eq80SourcePi4DomainQuadraticMixedPairTerm
      rw [
        cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_subset
          anchor K hc hmass hK s S₂ YZ.2 hsubset₂]
      exact cmp102Eq80QuadraticMixedPairTerm_zero_right _ _ _
  · unfold cmp102Eq80SourcePi4DomainQuadraticMixedPairTerm
    rw [
      cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_subset
        anchor K hc hmass hK s S₁ YZ.1 hsubset₁]
    exact cmp102Eq80QuadraticMixedPairTerm_zero_left _ _ _

/-- Exact physical depth-two localization of the quadratic equation-(80)
term.  Both complete mixed propagators are decomposed internally; no
domainwise product expansion is supplied as a hypothesis. -/
theorem
    cmp102Eq80QuadraticMixedPairTerm_fullRealMixed_eq_sum_pi4Domains
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
    (S₁ S₂ : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (v : PhysicalField M Q Nc) :
    cmp102Eq80QuadraticMixedPairTerm
        (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK s S₁)
        (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK s S₂)
        Δπ v =
      ∑ W : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4QuadraticMixedDomainCoefficient
          (R := R) anchor K hc hmass hK s S₁ S₂ Δπ v W := by
  rw [
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 s S₁ hRweak hs hcap hsmall,
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 s S₂ hRweak hs hcap hsmall,
    cmp102Eq80QuadraticMixedPairTerm_sum_sum]
  rw [sum_cmp102Eq80SourcePi4AnchoredPairFiber]
  rfl

end

end YangMills.RG

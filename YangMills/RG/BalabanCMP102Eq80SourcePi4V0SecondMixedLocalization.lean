/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4QuadraticMixedLocalization

/-!
# Source localization of the second mixed `V₀` term

For the shifted field `A - H(s) (D A)`, two distinct weakening derivatives
produce

`D²V₀ [H_d (D A), H_e (D A)] - DV₀ [H_de (D A)]`.

The signs come from the two negative first variations and the negative
second variation of the shifted field.  This file defines that literal
expression, expands the Hessian term over ordered pairs of physical source
domains, and combines it with the single-domain expansion of `H_de`.

The result is an exact finite localization identity.  The separate
calculus theorem identifying this expression with the actual second
derivative of the physical curve is intentionally left to the next layer.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Literal second mixed contribution of the shifted `V₀` term. -/
noncomputable def cmp102Eq80V0SecondMixedTerm
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V₀' : E →L[ℝ] ℝ)
    (V₀'' : E →L[ℝ] E →L[ℝ] ℝ)
    (Kde Kd Ke : F →L[ℝ] E) (v : F) : ℝ :=
  V₀'' (Kd v) (Ke v) - V₀' (Kde v)

/-- The bilinear Hessian part expands exactly over two finite operator
families. -/
theorem cmp102Eq80V0BilinearTerm_sum_sum
    {E F ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype ι] [Fintype κ]
    (V₀'' : E →L[ℝ] E →L[ℝ] ℝ)
    (Kd : ι → F →L[ℝ] E) (Ke : κ → F →L[ℝ] E)
    (v : F) :
    V₀'' ((∑ i, Kd i) v) ((∑ j, Ke j) v) =
      ∑ p : ι × κ, V₀'' ((Kd p.1) v) ((Ke p.2) v) := by
  classical
  simp only [ContinuousLinearMap.sum_apply, map_sum,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- One paired physical source-domain Hessian term. -/
noncomputable def cmp102Eq80SourcePi4DomainV0BilinearPairTerm
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (Sd Se : Finset (FinBox 4 (2 * Q)))
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (v : PhysicalField M Q Nc)
    (YZ : Finset (FinBox 4 (2 * Q)) ×
      Finset (FinBox 4 (2 * Q))) : ℝ :=
  V₀''
    (cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
      (R := R) anchor K hc hmass hK s Sd YZ.1 v)
    (cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
      (R := R) anchor K hc hmass hK s Se YZ.2 v)

/-- The paired Hessian coefficient at one union label. -/
noncomputable def cmp102Eq80SourcePi4V0BilinearDomainCoefficient
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (Sd Se : Finset (FinBox 4 (2 * Q)))
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (v : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q))) : ℝ :=
  cmp102Eq80SourcePi4AnchoredPairFiber anchor
    (cmp102Eq80SourcePi4DomainV0BilinearPairTerm
      (R := R) anchor K hc hmass hK s Sd Se V₀'' v) W

/-- The Hessian pair fiber vanishes when its union label omits the common
physical anchor. -/
theorem
    cmp102Eq80SourcePi4V0BilinearDomainCoefficient_eq_zero_of_not_subset
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (Sd Se : Finset (FinBox 4 (2 * Q)))
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (v : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q)))
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ W) :
    cmp102Eq80SourcePi4V0BilinearDomainCoefficient
      (R := R) anchor K hc hmass hK s Sd Se V₀'' v W = 0 := by
  classical
  unfold cmp102Eq80SourcePi4V0BilinearDomainCoefficient
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

/-- Every potentially nonzero Hessian pair contains two connected
full-carrier factors; hence its union label is connected. -/
theorem
    cmp102Eq80SourcePi4V0BilinearDomainCoefficient_eq_zero_of_not_walkConnected
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (Sd Se : Finset (FinBox 4 (2 * Q)))
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (v : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) W) :
    cmp102Eq80SourcePi4V0BilinearDomainCoefficient
      (R := R) anchor K hc hmass hK s Sd Se V₀'' v W = 0 := by
  classical
  unfold cmp102Eq80SourcePi4V0BilinearDomainCoefficient
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
        · unfold cmp102Eq80SourcePi4DomainV0BilinearPairTerm
          rw [
            cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_walkConnected
              anchor K hc hmass hK s Se YZ.2 hconnected₂]
          simp
      · unfold cmp102Eq80SourcePi4DomainV0BilinearPairTerm
        rw [
          cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_walkConnected
            anchor K hc hmass hK s Sd YZ.1 hconnected₁]
        simp
    · unfold cmp102Eq80SourcePi4DomainV0BilinearPairTerm
      rw [
        cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_subset
          anchor K hc hmass hK s Se YZ.2 hsubset₂]
      simp
  · unfold cmp102Eq80SourcePi4DomainV0BilinearPairTerm
    rw [
      cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_subset
        anchor K hc hmass hK s Sd YZ.1 hsubset₁]
    simp

/-- Complete localized coefficient of the shifted `V₀` contribution:
paired Hessian coefficient minus the single-domain `H_de` coefficient. -/
noncomputable def cmp102Eq80SourcePi4V0SecondMixedDomainCoefficient
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (Sde Sd Se : Finset (FinBox 4 (2 * Q)))
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (v : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q))) : ℝ :=
  cmp102Eq80SourcePi4V0BilinearDomainCoefficient
      (R := R) anchor K hc hmass hK s Sd Se V₀'' v W
    - V₀'
      (cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
        (R := R) anchor K hc hmass hK s Sde W v)

/-- The complete shifted-`V₀` second mixed coefficient retains the entire
literal `Pi^4` carrier. -/
theorem
    cmp102Eq80SourcePi4V0SecondMixedDomainCoefficient_eq_zero_of_not_subset
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (Sde Sd Se : Finset (FinBox 4 (2 * Q)))
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (v : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q)))
    (hanchor : ¬cmp102Eq80SourcePi4AnchorCarrier anchor ⊆ W) :
    cmp102Eq80SourcePi4V0SecondMixedDomainCoefficient
      (R := R) anchor K hc hmass hK s Sde Sd Se V₀' V₀'' v W = 0 := by
  unfold cmp102Eq80SourcePi4V0SecondMixedDomainCoefficient
  rw [
    cmp102Eq80SourcePi4V0BilinearDomainCoefficient_eq_zero_of_not_subset
      anchor K hc hmass hK s Sd Se V₀'' v W hanchor,
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_subset
      anchor K hc hmass hK s Sde W hanchor]
  simp

/-- The complete shifted-`V₀` second mixed coefficient is supported only on
face-connected physical source labels. -/
theorem
    cmp102Eq80SourcePi4V0SecondMixedDomainCoefficient_eq_zero_of_not_walkConnected
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (Sde Sd Se : Finset (FinBox 4 (2 * Q)))
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (v : PhysicalField M Q Nc)
    (W : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) W) :
    cmp102Eq80SourcePi4V0SecondMixedDomainCoefficient
      (R := R) anchor K hc hmass hK s Sde Sd Se V₀' V₀'' v W = 0 := by
  unfold cmp102Eq80SourcePi4V0SecondMixedDomainCoefficient
  rw [
    cmp102Eq80SourcePi4V0BilinearDomainCoefficient_eq_zero_of_not_walkConnected
      anchor K hc hmass hK s Sd Se V₀'' v W hconnected,
    cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_eq_zero_of_not_walkConnected
      anchor K hc hmass hK s Sde W hconnected]
  simp

/-- Exact physical localization of the full second mixed shifted-`V₀`
expression.  The complete `H_de`, `H_d`, and `H_e` operators are all
decomposed internally into their source-correct domains. -/
theorem cmp102Eq80V0SecondMixedTerm_fullRealMixed_eq_sum_pi4Domains
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
    (Sde Sd Se : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (V₀'' : PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ)
    (v : PhysicalField M Q Nc) :
    cmp102Eq80V0SecondMixedTerm V₀' V₀''
        (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK s Sde)
        (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK s Sd)
        (cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK s Se)
        v =
      ∑ W : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4V0SecondMixedDomainCoefficient
          (R := R) anchor K hc hmass hK s Sde Sd Se V₀' V₀'' v W := by
  rw [
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 s Sde hRweak hs hcap hsmall,
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 s Sd hRweak hs hcap hsmall,
    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative_eq_sum_pi4CarrierAnchoredDomainOperator
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 s Se hRweak hs hcap hsmall]
  have hpair :
      V₀''
          ((∑ Y : Finset (FinBox 4 (2 * Q)),
            cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
              (R := R) anchor K hc hmass hK s Sd Y) v)
          ((∑ Y : Finset (FinBox 4 (2 * Q)),
            cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
              (R := R) anchor K hc hmass hK s Se Y) v) =
        ∑ W : Finset (FinBox 4 (2 * Q)),
          cmp102Eq80SourcePi4V0BilinearDomainCoefficient
            (R := R) anchor K hc hmass hK s Sd Se V₀'' v W := by
    rw [cmp102Eq80V0BilinearTerm_sum_sum]
    rw [sum_cmp102Eq80SourcePi4AnchoredPairFiber]
    rfl
  unfold cmp102Eq80V0SecondMixedTerm
  rw [hpair]
  simp only [ContinuousLinearMap.sum_apply, map_sum]
  rw [← Finset.sum_sub_distrib]
  rfl

end

end YangMills.RG

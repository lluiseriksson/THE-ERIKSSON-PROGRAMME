/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4PhysicalConnectedDecomposition

/-!
# Normalization of the equation-(80) connected-domain activities

The component normalizations make the equation-(80) functional vanish at
the zero physical field for every propagator.  Consequently every
propagator Taylor coefficient, every localized Faà di Bruno coefficient,
and every literal FTC connected-domain activity vanishes there.

This is the order-zero half of the normalization needed before applying the
radial Taylor construction to the equation-(80) connected sector.  The
order-one statement is kept separate because it additionally requires
commuting the physical-field derivative with the finite propagator jets and
the recursive interval integrals.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- At the zero physical field, the outer equation-(80) functional is the
zero function of the propagator. -/
theorem cmp102Eq80PotentialAsFunctionOfPropagator_zero_field
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80PotentialAsFunctionOfPropagator D D₃ V₀ Δπ J 0 =
      (fun _ : PhysicalEndomorphism M Q Nc => 0) := by
  funext H
  exact cmp102Eq80GlobalPotential_zero
    D D₃ V₀ H Δπ J hD0 hD₃0 hV₀0

/-- Every domain-choice propagator jet vanishes at the zero physical
field. -/
theorem cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_zero_field
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (choice : CMP102Eq80FaaDiBrunoDomainChoice
      (Q := Q) partition)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
        vertexBase sigma L coordinates partition choice = 0 := by
  rw [cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt]
  rw [cmp102Eq80PotentialAsFunctionOfPropagator_zero_field
    D D₃ V₀ Δπ J hD0 hD₃0 hV₀0]
  simp [ftaylorSeries]

/-- Every coefficient of one domain label inside one ordered partition
vanishes at the zero physical field. -/
theorem
    cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt_zero_field
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (W : Finset (FinBox 4 (2 * Q)))
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
        vertexBase sigma L coordinates partition W = 0 := by
  unfold cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
  apply Finset.sum_eq_zero
  intro choice _hchoice
  exact
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_zero_field
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      vertexBase sigma L coordinates partition choice hD0 hD₃0 hV₀0

/-- The complete arbitrary-depth coefficient of every physical domain label
vanishes at the zero physical field. -/
theorem cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_zero_field
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (W : Finset (FinBox 4 (2 * Q)))
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
        vertexBase sigma L coordinates W = 0 := by
  unfold cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
  apply Finset.sum_eq_zero
  intro partition _hpartition
  exact
    cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt_zero_field
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      vertexBase sigma L coordinates partition W hD0 hD₃0 hV₀0

/-- Every recursive contribution of one connected-domain label vanishes at
the zero physical field.  The statement covers all intermediate FTC
histories, not just the source-level root. -/
theorem cmp102Eq80SourcePi4FTCConnectedDomainActivity_zero_field
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80SourcePi4FTCConnectedDomainActivity
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
        vertexBase vertexCoordinates W n coordinates sigma L = 0 := by
  induction L generalizing n coordinates sigma with
  | nil =>
      simp only [cmp102Eq80SourcePi4FTCConnectedDomainActivity]
      split
      · rfl
      · exact
          cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_zero_field
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            vertexBase sigma vertexCoordinates coordinates W
            hD0 hD₃0 hV₀0
  | cons d tail ih =>
      rw [cmp102Eq80SourcePi4FTCConnectedDomainActivity, ih]
      simp_rw [ih]
      simp

/-- Source-level connected-domain activities are normalized at the zero
physical field. -/
theorem cmp102Eq80SourcePi4ConnectedDomainActivity_zero_field
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80SourcePi4ConnectedDomainActivity
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
        vertexBase vertexCoordinates sigma L W = 0 := by
  exact
    cmp102Eq80SourcePi4FTCConnectedDomainActivity_zero_field
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      vertexBase vertexCoordinates W Fin.elim0 sigma L
      hD0 hD₃0 hV₀0

end

end YangMills.RG

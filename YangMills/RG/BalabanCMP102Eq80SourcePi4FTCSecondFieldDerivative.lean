/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivative

/-!
# Second field derivative through the equation-(80) FTC tree

This file mirrors the literal connected-domain FTC recursion with the
second physical-field derivative constructed from the source joint jets.
The subsequent module proves joint continuity, and the normalization
module proves that this is the actual derivative of the first-derivative
tree.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Explicit second physical-field derivative at every intermediate node
of the literal connected-domain FTC tree. -/
noncomputable def cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (n : ℕ) (coordinates : Fin n → FinBox 4 (2 * Q))
    (sigma : FinBox 4 (2 * Q) → ℝ) :
    List (FinBox 4 (2 * Q)) →
      (PhysicalField M Q Nc →L[ℝ]
        PhysicalField M Q Nc →L[ℝ] ℝ)
  | [] =>
      if n = 0 then 0 else
        cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma vertexCoordinates coordinates W
  | d :: tail =>
      cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase vertexCoordinates W n coordinates
          (Function.update sigma d 0) tail +
        ∫ t in (0 : ℝ)..1,
          cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase vertexCoordinates W (n + 1)
            (Fin.cons d coordinates) (Function.update sigma d t) tail

/-- Source-level second derivative of one connected physical domain. -/
noncomputable def cmp102Eq80SourcePi4ConnectedDomainSecondFieldDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q))) :
    PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ :=
  cmp102Eq80SourcePi4FTCConnectedDomainSecondFieldDerivative
    (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
    vertexBase vertexCoordinates W 0 Fin.elim0 s L

end

end YangMills.RG

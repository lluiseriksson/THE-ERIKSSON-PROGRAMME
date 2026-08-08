/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4ConnectedDomainFieldDerivative

/-!
# Explicit field derivative through the equation-(80) FTC tree

This file defines the derivative candidate for every intermediate node of
the literal connected-domain FTC recursion.  It uses the explicit
Faà di Bruno derivative at the leaves and applies exactly the same finite
addition and interval integration as the source activity.

The derivative candidate is normalized at the zero physical field at every
depth.  The subsequent module proves that it is the actual Fréchet
derivative by the parametric interval theorem.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Explicit physical-field derivative of one connected-domain
contribution at every intermediate node of the FTC tree. -/
noncomputable def cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
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
    List (FinBox 4 (2 * Q)) → (PhysicalField M Q Nc →L[ℝ] ℝ)
  | [] =>
      if n = 0 then 0 else
        cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma vertexCoordinates coordinates W
  | d :: tail =>
      cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase vertexCoordinates W n coordinates
          (Function.update sigma d 0) tail +
        ∫ t in (0 : ℝ)..1,
          cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase vertexCoordinates W (n + 1)
            (Fin.cons d coordinates) (Function.update sigma d t) tail

/-- Source-level explicit derivative of one connected physical domain. -/
noncomputable def cmp102Eq80SourcePi4ConnectedDomainFieldDerivative
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
    PhysicalField M Q Nc →L[ℝ] ℝ :=
  cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
    (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
    vertexBase vertexCoordinates W 0 Fin.elim0 s L

/-- The explicit derivative candidate vanishes at the zero physical field
at every intermediate FTC node. -/
theorem
    cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative_zero_field
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
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0) :
    cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
        vertexBase vertexCoordinates W n coordinates sigma L = 0 := by
  induction L generalizing n coordinates sigma with
  | nil =>
      simp only [
        cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative]
      split
      · rfl
      · exact
          cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt_zero_field
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            vertexBase sigma vertexCoordinates coordinates W
            hD hD₃ hV₀ hD0 hD₃0 hD₃' hV₀'
  | cons d tail ih =>
      rw [cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative, ih]
      simp_rw [ih]
      simp

/-- The source-level derivative candidate is normalized at the origin. -/
theorem cmp102Eq80SourcePi4ConnectedDomainFieldDerivative_zero_field
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
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (W : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0) :
    cmp102Eq80SourcePi4ConnectedDomainFieldDerivative
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
        vertexBase vertexCoordinates s L W = 0 := by
  exact
    cmp102Eq80SourcePi4FTCConnectedDomainFieldDerivative_zero_field
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      vertexBase vertexCoordinates W Fin.elim0 s L
      hD hD₃ hV₀ hD0 hD₃0 hD₃' hV₀'

end

end YangMills.RG

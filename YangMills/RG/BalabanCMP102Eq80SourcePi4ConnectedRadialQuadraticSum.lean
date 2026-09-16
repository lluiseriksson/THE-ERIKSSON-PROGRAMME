/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4ConnectedDomainRadialQuadratic
import YangMills.RG.BalabanCMP102Eq80SourcePi4PhysicalConnectedDecomposition

/-!
# The complete connected radial quadratic sector of equation (80)

The source-specific connected-domain construction produces one radial
quadratic operator for every physical domain label.  This file takes their
literal finite sum and proves that it reconstructs the complete
nondecoupled part of the equation-(80) FTC expansion.

The terminal identity is deliberately sectorial:

`equation80 = fullyDecoupledLeaf + 1/2 * <B, Q_equation80(B) B>`.

It does not call the fully decoupled leaf `V''_k`.  The latter also receives
the other contributions to the fluctuation-field action and must satisfy
the independent source estimate (1.36).
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- The finite sum of the radial quadratic operators belonging to all
connected equation-(80) domain labels. -/
noncomputable def cmp102Eq80SourcePi4ConnectedRadialQuadraticSum
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
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
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hs : CMP116RealPhysicalContourRegion Rweak s)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (B : PhysicalField M Q Nc) :
    PhysicalEndomorphism M Q Nc :=
  ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
    cmp102Eq80SourcePi4ConnectedDomainRadialQuadratic
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      vertexBase vertexCoordinates s L W
      hRweak hs hsmall hD hD₃ hV₀ B

/-- The quadratic form of the finite operator sum is exactly the finite sum
of the connected equation-(80) activities. -/
theorem
    inner_cmp102Eq80SourcePi4ConnectedRadialQuadraticSum_eq_sum_activity
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
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
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hs : CMP116RealPhysicalContourRegion Rweak s)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hV₀0 : V₀ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0)
    (B : PhysicalField M Q Nc) :
    (1 / 2 : ℝ) * inner ℝ B
        (cmp102Eq80SourcePi4ConnectedRadialQuadraticSum
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          hAhead hrho hrate Cert htri hrange hΔ hΔ1
          vertexBase vertexCoordinates s L
          hRweak hs hsmall hD hD₃ hV₀ B B) =
      ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
        cmp102Eq80SourcePi4ConnectedDomainActivity
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J B
          vertexBase vertexCoordinates s L W := by
  classical
  unfold cmp102Eq80SourcePi4ConnectedRadialQuadraticSum
  simp only [ContinuousLinearMap.sum_apply, inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W hW
  exact
    inner_cmp102Eq80SourcePi4ConnectedDomainRadialQuadratic_eq_activity
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      vertexBase vertexCoordinates s L W
      hRweak hs hsmall hD hD₃ hV₀
      hD0 hD₃0 hV₀0 hD₃' hV₀' B

set_option maxHeartbeats 128000000 in
/-- Exact source-specific split of the complete equation-(80) sector into
its fully decoupled leaf and its connected radial quadratic core. -/
theorem
    cmp102Eq80SourcePi4PhysicalPotential_eq_decoupledLeaf_add_radialQuadratic
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (PatchCert : CMP99PhysicalPatchWeightedCertificate
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
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (hcoordinates : coordinates.Nodup)
    (hcover : ∀ d : FinBox 4 (2 * Q), d ∈ coordinates)
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (hRweak : 1 ≤ Rweak)
    (hbaseShift : ∀ x, ‖(base x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hbaseCap : ∀ x, ‖(base x : ℂ)‖ ≤ Rweak)
    (hsShift : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hsCap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hV₀0 : V₀ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0)
    (B : PhysicalField M Q Nc) :
    cmp102Eq80SourcePi4RealMixedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        (cmp116SetRealWeakeningList s L 1) ∅ B =
      cmp102Eq80SourcePi4FullyDecoupledResidual
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          base coordinates s L B +
        (1 / 2 : ℝ) * inner ℝ B
          (cmp102Eq80SourcePi4ConnectedRadialQuadraticSum
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            hAhead hrho hrate PatchCert htri hrange hΔ hΔ1
            base coordinates s L hRweak
            ⟨hsShift, hsCap⟩ hsmall hD hD₃ hV₀ B B) := by
  rw [
    cmp102Eq80SourcePi4PhysicalPotential_eq_decoupledLeaf_add_sum_connected
      (R := R) anchor K hc hmass hK
      hAhead hrho hrate hgeom PatchCert htri hrange hΔ hΔ1
      D D₃ V₀ Δπ J base coordinates hcoordinates hcover
      s L hL hRweak hbaseShift hbaseCap hsShift hsCap hsmall B
      (hV₀.of_le le_top)]
  congr 1
  exact
    (inner_cmp102Eq80SourcePi4ConnectedRadialQuadraticSum_eq_sum_activity
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      hAhead hrho hrate PatchCert htri hrange hΔ hΔ1
      base coordinates s L hRweak ⟨hsShift, hsCap⟩ hsmall
      hD hD₃ hV₀ hD0 hD₃0 hV₀0 hD₃' hV₀' B).symm

end

end YangMills.RG

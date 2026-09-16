/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCConnectedDomainActivity

/-!
# Literal connected-domain decomposition of the physical equation-(80) term

This file composes the three source-specific identities already proved:

1. the complete FTC tree sums to the fully coupled physical equation-(80)
   potential;
2. the tree splits exactly into its all-zero leaf and its nondecoupled
   remainder;
3. the nondecoupled remainder is the finite sum of the connected-domain
   activities.

The all-zero leaf is deliberately called the *fully decoupled leaf*.  It is
not identified with Balaban's `V''_k`: that residual also contains the other
fluctuation-action contributions and must satisfy the separate bound (1.36).
Likewise, the connected terms constructed here are the equation-(80) sector,
not yet the complete `V_k(Y, B)` of (1.41).
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

set_option maxHeartbeats 128000000 in
/-- The literal fully coupled equation-(80) potential is the sum of its
fully decoupled FTC leaf and the finite family of physical connected-domain
activities.  This theorem is a source-faithful decomposition of the
equation-(80) sector only; it makes no identification with `V''_k`. -/
theorem
    cmp102Eq80SourcePi4PhysicalPotential_eq_decoupledLeaf_add_sum_connected
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
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ (L.length + 1) V₀) :
    cmp102Eq80SourcePi4RealMixedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        (cmp116SetRealWeakeningList s L 1) ∅ A =
      cmp102Eq80SourcePi4FullyDecoupledResidual
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          base coordinates s L A +
        ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
          cmp102Eq80SourcePi4ConnectedDomainActivity
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            base coordinates s L W := by
  have hV₀L : ContDiff ℝ L.length V₀ :=
    hV₀.of_le
      (WithTop.coe_le_coe.mpr
        (ENat.coe_le_coe.mpr (Nat.le_add_right L.length 1)))
  calc
    _ =
        (cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          base coordinates s L A).expansionSum :=
      (cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree_expansionSum_eq_physical
        (R := R) anchor K hc hmass hK
        hAhead hrho hrate hgeom PatchCert htri hrange hΔ hΔ1
        D D₃ V₀ Δπ J base coordinates hcoordinates hcover
        s L hL hRweak hbaseShift hbaseCap hsShift hsCap hsmall A hV₀).symm
    _ =
        cmp102Eq80SourcePi4FullyDecoupledResidual
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            base coordinates s L A +
          cmp102Eq80SourcePi4FTCNondecoupledRemainder
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            base coordinates s L A :=
      cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree_expansionSum_eq_residual_add_nondecoupled
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        base coordinates s L A
    _ = _ := by
      rw [
        cmp102Eq80SourcePi4FTCNondecoupledRemainder_eq_sum_connectedDomainActivity
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          hAhead hrho hrate hgeom PatchCert htri hrange hΔ hΔ1
          base s coordinates L hcoordinates hcover hL hRweak
          ⟨hbaseShift, hbaseCap⟩ ⟨hsShift, hsCap⟩ hsmall hV₀L]

end

end YangMills.RG

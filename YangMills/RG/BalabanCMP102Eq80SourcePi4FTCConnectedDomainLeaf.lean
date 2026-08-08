/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCFixedCoordinateDerivatives

/-!
# Connected-domain identification of every active FTC leaf

This module closes the terminal case needed to identify the complete physical
FTC remainder.  A nonempty literal history is first identified with the
corresponding arbitrary-order jet.  The source-specific Faà di Bruno theorem
then regroups that jet exactly over the proved physical connected-domain
labels.

No terminal coefficient is assumed.  In particular, injectivity of the
coordinate family is generated from the no-repetition invariant of the FTC
history.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

set_option maxHeartbeats 32000000 in
/-- Every nonempty active FTC leaf is exactly the finite sum of its physical
connected-domain coefficients. -/
theorem
    cmp116FixedWeakeningCoordinateDerivatives_eq_sum_connectedPhysicalDomains
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
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
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (vertexCoordinates : List (FinBox 4 (2 * Q)))
    (hvertexCoordinates : vertexCoordinates.Nodup)
    (hcover :
      ∀ d : FinBox 4 (2 * Q), d ∈ vertexCoordinates)
    (history : List (FinBox 4 (2 * Q) × ℝ))
    (hnonempty : history ≠ [])
    (hnodup : (history.map Prod.fst).Nodup)
    (hvalues : ∀ p ∈ history, sigma p.1 = p.2)
    (hRweak : 1 ≤ Rweak)
    (hvertexBase :
      CMP116RealPhysicalContourRegion Rweak vertexBase)
    (hsigma : CMP116RealPhysicalContourRegion Rweak sigma)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hV₀ : ContDiff ℝ history.length V₀) :
    cmp116FixedWeakeningCoordinateDerivatives
        (fun tau =>
          cmp102Eq80SourcePi4RealPotentialVertexPolynomial
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            vertexBase vertexCoordinates tau A)
        history sigma =
      ∑ W ∈ cmp102Eq80SourcePi4FaaDiBrunoPhysicalDomainLabels anchor,
        cmp102Eq80SourcePi4FTCConnectedDomainContribution
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase vertexCoordinates history sigma [] W := by
  let f := fun tau =>
    cmp102Eq80SourcePi4RealPotentialVertexPolynomial
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      vertexBase vertexCoordinates tau A
  have hf : ContDiff ℝ history.length f :=
    contDiff_cmp102Eq80SourcePi4RealPotentialVertexPolynomial
      history.length anchor K hc hmass hK D D₃ V₀ Δπ J
      vertexBase vertexCoordinates A hV₀
  rw [
    cmp116FixedWeakeningCoordinateDerivatives_eq_iteratedFDeriv
      f history sigma hnodup hvalues hf,
    cmp116FixedWeakeningCoordinateDirections_eq_names]
  rw [
    iteratedFDeriv_cmp102Eq80SourcePi4RealPotentialVertexPolynomial_apply_coordinateBlock_at_eq_sum_connectedPhysicalDomains
      anchor K hc hmass hK D D₃ V₀ Δπ J A
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      vertexBase sigma vertexCoordinates hvertexCoordinates hcover
      (cmp116FixedWeakeningCoordinateNames history)
      (cmp116FixedWeakeningCoordinateNames_injective history hnodup)
      hRweak hvertexBase hsigma hsmall hV₀]
  apply Finset.sum_congr rfl
  intro W hW
  cases history with
  | nil => contradiction
  | cons p history =>
      rfl

end

end YangMills.RG

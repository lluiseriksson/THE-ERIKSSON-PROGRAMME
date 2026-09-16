/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredPotentialDerivativeSupport
import YangMills.RG.BalabanCMP102Eq80SourcePi4MixedPotentialFTCExpansionTree

/-!
# Source-correct root fiber of the physical equation-(80) FTC tree

The physical derivative certificate identifies the root coordinate
derivative of the complete literal potential.  The complete mixed covariance
direction is then decomposed into its full-`Pi^4` source-domain operators.
This gives the first exact localized fiber of the arbitrary-depth FTC tree,
with all four equation-(80) terms retained.
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

set_option maxHeartbeats 2000000 in
/-- The first physical FTC fiber is exactly the finite sum of literal
equation-(80) source-domain derivatives. -/
theorem
    CMP116SourcePi4RealMixedDerivativeCertificate.realWeakeningDerivative_eq_sum_pi4CarrierAnchoredDomains
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
    (s : FinBox 4 (2 * Q) → ℝ)
    (d : FinBox 4 (2 * Q))
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (t : ℝ)
    (Cert : CMP116SourcePi4RealMixedDerivativeCertificate
      (R := R) anchor K hc hmass hK s ∅ d t)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (hV₀ : HasFDerivAt V₀ V₀'
      (A -
        cmp116SourcePi4RealMixedCovarianceOperatorCurve
          (R := R) anchor K hc hmass hK s ∅ d t (D A))) :
    cmp116RealWeakeningCoordinateDerivative
        (fun sigma =>
          cmp102Eq80SourcePi4RealMixedPotential
            (R := R) anchor K hc hmass hK
            D D₃ V₀ Δπ J sigma ∅ A)
        d t s =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        cmp102Eq80SourcePi4CarrierAnchoredDomainPotentialDerivative
          (R := R) anchor K hc hmass hK s {d} Y
          D D₃
          (cmp116SourcePi4RealMixedCovarianceOperatorCurve
            (R := R) anchor K hc hmass hK s ∅ d t)
          Δπ J A V₀' := by
  rw [
    CMP116SourcePi4RealMixedDerivativeCertificate.realWeakeningDerivative_eq
      anchor K hc hmass hK D D₃ V₀ Δπ J s d A t Cert V₀' hV₀]
  unfold cmp102Eq80SourcePi4RealMixedPotentialCurveDerivative
  rw [cmp116SourcePi4RealMixedCovarianceOperatorDerivative_eq]
  exact
    cmp102Eq80PropagatorDirectionalDerivative_fullRealMixed_eq_sum_pi4CarrierAnchoredDomains
      anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri hrange
      hΔ hΔ1 s {d} hRweak hs hcap hsmall D D₃
      (cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK s ∅ d t)
      Δπ J A V₀'

end

end YangMills.RG

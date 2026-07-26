/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4RealMixedPotentialDerivative
import YangMills.RG.BalabanCMP116SourcePi4RealMixedCovarianceAffineRegularity

/-!
# All-order regularity of the literal equation-(80) coordinate lines

The physical covariance coordinate line is exactly affine and hence smooth
to every order.  Composing it with the four literal terms of CMP102 equation
(80) therefore transfers precisely the regularity of the physical residual
potential `V₀`; no regularity assumption on an abstract weakened potential is
introduced.
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

/-- Along every source-certified fresh weakening coordinate, the complete
literal equation-(80) potential has exactly the differentiability order
available for `V₀`. -/
theorem
    contDiff_cmp102Eq80SourcePi4RealMixedPotentialCurve_ofPhysicalContour
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (n : WithTop ℕ∞)
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
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) (hdS : d ∉ S)
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ n V₀) :
    ContDiff ℝ n
      (cmp102Eq80SourcePi4RealMixedPotentialCurve
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s S d A) := by
  unfold cmp102Eq80SourcePi4RealMixedPotentialCurve
  exact
    contDiff_cmp102Eq80GlobalPotential_propagatorFamily
      D D₃ V₀
      (cmp116SourcePi4RealMixedCovarianceOperatorCurve
        (R := R) anchor K hc hmass hK s S d)
      Δπ J A
      (contDiff_cmp116SourcePi4RealMixedCovarianceOperatorCurve_ofPhysicalContour
        n anchor K hc hmass hK hAhead hrho hrate hgeom PatchCert htri
        hrange hΔ hΔ1 s S d hdS hRweak hs hcap hsmall)
      hV₀

end

end YangMills.RG

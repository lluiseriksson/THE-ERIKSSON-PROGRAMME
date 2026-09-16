/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80CouplingScaledTaylorSplit
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCNormalization

/-!
# Coupling-scaled Taylor split of one literal CMP102 domain potential

The equation-(1.36) residual is evaluated after the physical substitution

`B ↦ g_k C B`.

This file specializes the exact coupling-scaled Taylor split to the literal
fine-head-tail domain FTC contribution from equation (80).  Its normalization
at the origin is generated internally from the physical `D`, `D₃`, and `V₀`
normalizations.

The result is an exact identity.  It closes the source-coordinate dictionary
between the unscaled domain potential and the Gaussian-coordinate potential,
but proves no residual majorant and does not claim equation (1.36).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CoarseField Q Nc →L[ℝ] FineField M Q Nc

/-- Exact fixed-quadratic plus residual split of one literal equation-(80)
domain contribution after the physical Gaussian-coordinate substitution
`B ↦ g_k C B`. -/
theorem
    cmp102Eq80CouplingScaledFineHeadTailDomainPotential_eq_fixed_add_residual
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (weakening : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖weakening d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : FineField M Q Nc →L[ℝ] CoarseField Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : FineField M Q Nc →L[ℝ] ℝ) 0)
    (gk : ℝ) (B : FineField M Q Nc) :
    let f : FineField M Q Nc → ℝ := fun X =>
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        weakening layerWord choice D D₃ V₀ P T Δπ J X Y
    cmp102Eq80CouplingScaledPotential gk f B =
      (1 / 2 : ℝ) * inner ℝ B
        (cmp102Eq80CouplingScaledFixedQuadratic gk f
          (contDiff_two_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
            anchor K hc hmass hK baseCoarseCovariance
            hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
            weakening hRweak hcap hsmall layerWord choice
            D D₃ V₀ P T Δπ J Y hD hD₃ hV₀) B) +
      cmp102Eq80CouplingScaledTaylorResidual gk f
        (contDiff_two_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J Y hD hD₃ hV₀) B := by
  dsimp only
  let f : FineField M Q Nc → ℝ := fun X =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      weakening layerWord choice D D₃ V₀ P T Δπ J X Y
  have hf : ContDiff ℝ 2 f :=
    contDiff_two_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      weakening hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J Y hD hD₃ hV₀
  have hf0 : f 0 = 0 :=
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_zero_field
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      weakening hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J Y hD hD₃ hV₀ hD0 hD₃0 hV₀0
  have hdf0 : fderiv ℝ f 0 = 0 :=
    fderiv_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_zero_field
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      weakening hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J Y hD hD₃ hV₀ hD0 hD₃0 hD₃' hV₀'
  exact
    cmp102Eq80CouplingScaledPotential_eq_fixed_add_residual
      gk f hf hf0 hdf0 B

end

end YangMills.RG

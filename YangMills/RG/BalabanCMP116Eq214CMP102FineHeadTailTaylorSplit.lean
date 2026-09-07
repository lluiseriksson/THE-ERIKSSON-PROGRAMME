/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214CMP102FineHeadTailPotential
import YangMills.RG.BalabanCMP116RadialTaylorResidual

/-!
# Fixed-quadratic Taylor split of the literal CMP102 domain potential

The first CMP102-to-CMP116 installer represented each literal fine-head-tail
domain contribution by its full field-dependent radial operator and a zero
residual.  That identity is exact, but it does not expose the source split
needed by equations (1.36) and (1.42).

This file keeps the same literal contribution and refines its dictionary:

* the quadratic part is the radial Taylor operator frozen at the zero field;
* the scalar residual is the diagonal value of the operator difference
  `Q(B) - Q(0)`;
* their equation-(1.42) potential term is proved exactly equal to the original
  CMP102 domain FTC contribution.

Thus the residual is a constructed physical object rather than a free scalar
or a zero placeholder.  This module does not prove its equation-(1.36)
majorant.  It also does not identify this unscaled fine-head-tail installer
with the coupling-scaled Gaussian potential `f(g_k C B)` consumed by the
cutoff estimate; that source-coordinate dictionary remains a separate
obligation.
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

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FineField M Q Nc →L[ℝ] FineField M Q Nc

/-- The literal CMP102 domain quadratic family frozen at the zero field.
The dummy field argument is retained because equation (1.42) accepts a
field-dependent operator family. -/
noncomputable def
    cmp102Eq80PhysicalFineHeadTailDomainFixedQuadraticFamily
    {M Q Nc R Δ n nY : ℕ}
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
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (domain : Fin nY → Finset (FinBox 4 (2 * Q))) :
    Fin nY → FineField M Q Nc → PhysicalEndomorphism M Q Nc :=
  fun i _ =>
    cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      weakening hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain i 0

/-- The genuine scalar Taylor residual of one literal CMP102 domain
contribution.  It is the diagonal value of `Q(B) - Q(0)`, not a supplied
remainder and not the zero function. -/
noncomputable def
    cmp102Eq80PhysicalFineHeadTailDomainTaylorResidualFamily
    {M Q Nc R Δ n nY : ℕ}
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
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (domain : Fin nY → Finset (FinBox 4 (2 * Q))) :
    Fin nY → FineField M Q Nc → ℝ :=
  fun i B =>
    (1 / 2 : ℝ) * inner ℝ B
      ((cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain i B -
        cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain i 0) B)

/-- The constructed scalar residual is definitionally the diagonal residual
operator.  This exposes exactly the operator shape used by the
cutoff-centered cubic estimate, without claiming that the present unscaled
installer is already the coupling-scaled source potential. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainTaylorResidualFamily_eq
    {M Q Nc R Δ n nY : ℕ}
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
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (domain : Fin nY → Finset (FinBox 4 (2 * Q)))
    (i : Fin nY) (B : FineField M Q Nc) :
    cmp102Eq80PhysicalFineHeadTailDomainTaylorResidualFamily
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        weakening hRweak hcap hsmall layerWord choice
        D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain i B =
      (1 / 2 : ℝ) * inner ℝ B
        (cmp116RadialTaylorResidualOperator
          (fun X =>
            cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
              anchor K hc hmass hK baseCoarseCovariance
              weakening layerWord choice D D₃ V₀ P T Δπ J
              X (domain i))
          B
          (contDiff_two_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
            anchor K hc hmass hK baseCoarseCovariance
            hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
            weakening hRweak hcap hsmall layerWord choice
            D D₃ V₀ P T Δπ J (domain i) hD hD₃ hV₀)
          B) := by
  rfl

/-- The fixed quadratic plus the constructed Taylor residual is exactly the
same literal CMP102 fine-head-tail domain FTC contribution as the original
field-dependent radial installer. -/
theorem
    cmp116Eq142PhysicalPotentialTerm_fixedTaylorSplit_eq_cmp102Eq80FineHeadTailDomainFTCContribution
    {M Q Nc R Δ n nY : ℕ}
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
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : FineField M Q Nc →L[ℝ] CoarseField Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : FineField M Q Nc →L[ℝ] ℝ) 0)
    (domain : Fin nY → Finset (FinBox 4 (2 * Q)))
    (i : Fin nY) (B : FineField M Q Nc) :
    cmp116Eq142PhysicalPotentialTerm
        (cmp102Eq80PhysicalFineHeadTailDomainFixedQuadraticFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain)
        (cmp102Eq80PhysicalFineHeadTailDomainTaylorResidualFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain)
        i B =
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        weakening layerWord choice D D₃ V₀ P T Δπ J B (domain i) := by
  calc
    cmp116Eq142PhysicalPotentialTerm
        (cmp102Eq80PhysicalFineHeadTailDomainFixedQuadraticFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain)
        (cmp102Eq80PhysicalFineHeadTailDomainTaylorResidualFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain)
        i B =
      cmp116Eq142PhysicalPotentialTerm
        (cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain)
        (fun _ _ => 0) i B := by
          simp only [
            cmp116Eq142PhysicalPotentialTerm,
            cmp102Eq80PhysicalFineHeadTailDomainFixedQuadraticFamily,
            cmp102Eq80PhysicalFineHeadTailDomainTaylorResidualFamily,
            ContinuousLinearMap.sub_apply, inner_sub_right]
          ring
    _ =
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        weakening layerWord choice D D₃ V₀ P T Δπ J B (domain i) :=
      cmp116Eq142PhysicalPotentialTerm_eq_cmp102Eq80FineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        weakening hRweak hcap hsmall layerWord choice
        D D₃ V₀ P T Δπ J hD hD₃ hV₀
        hD0 hD₃0 hV₀0 hD₃' hV₀' domain i B

end

end YangMills.RG

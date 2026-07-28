/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCRadial
import YangMills.RG.BalabanCMP116RadialTaylorBound

/-!
# Literal CMP102 equation-(1.43) frontier

This module identifies the Fréchet Hessian consumed by the radial Taylor
bound with the literal second field derivative of the reconstructed CMP102
domain contribution.  It then exposes equation (1.43) at the correct level:
a matrix-element estimate on that literal second derivative along `t • B`.

Equation (1.36) is deliberately absent.  It bounds the distinct residual
`V''_k`; using its majorant as an operator-norm bound for the radial
quadratic operator would conflate two source objects.

The remaining premise is source-facing and quantitative.  It must be
derived from the CMP102 source jets and domain-decay estimates; this module
does not rename it as a bound on the already constructed radial operator.
-/

open Set
open scoped RealInnerProductSpace

namespace YangMills.RG

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

/-- The Hessian used by the radial Taylor construction is definitionally
the derivative of the first derivative; the two literal CMP102
differentiation theorems identify it with the reconstructed second field
derivative. -/
theorem
    cmp116FDerivHessian_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
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
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    cmp116FDerivHessian
        (fun X =>
          cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ V₀ P T Δπ J X Y)
        A =
      cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J A Y := by
  let f : FineField M Q Nc → ℝ := fun X =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ V₀ P T Δπ J X Y
  let df : FineField M Q Nc →
      FineField M Q Nc →L[ℝ] ℝ := fun X =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ V₀ P T Δπ J X Y
  have hfirst : fderiv ℝ f = df := by
    funext X
    exact
      (cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_hasFDerivAt
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmall layerWord choice
        D D₃ V₀ P T Δπ J X Y hD hD₃ hV₀).fderiv
  have hsecond :
      fderiv ℝ df A =
        cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J A Y :=
    (cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative_hasFDerivAt
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ V₀ P T Δπ J A Y
      hD hD₃ hV₀).fderiv
  change fderiv ℝ (fderiv ℝ f) A = _
  rw [hfirst]
  exact hsecond

/-- Exact source-facing equation-(1.43) frontier for the literal CMP102
domain contribution.  A bound on the already reconstructed second field
derivative passes to its radial operator with no loss. -/
theorem
    abs_inner_cmp102Eq80PhysicalFineHeadTailDomainFTCRadialOperator_le_eq143
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
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
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J B A A' : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (C3 epsilon1 : ℝ) (Msource : ℕ)
    (C2 kappa1 domainDist : ℝ) (domainCard : ℕ)
    (hsecond : ∀ t ∈ Icc (0 : ℝ) 1,
      |(cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J (t • B) Y) A' A| ≤
        cmp116Eq143QMajorant C3 epsilon1 Msource C2 kappa1
          domainDist domainCard) :
    |inner ℝ A
        (cmp102Eq80PhysicalFineHeadTailDomainFTCRadialOperator
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          sigma hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J Y hD hD₃ hV₀ B A')| ≤
      cmp116Eq143QMajorant C3 epsilon1 Msource C2 kappa1
        domainDist domainCard := by
  let f : FineField M Q Nc → ℝ := fun X =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ V₀ P T Δπ J X Y
  have hf : ContDiff ℝ 2 f :=
    contDiff_two_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J Y hD hD₃ hV₀
  apply abs_inner_cmp116RadialTaylorOperator_le_of_hessian
    f B A A' hf
    (cmp116Eq143QMajorant C3 epsilon1 Msource C2 kappa1
      domainDist domainCard)
  intro t ht
  rw [
    cmp116FDerivHessian_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J (t • B) Y hD hD₃ hV₀]
  exact hsecond t ht

end

end YangMills.RG

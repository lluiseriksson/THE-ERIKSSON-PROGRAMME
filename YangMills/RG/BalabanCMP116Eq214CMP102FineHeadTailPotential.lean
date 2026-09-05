/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCRadial
import YangMills.RG.BalabanCMP116Eq214PhysicalContourPotential

/-!
# Installing the literal CMP102 fine-head-tail contribution in CMP116

The reconstructed CMP102 contribution attached to one physical domain is a
real `C²` function of the fine fluctuation field.  Its source normalization
identifies it exactly with the radial quadratic term required by the
equation-(1.42) potential slot.

This module performs the first source-faithful CMP102-to-CMP116 installation:

* a `Fin nY` family of physical domains selects the CMP102 radial operators;
* each equation-(1.42) potential term, with zero residual, is proved equal to
  the corresponding literal CMP102 contribution;
* the finite complex `tau` sum and its Gaussian-coordinate realization are
  identified with the same contributions;
* an existing contour density can have its `potential` field replaced by
  this literal family.

The module does not construct the initial contour density, does not identify
the full `interactionExponent` (which also contains the `R₂` correction), and
does not assume or prove equations (1.36), (1.43), (2.20), or `hprofile`.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators RealInnerProductSpace

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

/-- The literal CMP102 radial operator reindexed by the finite family of
source domains used by the CMP116 `tau` contour.  It is constant in the
external CMP116 `sigma`, spectator and fluctuation fields; those arguments
belong to the contour installer, not to this physical domain coefficient. -/
noncomputable def
    cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily
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
  fun i B =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCRadialOperator
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      weakening hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J (domain i) hD hD₃ hV₀ B

/-- One equation-(1.42) term built from the CMP102 radial operator and zero
residual is exactly the literal reconstructed CMP102 domain contribution. -/
theorem
    cmp116Eq142PhysicalPotentialTerm_eq_cmp102Eq80FineHeadTailDomainFTCContribution
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
        (cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain)
        (fun _ _ => 0) i B =
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        weakening layerWord choice D D₃ V₀ P T Δπ J B (domain i) := by
  simpa [
    cmp116Eq142PhysicalPotentialTerm,
    cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily] using
    (cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_eq_radial
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      weakening hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J B (domain i)
      hD hD₃ hV₀ hD0 hD₃0 hV₀0 hD₃' hV₀').symm

/-- The complex `tau`-weighted CMP116 potential built from the radial family
is exactly the finite sum of literal CMP102 domain contributions. -/
theorem
    cmp116Eq214PhysicalComplexTauPotential_cmp102FineHeadTail_eq
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
    (Dset : Finset (Fin nY))
    (domain : Fin nY → Finset (FinBox 4 (2 * Q)))
    (tau : Fin nY → ℂ) (B : FineField M Q Nc) :
    cmp116Eq214PhysicalComplexTauPotential Dset tau
        (cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain)
        (fun _ _ => 0) B =
      ∑ i ∈ Dset, tau i *
        (cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          weakening layerWord choice D D₃ V₀ P T Δπ J B (domain i) : ℂ) := by
  unfold cmp116Eq214PhysicalComplexTauPotential
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact_mod_cast
    cmp116Eq142PhysicalPotentialTerm_eq_cmp102Eq80FineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      weakening hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J hD hD₃ hV₀
      hD0 hD₃0 hV₀0 hD₃' hV₀' domain i B

/-- Coordinate-level form of the same equality after the canonical CMP116
localization and flattening of the inner Gaussian coordinate. -/
theorem
    cmp116Eq214ComplexTauPotentialCoordinate_cmp102FineHeadTail_eq
    {M Q Nc R Δ n nY L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    [NeZero L] [NeZero lieDim]
    (Dict :
      PhysicalGaugeCMP116Dictionary
        4 (M * (2 * Q)) Nc 4 L lieDim)
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
    (Dset : Finset (Fin nY))
    (domain : Fin nY → Finset (FinBox 4 (2 * Q)))
    (tau : Fin nY → ℂ)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (b : CMP116Eq214GaussianCoordinate (Cube 4 L) lieDim) :
    Dict.cmp116Eq214ComplexTauPotentialCoordinate Dset tau
        (cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain)
        (fun _ _ => 0) Z0 b =
      ∑ i ∈ Dset, tau i *
        (cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          weakening layerWord choice D D₃ V₀ P T Δπ J
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
            (Dict.flatPhysicalLinearIsometryEquiv (WithLp.toLp 2 b)))
          (domain i) : ℂ) := by
  unfold PhysicalGaugeCMP116Dictionary.cmp116Eq214ComplexTauPotentialCoordinate
  exact
    cmp116Eq214PhysicalComplexTauPotential_cmp102FineHeadTail_eq
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      weakening hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J hD hD₃ hV₀
      hD0 hD₃0 hV₀0 hD₃' hV₀' Dset domain tau
      (physicalBondProjection
        (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
        (Dict.flatPhysicalLinearIsometryEquiv (WithLp.toLp 2 b)))

namespace CMP116Eq214PhysicalContourDensity

/-- Replace the `potential` field of an existing contour density by the
literal CMP102 fine-head-tail radial family.  The installed family is
constant in the external `sigma`, spectator and fluctuation fields and is
multiplied by the source `tau` coordinates by the existing contour
constructor. -/
noncomputable def withCMP102FineHeadTailPotential
    {M Q Nc R Δ n nDelta nY L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube 4 L) Site Psi Phi E lieDim)
    (Dict :
      PhysicalGaugeCMP116Dictionary
        4 (M * (2 * Q)) Nc 4 L lieDim)
    (Dset : Finset (Fin nY))
    (domain : Fin nY → Finset (FinBox 4 (2 * Q)))
    (Z0 : Finset (FinBox 4 (2 * Q)))
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
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube 4 L) Site Psi Phi E lieDim :=
  C.withPhysicalComplexTauPotential Dict Dset
    (fun _sigma _psi _phi =>
      cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        weakening hRweak hcap hsmall layerWord choice
        D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain)
    (fun _sigma _psi _phi _i _B => 0) Z0

@[simp]
theorem withCMP102FineHeadTailPotential_potential
    {M Q Nc R Δ n nDelta nY L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube 4 L) Site Psi Phi E lieDim)
    (Dict :
      PhysicalGaugeCMP116Dictionary
        4 (M * (2 * Q)) Nc 4 L lieDim)
    (Dset : Finset (Fin nY))
    (domain : Fin nY → Finset (FinBox 4 (2 * Q)))
    (Z0 : Finset (FinBox 4 (2 * Q)))
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
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (b : CMP116Eq214GaussianCoordinate (Cube 4 L) lieDim) :
    (C.withCMP102FineHeadTailPotential Dict Dset domain Z0
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        weakening hRweak hcap hsmall layerWord choice
        D D₃ V₀ P T Δπ J hD hD₃ hV₀).potential
        sigma tau psi phi b =
      Dict.cmp116Eq214ComplexTauPotentialCoordinate Dset tau
        (cmp102Eq80PhysicalFineHeadTailDomainQuadraticFamily
          anchor K hc hmass hK baseCoarseCovariance
          hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
          weakening hRweak hcap hsmall layerWord choice
          D D₃ V₀ P T Δπ J hD hD₃ hV₀ domain)
        (fun _ _ => 0) Z0 b := by
  rfl

@[simp]
theorem withCMP102FineHeadTailPotential_potential_zero
    {M Q Nc R Δ n nDelta nY L lieDim : ℕ}
    {Site E : Type*} {Psi Phi : Site → Type*}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    [NeZero L] [NeZero lieDim] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube 4 L) Site Psi Phi E lieDim)
    (Dict :
      PhysicalGaugeCMP116Dictionary
        4 (M * (2 * Q)) Nc 4 L lieDim)
    (Dset : Finset (Fin nY))
    (domain : Fin nY → Finset (FinBox 4 (2 * Q)))
    (Z0 : Finset (FinBox 4 (2 * Q)))
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
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (b : CMP116Eq214GaussianCoordinate (Cube 4 L) lieDim) :
    (C.withCMP102FineHeadTailPotential Dict Dset domain Z0
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        weakening hRweak hcap hsmall layerWord choice
        D D₃ V₀ P T Δπ J hD hD₃ hV₀).potential
        0 0 psi phi b = 0 := by
  exact
    (C.withCMP102FineHeadTailPotential Dict Dset domain Z0
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      weakening hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J hD hD₃ hV₀).potential_zero psi phi b

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG

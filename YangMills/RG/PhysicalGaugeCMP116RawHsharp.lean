/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
import YangMills.RG.AppendixFHsharpLeafSource

/-!
# Raw-source CMP116 activities as an Appendix-F/H# input

This file contains only source-independent plumbing.  It packages the
scale-indexed CMP116 family constructed from the raw-source compatibility
record and shows that the existing source-measurable H# endpoint accepts its
`hraw` premise directly.

No Yang--Mills source estimate, Gaussian pushforward, covariance-root
localization, fluctuation-integrability theorem, physical remainder identity,
or `hRpoly` theorem is proved here.
-/

namespace YangMills.RG

open MeasureTheory
open scoped RealInnerProductSpace

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- The scale-indexed CMP116 localized family canonically transported from
raw-source physical activity packages. -/
noncomputable def physicalGaugeCMP116RawSourceScaleFamily
    {β : Type*}
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _ _, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ _ _, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc)
    (precision covariance root :
      ∀ _ _,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      ∀ _ _, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (covNormBound rootNormBound : ∀ _ _, ℝ)
    (covWeight rootWeight :
      ∀ _ _, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
    (physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc)
    (physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N))
    (weight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ)
    (amplitude : ℕ → ℕ → ℝ)
    (kappa : ℝ)
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop)
    (hroot :
      ∀ t k,
        PhysicalLocalizedCovarianceRootCertificate
          (precision t k) (covariance t k) (root t k)
          (covNormBound t k) (rootNormBound t k)
          (covWeight t k) (rootWeight t k))
    (hsource :
      ∀ t k,
        PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
          (D t k) (root t k) (physicalGaussian t k)
          (physicalActivity t k) (weight t k) (amplitude t k)
          (rootLocalization t k)
          (wilsonHessianIdentification t k)
          (localActivityConstruction t k))
    (hspectator :
      ∀ t k X, (physicalActivity t k X).spectatorSupport ⊆
        physicalActiveSupport t k X)
    (hfluctuation :
      ∀ t k X, (physicalActivity t k X).fluctuationSupport ⊆
        physicalActiveSupport t k X)
    (hamplitude_nonneg : ∀ t k, 0 ≤ amplitude t k)
    (hweight : ∀ t k X, 0 ≤ weight t k X)
    (activity_stronglyMeasurable :
      ∀ t k X, ∀ ψ : ∀ _ : Cube d L, β,
        StronglyMeasurable
          (fun ξ : CMP116FluctuationField d L lieDim =>
            ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
              (Ψ := fun _ : Cube d L => β)
              (D t k) (fun X : OmegaPolymerType HF (z t k) => X)
              (spectatorPull t k)).activity
                (physicalActivity t k) X).globalEval ψ ξ))
    (activeSupport_subset_Omega :
      ∀ t k X, physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (D t k).siteMap.Omega)
    (activeSupport_subset_skeleton :
      ∀ t k X, X ∈ Λ t k →
        physicalActiveSupport t k X ⊆
          (D t k).physicalBondsOfCells (skeleton HF X.val))
    (weight_domination :
      ∀ t k X, X ∈ Λ t k →
        weight t k X ≤ appendixFHoleExpWeight HF kappa X.val) :
    ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => β) (OmegaPolymerType HF (z t k)) :=
  fun t k =>
    (physicalGaugeCMP116ActivityTransport_of_cmp116RawSource
      (lieDim := lieDim) (Ψ := fun _ : Cube d L => β)
      (HF := HF) (z := z t k) (Λ := Λ t k)
      (precision := precision t k)
      (covariance := covariance t k)
      (root := root t k)
      (covNormBound := covNormBound t k)
      (rootNormBound := rootNormBound t k)
      (H0 := amplitude t k) (κ := kappa)
      (covWeight := covWeight t k)
      (rootWeight := rootWeight t k)
      (physicalActivity := physicalActivity t k)
      (physicalActiveSupport := physicalActiveSupport t k)
      (weight := weight t k)
      (D := D t k)
      (physicalGaussian := physicalGaussian t k)
      (rootLocalization := rootLocalization t k)
      (wilsonHessianIdentification := wilsonHessianIdentification t k)
      (localActivityConstruction := localActivityConstruction t k)
      (spectatorPull t k) (hroot t k) (hsource t k)
      (hspectator t k) (hfluctuation t k)
      (hamplitude_nonneg t k) (hweight t k)
      (activity_stronglyMeasurable t k)
      (activeSupport_subset_Omega t k)
      (activeSupport_subset_skeleton t k)
      (weight_domination t k)).family

/-- The raw-source scale family feeds the existing source-measurable H# endpoint.

The theorem only discharges the `hraw` premise from the raw-source transport.
All analytic H# inputs remain explicit: the rooted remainder identity, the
probability law, smallness/profile conditions, and hole geometry are still
hypotheses. -/
theorem singleScaleUVDecay_of_cmp116RawSource_hsharp
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _ _, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ _ _, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc)
    (precision covariance root :
      ∀ _ _,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      ∀ _ _, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (covNormBound rootNormBound : ∀ _ _, ℝ)
    (covWeight rootWeight :
      ∀ _ _, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
    (physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc)
    (physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N))
    (weight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ)
    (ν : ℕ → ℕ → Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (amplitude : ℕ → ℕ → ℝ)
    {C Hbar c0 kappa kappa0 : ℝ}
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop)
    (hroot :
      ∀ t k,
        PhysicalLocalizedCovarianceRootCertificate
          (precision t k) (covariance t k) (root t k)
          (covNormBound t k) (rootNormBound t k)
          (covWeight t k) (rootWeight t k))
    (hsource :
      ∀ t k,
        PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
          (D t k) (root t k) (physicalGaussian t k)
          (physicalActivity t k) (weight t k) (amplitude t k)
          (rootLocalization t k)
          (wilsonHessianIdentification t k)
          (localActivityConstruction t k))
    (hspectator :
      ∀ t k X, (physicalActivity t k X).spectatorSupport ⊆
        physicalActiveSupport t k X)
    (hfluctuation :
      ∀ t k X, (physicalActivity t k X).fluctuationSupport ⊆
        physicalActiveSupport t k X)
    (hamplitude_nonneg : ∀ t k, 0 ≤ amplitude t k)
    (hamplitude_one : ∀ t k, amplitude t k ≤ 1)
    (hweight : ∀ t k X, 0 ≤ weight t k X)
    (activity_stronglyMeasurable :
      ∀ t k X, ∀ ψ : ∀ _ : Cube d L, β,
        StronglyMeasurable
          (fun ξ : CMP116FluctuationField d L lieDim =>
            ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
              (Ψ := fun _ : Cube d L => β)
              (D t k) (fun X : OmegaPolymerType HF (z t k) => X)
              (spectatorPull t k)).activity
                (physicalActivity t k) X).globalEval ψ ξ))
    (activeSupport_subset_Omega :
      ∀ t k X, physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (D t k).siteMap.Omega)
    (activeSupport_subset_skeleton :
      ∀ t k X, X ∈ Λ t k →
        physicalActiveSupport t k X ⊆
          (D t k).physicalBondsOfCells (skeleton HF X.val))
    (weight_domination :
      ∀ t k X, X ∈ Λ t k →
        weight t k X ≤ appendixFHoleExpWeight HF kappa X.val)
    (hC : 0 ≤ C)
    (hHbar : 0 ≤ Hbar)
    (hg : ∀ k, 0 ≤ g k)
    (hkappa : 4 * kappa0 + 3 ≤ kappa)
    (hkappa0 : 0 < kappa0)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k)
                ((physicalGaugeCMP116RawSourceScaleFamily
                  Λ D spectatorPull precision covariance
                  root physicalGaussian covNormBound rootNormBound covWeight
                  rootWeight physicalActivity physicalActiveSupport weight
                  amplitude kappa rootLocalization
                  wilsonHessianIdentification localActivityConstruction
                  hroot hsource hspectator hfluctuation hamplitude_nonneg
                  hweight activity_stronglyMeasurable
                  activeSupport_subset_Omega activeSupport_subset_skeleton
                  weight_domination) t k)
                (ν t k) P.val.val))
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H ∈ HF.holes, H.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1)
    (hhalf :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d kappa0 *
            (2 * amplitude t k *
              appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2)
    (hprofile :
      ∀ t k,
        4 * appendixFSecondUrsellMomentConstant d kappa0 *
            amplitude t k * appendixFHoleRootSumConstant d kappa0 ≤
          C * Hbar * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0) :
    SingleScaleUVDecay Rsc g
      ((C * Hbar) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)))⁻¹)
      c0 kappa0 := by
  let F :=
    physicalGaugeCMP116RawSourceScaleFamily
      (lieDim := lieDim) Λ D spectatorPull precision covariance root
      physicalGaussian covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport weight amplitude kappa
      rootLocalization wilsonHessianIdentification localActivityConstruction
      hroot hsource hspectator hfluctuation hamplitude_nonneg hweight
      activity_stronglyMeasurable activeSupport_subset_Omega
      activeSupport_subset_skeleton weight_domination
  refine
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_sourceMeasurable
      (d := d) (L := L) (lieDim := lieDim) (β := β)
      (C := C) (Hbar := Hbar) (c₀ := c0)
      (κ := kappa) (κ₀ := kappa0)
      HF zCarrier r z Λ F ν Rsc g amplitude
      hC hHbar hg hkappa hkappa0 ?_ hν hamplitude_nonneg
      hamplitude_one ?_ hdisj hnoedges hholes_ne hCq hhalf hprofile
  · intro t k
    simpa [F] using hR t k
  · intro t k ψ φ X hX
    simpa [F, physicalGaugeCMP116RawSourceScaleFamily] using
      (balabanCMP116_hraw_of_cmp116RawSource
        (lieDim := lieDim) (Ψ := fun _ : Cube d L => β)
        (HF := HF) (z := z t k) (Λ := Λ t k)
        (precision := precision t k) (covariance := covariance t k)
        (root := root t k) (covNormBound := covNormBound t k)
        (rootNormBound := rootNormBound t k)
        (H0 := amplitude t k) (κ := kappa)
        (covWeight := covWeight t k) (rootWeight := rootWeight t k)
        (physicalActivity := physicalActivity t k)
        (physicalActiveSupport := physicalActiveSupport t k)
        (weight := weight t k) (D := D t k)
        (physicalGaussian := physicalGaussian t k)
        (rootLocalization := rootLocalization t k)
        (wilsonHessianIdentification := wilsonHessianIdentification t k)
        (localActivityConstruction := localActivityConstruction t k)
        (spectatorPull t k) (hroot t k) (hsource t k)
        (hspectator t k) (hfluctuation t k)
        (hamplitude_nonneg t k) (hweight t k)
        (activity_stronglyMeasurable t k)
        (activeSupport_subset_Omega t k)
        (activeSupport_subset_skeleton t k)
        (weight_domination t k) ψ φ X hX)

end YangMills.RG

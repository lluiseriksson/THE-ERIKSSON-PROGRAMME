/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeCMP116RawM3
import YangMills.RG.BalabanCMP116Lemma3ScaleFamily

/-!
# Balaban CMP116 source theorem target

This file states the source-facing theorem target for the CMP116 raw-source M3
frontier.  It splits the current opaque raw-source package into the five
source facts it already contains: Gaussian pushforward, covariance-root
localization, Wilson-Hessian identification, local physical activity
construction, and raw pointwise decay.

The named proposition `BalabanCMP116SourceTheorem` is discharged below by pure
record packaging from the unfolded source-assumption record to the existing
`CMP116RawSourceM3Frontier`.  No Gaussian pushforward, localization,
Wilson-Hessian, local-activity, raw-decay, or rooted-remainder source fact is
proved here.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

namespace PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses

/-- Reassemble the existing raw-source compatibility package from its five
explicit source components.

This is pure record packaging.  It proves no Gaussian pushforward,
root-localization, Wilson-Hessian, local-activity, or raw-decay source fact. -/
def of_components
    {ι : Type*}
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {physicalActivity :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {weight : ι → ℝ}
    {H0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (gaussian_pushforward :
      (balabanCMP116Dmu0 (Cube d L) lieDim).map
          (D.gaussianRootMap root) =
        physicalGaussian)
    (root_localization : rootLocalization)
    (wilson_hessian_identification : wilsonHessianIdentification)
    (local_activity_construction : localActivityConstruction)
    (raw_pointwise_decay :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        ‖(physicalActivity X).globalEval ψ φ‖ ≤ H0 * weight X) :
    PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
      D root physicalGaussian physicalActivity weight H0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction where
  gaussian_pushforward := gaussian_pushforward
  root_localization := root_localization
  wilson_hessian_identification := wilson_hessian_identification
  local_activity_construction := local_activity_construction
  raw_pointwise_decay := raw_pointwise_decay

end PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses

/-- Source-facing CMP116 assumptions with the current `raw_source` package
unfolded into individually auditable source fields.

The truncation schedule is intentionally absent, matching
`CMP116RawSourceM3Frontier`: no source field constrains it. -/
structure BalabanCMP116SourceAssumptions
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc)
    (precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ)
    (covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
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
    (covIR : ℕ → ℝ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (amplitude : ℕ → ℕ → ℝ)
    (C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ)
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop) : Prop where

  covariance_root_certificate :
    ∀ t k,
      PhysicalLocalizedCovarianceRootCertificate
        (precision t k) (covariance t k) (root t k)
        (covNormBound t k) (rootNormBound t k)
        (covWeight t k) (rootWeight t k)

  root_localization :
    ∀ t k, rootLocalization t k

  gaussian_pushforward :
    ∀ t k,
      (balabanCMP116Dmu0 (Cube d L) lieDim).map
          ((D t k).gaussianRootMap (root t k)) =
        physicalGaussian t k

  wilson_hessian_identification :
    ∀ t k, wilsonHessianIdentification t k

  local_physical_activity_construction :
    ∀ t k, localActivityConstruction t k

  spectator_support_subset :
    ∀ t k X,
      (physicalActivity t k X).spectatorSupport ⊆
        physicalActiveSupport t k X

  fluctuation_support_subset :
    ∀ t k X,
      (physicalActivity t k X).fluctuationSupport ⊆
        physicalActiveSupport t k X

  activity_stronglyMeasurable :
    ∀ t k X, ∀ ψ : ∀ _ : Cube d L, β,
      StronglyMeasurable
        (fun ξ : CMP116FluctuationField d L lieDim =>
          ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
            (Ψ := fun _ : Cube d L => β)
            (D t k)
            (fun X : OmegaPolymerType HF (z t k) => X)
            (spectatorPull t k)).activity
              (physicalActivity t k) X).globalEval ψ ξ)

  raw_pointwise_decay :
    ∀ t k X
      (ψ φ : PhysicalGaugeField dPhys N Nc),
      ‖(physicalActivity t k X).globalEval ψ φ‖ ≤
        amplitude t k * weight t k X

  amplitude_nonneg :
    ∀ t k, 0 ≤ amplitude t k

  weight_nonneg :
    ∀ t k X, 0 ≤ weight t k X

  active_support_subset_omega :
    ∀ t k X,
      physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (D t k).siteMap.Omega

  active_support_subset_skeleton :
    ∀ t k X, X ∈ Λ t k →
      physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (skeleton HF X.val)

  weight_domination :
    ∀ t k X, X ∈ Λ t k →
      weight t k X ≤ appendixFHoleExpWeight HF kappa X.val

  probability_law :
    ∀ t k, IsProbabilityMeasure (ν t k)

  holes_pairwise_disjoint :
    ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂

  no_edges_between_holes :
    noEdgesBetweenHoles (cubeAdj d L) HF.holes

  holes_nonempty :
    ∀ H ∈ HF.holes, H.Nonempty

  appendix_f_geometric_smallness :
    ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1

  rooted_hsharp_remainder_identity :
    let rawSource :=
      fun t k =>
        PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_components
          (gaussian_pushforward t k)
          (root_localization t k)
          (wilson_hessian_identification t k)
          (local_physical_activity_construction t k)
          (raw_pointwise_decay t k)
    ∀ t k,
      Rsc t k =
        ∑' P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val },
          Complex.re
            (balabanCMP116AppendixFHsharpOfIntegratedKsharp
              HF (z t k) (Λ t k)
              ((physicalGaugeCMP116RawSourceScaleFamily
                Λ D spectatorPull precision covariance root
                physicalGaussian
                covNormBound rootNormBound covWeight rootWeight
                physicalActivity physicalActiveSupport weight
                amplitude kappa
                rootLocalization
                wilsonHessianIdentification
                localActivityConstruction
                covariance_root_certificate
                rawSource
                spectator_support_subset
                fluctuation_support_subset
                amplitude_nonneg
                weight_nonneg
                activity_stronglyMeasurable
                active_support_subset_omega
                active_support_subset_skeleton
                weight_domination) t k)
              (ν t k) P.val.val)

  amplitude_le_one :
    ∀ t k, amplitude t k ≤ 1

  profile_constant_nonneg :
    0 ≤ C

  hbar_nonneg :
    0 ≤ Hbar

  kappa_margin :
    4 * kappa0 + 3 ≤ kappa

  kappa0_gt_one :
    1 < kappa0

  time_decay_positive :
    0 < c0

  half_budget :
    ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 * amplitude t k *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2

  profile_bound :
    ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          amplitude t k *
          appendixFHoleRootSumConstant d kappa0 ≤
        C * Hbar *
          Real.exp (-(c0 * (t : ℝ))) *
          g k ^ kappa0

  epsilon_positive :
    0 < ε

  beta_flow_positive :
    0 < betaFlow

  coupling_positive :
    ∀ k, 0 < g k

  coupling_small :
    ∀ k, betaFlow * g k < 1

  coupling_recursion :
    ∀ k,
      g (k + 1) =
        g k * (1 - betaFlow * g k)

  ir_bound :
    ∀ k : ℕ,
      |covIR k| ≤
        C1 * Real.exp (-(ε * (k : ℝ)))

namespace BalabanCMP116SourceAssumptions

/-- Canonical raw-source package extracted from the unfolded Balaban CMP116
source assumptions.

This is the reusable projection that later frontier constructors should use
instead of rebuilding the five-component raw-source package by hand. -/
def rawSource
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    {zCarrier : Finset (Cube d L) → ℂ}
    {r : Cube d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))}
    {D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc}
    {precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ}
    {covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N)}
    {weight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {ν : ℕ → ℕ → Measure β}
    {covIR : ℕ → ℝ}
    {Rsc : ℕ → ℕ → ℝ}
    {g : ℕ → ℝ}
    {amplitude : ℕ → ℕ → ℝ}
    {C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (source :
      BalabanCMP116SourceAssumptions
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport weight
        ν covIR Rsc g amplitude
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k) (root t k) (physicalGaussian t k)
        (physicalActivity t k) (weight t k) (amplitude t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  fun t k =>
    PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_components
      (source.gaussian_pushforward t k)
      (source.root_localization t k)
      (source.wilson_hessian_identification t k)
      (source.local_physical_activity_construction t k)
      (source.raw_pointwise_decay t k)

/-- The rooted H# identity from the source-assumption record, restated with the
canonical `source.rawSource` projection.

This is a projection-consistency theorem only.  It does not prove the physical
rooted remainder identity; that identity is still exactly the source field
`rooted_hsharp_remainder_identity`. -/
theorem rooted_hsharp_remainder_identity_rawSource
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    {zCarrier : Finset (Cube d L) → ℂ}
    {r : Cube d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))}
    {D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc}
    {precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ}
    {covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N)}
    {weight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {ν : ℕ → ℕ → Measure β}
    {covIR : ℕ → ℝ}
    {Rsc : ℕ → ℕ → ℝ}
    {g : ℕ → ℝ}
    {amplitude : ℕ → ℕ → ℝ}
    {C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (source :
      BalabanCMP116SourceAssumptions
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport weight
        ν covIR Rsc g amplitude
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    ∀ t k,
      Rsc t k =
        ∑' P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val },
          Complex.re
            (balabanCMP116AppendixFHsharpOfIntegratedKsharp
              HF (z t k) (Λ t k)
              ((physicalGaugeCMP116RawSourceScaleFamily
                Λ D spectatorPull precision covariance root
                physicalGaussian
                covNormBound rootNormBound covWeight rootWeight
                physicalActivity physicalActiveSupport weight
                amplitude kappa
                rootLocalization
                wilsonHessianIdentification
                localActivityConstruction
                source.covariance_root_certificate
                (BalabanCMP116SourceAssumptions.rawSource source)
                source.spectator_support_subset
                source.fluctuation_support_subset
                source.amplitude_nonneg
                source.weight_nonneg
                source.activity_stronglyMeasurable
                source.active_support_subset_omega
                source.active_support_subset_skeleton
                source.weight_domination) t k)
              (ν t k) P.val.val) := by
  simpa [rawSource] using source.rooted_hsharp_remainder_identity

end BalabanCMP116SourceAssumptions

/-- Source-facing CMP116 assumptions where the raw pointwise estimate is
replaced by the canonical CMP116 Lemma 3 scale-family estimate.

All non-raw source obligations from `BalabanCMP116SourceAssumptions` remain
explicit.  This is a compatibility boundary: until admissible-domain transport
or zero-extension is formalized, the full scale-family estimate is a supplied
hypothesis rather than a verbatim source theorem over every repository
polymer. -/
structure BalabanCMP116Lemma3SourceAssumptions
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc)
    (precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ)
    (covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
    (physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc)
    (physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N))
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (ν : ℕ → ℕ → Measure β)
    (covIR : ℕ → ℝ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ)
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop) : Prop where

  covariance_root_certificate :
    ∀ t k,
      PhysicalLocalizedCovarianceRootCertificate
        (precision t k) (covariance t k) (root t k)
        (covNormBound t k) (rootNormBound t k)
        (covWeight t k) (rootWeight t k)

  root_localization :
    ∀ t k, rootLocalization t k

  gaussian_pushforward :
    ∀ t k,
      (balabanCMP116Dmu0 (Cube d L) lieDim).map
          ((D t k).gaussianRootMap (root t k)) =
        physicalGaussian t k

  wilson_hessian_identification :
    ∀ t k, wilsonHessianIdentification t k

  local_physical_activity_construction :
    ∀ t k, localActivityConstruction t k

  spectator_support_subset :
    ∀ t k X,
      (physicalActivity t k X).spectatorSupport ⊆
        physicalActiveSupport t k X

  fluctuation_support_subset :
    ∀ t k X,
      (physicalActivity t k X).fluctuationSupport ⊆
        physicalActiveSupport t k X

  activity_stronglyMeasurable :
    ∀ t k X, ∀ ψ : ∀ _ : Cube d L, β,
      StronglyMeasurable
        (fun ξ : CMP116FluctuationField d L lieDim =>
          ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
            (Ψ := fun _ : Cube d L => β)
            (D t k)
            (fun X : OmegaPolymerType HF (z t k) => X)
            (spectatorPull t k)).activity
              (physicalActivity t k) X).globalEval ψ ξ)

  lemma3_activity_estimate :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity sourceMetric
      blockScale C3 epsilon1 delta kappaSource

  amplitude_nonneg :
    ∀ t k, 0 ≤ cmp116Lemma3ScaleAmplitude C3 epsilon1 t k

  active_support_subset_omega :
    ∀ t k X,
      physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (D t k).siteMap.Omega

  active_support_subset_skeleton :
    ∀ t k X, X ∈ Λ t k →
      physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (skeleton HF X.val)

  weight_domination :
    ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val

  probability_law :
    ∀ t k, IsProbabilityMeasure (ν t k)

  holes_pairwise_disjoint :
    ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂

  no_edges_between_holes :
    noEdgesBetweenHoles (cubeAdj d L) HF.holes

  holes_nonempty :
    ∀ H ∈ HF.holes, H.Nonempty

  appendix_f_geometric_smallness :
    ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1

  rooted_hsharp_remainder_identity :
    let rawSource :=
      rawSource_of_lemma3ActivityEstimate
        gaussian_pushforward
        root_localization
        wilson_hessian_identification
        local_physical_activity_construction
        lemma3_activity_estimate
    ∀ t k,
      Rsc t k =
        ∑' P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val },
          Complex.re
            (balabanCMP116AppendixFHsharpOfIntegratedKsharp
              HF (z t k) (Λ t k)
              ((physicalGaugeCMP116RawSourceScaleFamily
                Λ D spectatorPull precision covariance root
                physicalGaussian
                covNormBound rootNormBound covWeight rootWeight
                physicalActivity physicalActiveSupport
                (cmp116Lemma3ScaleWeight
                  sourceMetric blockScale delta kappaSource)
                (cmp116Lemma3ScaleAmplitude C3 epsilon1)
                kappa
                rootLocalization
                wilsonHessianIdentification
                localActivityConstruction
                covariance_root_certificate
                rawSource
                spectator_support_subset
                fluctuation_support_subset
                amplitude_nonneg
                (cmp116Lemma3ScaleWeight_nonneg
                  sourceMetric blockScale delta kappaSource)
                activity_stronglyMeasurable
                active_support_subset_omega
                active_support_subset_skeleton
                weight_domination) t k)
              (ν t k) P.val.val)

  amplitude_le_one :
    ∀ t k, cmp116Lemma3ScaleAmplitude C3 epsilon1 t k ≤ 1

  profile_constant_nonneg :
    0 ≤ C

  hbar_nonneg :
    0 ≤ Hbar

  kappa_margin :
    4 * kappa0 + 3 ≤ kappa

  kappa0_gt_one :
    1 < kappa0

  time_decay_positive :
    0 < c0

  half_budget :
    ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 * cmp116Lemma3ScaleAmplitude C3 epsilon1 t k *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2

  profile_bound :
    ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          cmp116Lemma3ScaleAmplitude C3 epsilon1 t k *
          appendixFHoleRootSumConstant d kappa0 ≤
        C * Hbar *
          Real.exp (-(c0 * (t : ℝ))) *
          g k ^ kappa0

  epsilon_positive :
    0 < ε

  beta_flow_positive :
    0 < betaFlow

  coupling_positive :
    ∀ k, 0 < g k

  coupling_small :
    ∀ k, betaFlow * g k < 1

  coupling_recursion :
    ∀ k,
      g (k + 1) =
        g k * (1 - betaFlow * g k)

  ir_bound :
    ∀ k : ℕ,
      |covIR k| ≤
        C1 * Real.exp (-(ε * (k : ℝ)))

namespace BalabanCMP116Lemma3SourceAssumptions

/-- Canonical raw-source package extracted from Lemma-3 source assumptions. -/
def rawSource
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    {zCarrier : Finset (Cube d L) → ℂ}
    {r : Cube d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))}
    {D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc}
    {precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ}
    {covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N)}
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ}
    {ν : ℕ → ℕ → Measure β}
    {covIR : ℕ → ℝ}
    {Rsc : ℕ → ℕ → ℝ}
    {g : ℕ → ℝ}
    {C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (source :
      BalabanCMP116Lemma3SourceAssumptions
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport
        sourceMetric blockScale C3 epsilon1 delta kappaSource
        ν covIR Rsc g
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k) (root t k) (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k)
        (cmp116Lemma3ScaleAmplitude C3 epsilon1 t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_lemma3ActivityEstimate
    source.gaussian_pushforward
    source.root_localization
    source.wilson_hessian_identification
    source.local_physical_activity_construction
    source.lemma3_activity_estimate

/-- The rooted H# identity restated with the canonical Lemma-3 raw-source
projection. -/
theorem rooted_hsharp_remainder_identity_rawSource
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    {zCarrier : Finset (Cube d L) → ℂ}
    {r : Cube d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))}
    {D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc}
    {precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ}
    {covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N)}
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ}
    {ν : ℕ → ℕ → Measure β}
    {covIR : ℕ → ℝ}
    {Rsc : ℕ → ℕ → ℝ}
    {g : ℕ → ℝ}
    {C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (source :
      BalabanCMP116Lemma3SourceAssumptions
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport
        sourceMetric blockScale C3 epsilon1 delta kappaSource
        ν covIR Rsc g
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    ∀ t k,
      Rsc t k =
        ∑' P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val },
          Complex.re
            (balabanCMP116AppendixFHsharpOfIntegratedKsharp
              HF (z t k) (Λ t k)
              ((physicalGaugeCMP116RawSourceScaleFamily
                Λ D spectatorPull precision covariance root
                physicalGaussian
                covNormBound rootNormBound covWeight rootWeight
                physicalActivity physicalActiveSupport
                (cmp116Lemma3ScaleWeight
                  sourceMetric blockScale delta kappaSource)
                (cmp116Lemma3ScaleAmplitude C3 epsilon1)
                kappa
                rootLocalization
                wilsonHessianIdentification
                localActivityConstruction
                source.covariance_root_certificate
                (BalabanCMP116Lemma3SourceAssumptions.rawSource source)
                source.spectator_support_subset
                source.fluctuation_support_subset
                source.amplitude_nonneg
                (cmp116Lemma3ScaleWeight_nonneg
                  sourceMetric blockScale delta kappaSource)
                source.activity_stronglyMeasurable
                source.active_support_subset_omega
                source.active_support_subset_skeleton
                source.weight_domination) t k)
              (ν t k) P.val.val) := by
  simpa [rawSource] using source.rooted_hsharp_remainder_identity

end BalabanCMP116Lemma3SourceAssumptions

/-- Source-facing CMP116 assumptions where the Lemma 3 scale-family estimate is
derived from the explicit finite resummation obligations now available in Lean.

This is still a source-boundary record.  It does not prove equation (2.29), the
P-stage budget, the `Z0/Z0'` residual estimates, the complex termwise estimate,
or the activity identification.  It only replaces the monolithic
`lemma3_activity_estimate` field by the smaller named obligations consumed by
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageResidualStages`. -/
structure BalabanCMP116Lemma3ResummationSourceAssumptions
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    (ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*)
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc)
    (precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ)
    (covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
    (physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc)
    (physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N))
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (hp : ∀ _t _k : ℕ, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ)
    (pWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ)
    (z0Weight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ℝ)
    (z0PrimeWeight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ιZ0' t k → ℝ)
    (ν : ℕ → ℕ → Measure β)
    (covIR : ℕ → ℝ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ)
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop) : Prop where

  covariance_root_certificate :
    ∀ t k,
      PhysicalLocalizedCovarianceRootCertificate
        (precision t k) (covariance t k) (root t k)
        (covNormBound t k) (rootNormBound t k)
        (covWeight t k) (rootWeight t k)

  root_localization :
    ∀ t k, rootLocalization t k

  gaussian_pushforward :
    ∀ t k,
      (balabanCMP116Dmu0 (Cube d L) lieDim).map
          ((D t k).gaussianRootMap (root t k)) =
        physicalGaussian t k

  wilson_hessian_identification :
    ∀ t k, wilsonHessianIdentification t k

  local_physical_activity_construction :
    ∀ t k, localActivityConstruction t k

  spectator_support_subset :
    ∀ t k X,
      (physicalActivity t k X).spectatorSupport ⊆
        physicalActiveSupport t k X

  fluctuation_support_subset :
    ∀ t k X,
      (physicalActivity t k X).fluctuationSupport ⊆
        physicalActiveSupport t k X

  activity_stronglyMeasurable :
    ∀ t k X, ∀ ψ : ∀ _ : Cube d L, β,
      StronglyMeasurable
        (fun ξ : CMP116FluctuationField d L lieDim =>
          ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
            (Ψ := fun _ : Cube d L => β)
            (D t k)
            (fun X : OmegaPolymerType HF (z t k) => X)
            (spectatorPull t k)).activity
              (physicalActivity t k) X).globalEval ψ ξ)

  eq229_summability :
    ∀ t k,
      CMP116Eq229Summability
        (R t k).DIndex
        (DParts t k)
        (alpha6 t k)
        (hp t k).delta
        (hp t k).kappa
        (eq229Metric t k)

  p_stage_summability :
    ∀ t k,
      CMP116PStageSummability
        (R t k).DIndex
        (R t k).PIndex
        (pWeight t k)
        (fun Z D =>
          Finset.prod (DParts t k Z D)
            (cmp116Eq229Weight
              (alpha6 t k)
              (hp t k).delta
              (hp t k).kappa
              (eq229Metric t k Z)))

  z0_residual_summability :
    ∀ t k,
      CMP116Z0ResidualSummability
        (R t k).DIndex
        (R t k).PIndex
        (R t k).Z0Index
        (z0Weight t k)

  z0Prime_residual_summability :
    ∀ t k,
      CMP116Z0PrimeResidualSummability
        (R t k).DIndex
        (R t k).PIndex
        (R t k).Z0Index
        (R t k).Z0PrimeIndex
        (z0PrimeWeight t k)

  activity_identification :
    ∀ t k Z ψ φ,
      (physicalActivity t k Z).globalEval ψ φ =
        balabanCMP116H (R t k) Z ψ φ

  termwise_estimate :
    ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
      ∀ ψ φ,
        ‖(R t k).summand
            Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
          (R t k).termWeight
            Z x.1.1 x.1.2 x.2.1 x.2.2

  pWeight_nonneg :
    ∀ t k Z D, D ∈ (R t k).DIndex Z →
      ∀ P, P ∈ (R t k).PIndex Z D →
        0 ≤ pWeight t k Z D P

  z0Weight_nonneg :
    ∀ t k Z D, D ∈ (R t k).DIndex Z →
      ∀ P, P ∈ (R t k).PIndex Z D →
        ∀ Z0, Z0 ∈ (R t k).Z0Index Z D P →
          0 ≤ z0Weight t k Z D P Z0

  residual_factorization :
    ∀ t k Z D, D ∈ (R t k).DIndex Z →
      ∀ P, P ∈ (R t k).PIndex Z D →
        ∀ Z0, Z0 ∈ (R t k).Z0Index Z D P →
          ∀ Z0', Z0' ∈ (R t k).Z0PrimeIndex Z D P Z0 →
            (R t k).termWeight Z D P Z0 Z0' ≤
              (((((hp t k).C3 * (hp t k).epsilon1) *
                  balabanCMP116Lemma3Weight
                    (hp t k).blockScale
                    (hp t k).delta
                    (hp t k).kappa
                    (sourceMetric t k)
                    Z) *
                  pWeight t k Z D P) *
                z0Weight t k Z D P Z0) *
                z0PrimeWeight t k Z D P Z0 Z0'

  amplitude_nonneg :
    ∀ t k,
      0 ≤
        cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k

  active_support_subset_omega :
    ∀ t k X,
      physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (D t k).siteMap.Omega

  active_support_subset_skeleton :
    ∀ t k X, X ∈ Λ t k →
      physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (skeleton HF X.val)

  weight_domination :
    ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k X ≤
        appendixFHoleExpWeight HF kappa X.val

  probability_law :
    ∀ t k, IsProbabilityMeasure (ν t k)

  holes_pairwise_disjoint :
    ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂

  no_edges_between_holes :
    noEdgesBetweenHoles (cubeAdj d L) HF.holes

  holes_nonempty :
    ∀ H ∈ HF.holes, H.Nonempty

  appendix_f_geometric_smallness :
    ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1

  rooted_hsharp_remainder_identity :
    let lemma3_activity_estimate :=
      cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageResidualStages
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pWeight z0Weight z0PrimeWeight
        eq229_summability p_stage_summability
        z0_residual_summability z0Prime_residual_summability
        activity_identification termwise_estimate
        pWeight_nonneg z0Weight_nonneg residual_factorization
    let rawSource :=
      rawSource_of_lemma3ActivityEstimate
        gaussian_pushforward
        root_localization
        wilson_hessian_identification
        local_physical_activity_construction
        lemma3_activity_estimate
    ∀ t k,
      Rsc t k =
        ∑' P : { P : OmegaPolymerType HF zCarrier //
            r ∈ skeleton HF P.val },
          Complex.re
            (balabanCMP116AppendixFHsharpOfIntegratedKsharp
              HF (z t k) (Λ t k)
              ((physicalGaugeCMP116RawSourceScaleFamily
                Λ D spectatorPull precision covariance root
                physicalGaussian
                covNormBound rootNormBound covWeight rootWeight
                physicalActivity physicalActiveSupport
                (cmp116Lemma3ScaleWeight
                  sourceMetric
                  (fun t k => (hp t k).blockScale)
                  (fun t k => (hp t k).delta)
                  (fun t k => (hp t k).kappa))
                (cmp116Lemma3ScaleAmplitude
                  (fun t k => (hp t k).C3)
                  (fun t k => (hp t k).epsilon1))
                kappa
                rootLocalization
                wilsonHessianIdentification
                localActivityConstruction
                covariance_root_certificate
                rawSource
                spectator_support_subset
                fluctuation_support_subset
                amplitude_nonneg
                (cmp116Lemma3ScaleWeight_nonneg
                  sourceMetric
                  (fun t k => (hp t k).blockScale)
                  (fun t k => (hp t k).delta)
                  (fun t k => (hp t k).kappa))
                activity_stronglyMeasurable
                active_support_subset_omega
                active_support_subset_skeleton
                weight_domination) t k)
              (ν t k) P.val.val)

  amplitude_le_one :
    ∀ t k,
      cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k ≤ 1

  profile_constant_nonneg :
    0 ≤ C

  hbar_nonneg :
    0 ≤ Hbar

  kappa_margin :
    4 * kappa0 + 3 ≤ kappa

  kappa0_gt_one :
    1 < kappa0

  time_decay_positive :
    0 < c0

  half_budget :
    ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 *
            cmp116Lemma3ScaleAmplitude
              (fun t k => (hp t k).C3)
              (fun t k => (hp t k).epsilon1)
              t k *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2

  profile_bound :
    ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          cmp116Lemma3ScaleAmplitude
            (fun t k => (hp t k).C3)
            (fun t k => (hp t k).epsilon1)
            t k *
          appendixFHoleRootSumConstant d kappa0 ≤
        C * Hbar *
          Real.exp (-(c0 * (t : ℝ))) *
          g k ^ kappa0

  epsilon_positive :
    0 < ε

  beta_flow_positive :
    0 < betaFlow

  coupling_positive :
    ∀ k, 0 < g k

  coupling_small :
    ∀ k, betaFlow * g k < 1

  coupling_recursion :
    ∀ k,
      g (k + 1) =
        g k * (1 - betaFlow * g k)

  ir_bound :
    ∀ k : ℕ,
      |covIR k| ≤
        C1 * Real.exp (-(ε * (k : ℝ)))

namespace BalabanCMP116Lemma3ResummationSourceAssumptions

/-- The Lemma 3 scale-family estimate derived from the explicit resummation
obligations in `BalabanCMP116Lemma3ResummationSourceAssumptions`. -/
def lemma3_activity_estimate
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {zCarrier : Finset (Cube d L) → ℂ}
    {r : Cube d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))}
    {D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc}
    {precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ}
    {covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N)}
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {hp : ∀ _t _k : ℕ, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {z0Weight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ℝ}
    {z0PrimeWeight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ιZ0' t k → ℝ}
    {ν : ℕ → ℕ → Measure β}
    {covIR : ℕ → ℝ}
    {Rsc : ℕ → ℕ → ℝ}
    {g : ℕ → ℝ}
    {C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (source :
      BalabanCMP116Lemma3ResummationSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pWeight z0Weight z0PrimeWeight
        ν covIR Rsc g
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageResidualStages
    hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
    pWeight z0Weight z0PrimeWeight
    source.eq229_summability
    source.p_stage_summability
    source.z0_residual_summability
    source.z0Prime_residual_summability
    source.activity_identification
    source.termwise_estimate
    source.pWeight_nonneg
    source.z0Weight_nonneg
    source.residual_factorization

/-- Canonical raw-source package extracted from the resummation-source
assumption record. -/
def rawSource
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {zCarrier : Finset (Cube d L) → ℂ}
    {r : Cube d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))}
    {D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc}
    {precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ}
    {covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N)}
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {hp : ∀ _t _k : ℕ, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {z0Weight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ℝ}
    {z0PrimeWeight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ιZ0' t k → ℝ}
    {ν : ℕ → ℕ → Measure β}
    {covIR : ℕ → ℝ}
    {Rsc : ℕ → ℕ → ℝ}
    {g : ℕ → ℝ}
    {C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (source :
      BalabanCMP116Lemma3ResummationSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pWeight z0Weight z0PrimeWeight
        ν covIR Rsc g
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_lemma3ActivityEstimate
    source.gaussian_pushforward
    source.root_localization
    source.wilson_hessian_identification
    source.local_physical_activity_construction
    (lemma3_activity_estimate source)

/-- Package resummation-source assumptions into the existing Lemma-3 source
assumption record. -/
def to_lemma3SourceAssumptions
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {zCarrier : Finset (Cube d L) → ℂ}
    {r : Cube d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))}
    {D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc}
    {precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ}
    {covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N)}
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {hp : ∀ _t _k : ℕ, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {z0Weight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ℝ}
    {z0PrimeWeight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ιZ0' t k → ℝ}
    {ν : ℕ → ℕ → Measure β}
    {covIR : ℕ → ℝ}
    {Rsc : ℕ → ℕ → ℝ}
    {g : ℕ → ℝ}
    {C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (source :
      BalabanCMP116Lemma3ResummationSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pWeight z0Weight z0PrimeWeight
        ν covIR Rsc g
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    BalabanCMP116Lemma3SourceAssumptions
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      ν covIR Rsc g
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction where
  covariance_root_certificate := source.covariance_root_certificate
  root_localization := source.root_localization
  gaussian_pushforward := source.gaussian_pushforward
  wilson_hessian_identification := source.wilson_hessian_identification
  local_physical_activity_construction :=
    source.local_physical_activity_construction
  spectator_support_subset := source.spectator_support_subset
  fluctuation_support_subset := source.fluctuation_support_subset
  activity_stronglyMeasurable := source.activity_stronglyMeasurable
  lemma3_activity_estimate := lemma3_activity_estimate source
  amplitude_nonneg := source.amplitude_nonneg
  active_support_subset_omega := source.active_support_subset_omega
  active_support_subset_skeleton := source.active_support_subset_skeleton
  weight_domination := source.weight_domination
  probability_law := source.probability_law
  holes_pairwise_disjoint := source.holes_pairwise_disjoint
  no_edges_between_holes := source.no_edges_between_holes
  holes_nonempty := source.holes_nonempty
  appendix_f_geometric_smallness := source.appendix_f_geometric_smallness
  rooted_hsharp_remainder_identity := by
    simpa [lemma3_activity_estimate] using
      source.rooted_hsharp_remainder_identity
  amplitude_le_one := source.amplitude_le_one
  profile_constant_nonneg := source.profile_constant_nonneg
  hbar_nonneg := source.hbar_nonneg
  kappa_margin := source.kappa_margin
  kappa0_gt_one := source.kappa0_gt_one
  time_decay_positive := source.time_decay_positive
  half_budget := source.half_budget
  profile_bound := source.profile_bound
  epsilon_positive := source.epsilon_positive
  beta_flow_positive := source.beta_flow_positive
  coupling_positive := source.coupling_positive
  coupling_small := source.coupling_small
  coupling_recursion := source.coupling_recursion
  ir_bound := source.ir_bound

end BalabanCMP116Lemma3ResummationSourceAssumptions

/-- Checked target statement for the Balaban CMP116 source theorem package.

This named proposition records the implication from unfolded source assumptions
to the existing raw-source M3 frontier.  The implication is discharged below
purely structurally; every mathematical source fact remains in the premise. -/
def BalabanCMP116SourceTheorem
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc)
    (precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ)
    (covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
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
    (covIR : ℕ → ℝ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (amplitude : ℕ → ℕ → ℝ)
    (C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ)
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop) : Prop :=
  BalabanCMP116SourceAssumptions
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport weight
      ν covIR Rsc g amplitude
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction →
    CMP116RawSourceM3Frontier
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport weight
      ν covIR Rsc g amplitude
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction

section

variable
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    {zCarrier : Finset (Cube d L) → ℂ}
    {r : Cube d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))}
    {D : ∀ _t _k : ℕ, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {spectatorPull :
      ∀ _t _k : ℕ, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc}
    {precision covariance root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ, Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {covNormBound rootNormBound : ∀ _t _k : ℕ, ℝ}
    {covWeight rootWeight :
      ∀ _t _k : ℕ, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N)}
    {weight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {ν : ℕ → ℕ → Measure β}
    {covIR : ℕ → ℝ}
    {Rsc : ℕ → ℕ → ℝ}
    {g : ℕ → ℝ}
    {amplitude : ℕ → ℕ → ℝ}
    {C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}

/-- Package the unfolded Balaban source assumptions into the existing
raw-source M3 frontier.

This proves no source field.  It only reassembles records, combining the five
unfolded source fields into `raw_source` through the canonical
`BalabanCMP116SourceAssumptions.rawSource` projection. -/
def CMP116RawSourceM3Frontier.of_balabanSourceAssumptions
    (h :
      BalabanCMP116SourceAssumptions
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport weight
        ν covIR Rsc g amplitude
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    CMP116RawSourceM3Frontier
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport weight
      ν covIR Rsc g amplitude
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction where
  covariance_root_certificate := h.covariance_root_certificate
  raw_source := BalabanCMP116SourceAssumptions.rawSource h
  spectator_support_subset := h.spectator_support_subset
  fluctuation_support_subset := h.fluctuation_support_subset
  weight_nonneg := h.weight_nonneg
  active_support_subset_omega := h.active_support_subset_omega
  active_support_subset_skeleton := h.active_support_subset_skeleton
  weight_domination := h.weight_domination
  holes_pairwise_disjoint := h.holes_pairwise_disjoint
  no_edges_between_holes := h.no_edges_between_holes
  holes_nonempty := h.holes_nonempty
  appendix_f_geometric_smallness := h.appendix_f_geometric_smallness
  activity_stronglyMeasurable := h.activity_stronglyMeasurable
  probability_law := h.probability_law
  amplitude_nonneg := h.amplitude_nonneg
  amplitude_le_one := h.amplitude_le_one
  profile_constant_nonneg := h.profile_constant_nonneg
  hbar_nonneg := h.hbar_nonneg
  kappa_margin := h.kappa_margin
  kappa0_gt_one := h.kappa0_gt_one
  coupling_positive := h.coupling_positive
  half_budget := h.half_budget
  profile_bound := h.profile_bound
  epsilon_positive := h.epsilon_positive
  time_decay_positive := h.time_decay_positive
  beta_flow_positive := h.beta_flow_positive
  coupling_small := h.coupling_small
  coupling_recursion := h.coupling_recursion
  ir_bound := h.ir_bound
  rooted_hsharp_remainder_identity :=
    BalabanCMP116SourceAssumptions.rooted_hsharp_remainder_identity_rawSource h

/-- Package Lemma-3 source assumptions into the existing raw-source M3
frontier.

This is the parallel constructor to
`CMP116RawSourceM3Frontier.of_balabanSourceAssumptions`.  It replaces the raw
pointwise source field by the canonical Lemma 3 scale-family estimate and
derives weight nonnegativity from the exponential weight.  All support,
measurability, geometry, H#, marginal-flow, and IR fields remain explicit. -/
def CMP116RawSourceM3Frontier.of_lemma3SourceAssumptions
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ}
    (h :
      BalabanCMP116Lemma3SourceAssumptions
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport
        sourceMetric blockScale C3 epsilon1 delta kappaSource
        ν covIR Rsc g
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    CMP116RawSourceM3Frontier
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport
      (cmp116Lemma3ScaleWeight sourceMetric blockScale delta kappaSource)
      ν covIR Rsc g
      (cmp116Lemma3ScaleAmplitude C3 epsilon1)
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction where
  covariance_root_certificate := h.covariance_root_certificate
  raw_source := BalabanCMP116Lemma3SourceAssumptions.rawSource h
  spectator_support_subset := h.spectator_support_subset
  fluctuation_support_subset := h.fluctuation_support_subset
  weight_nonneg :=
    cmp116Lemma3ScaleWeight_nonneg
      sourceMetric blockScale delta kappaSource
  active_support_subset_omega := h.active_support_subset_omega
  active_support_subset_skeleton := h.active_support_subset_skeleton
  weight_domination := h.weight_domination
  holes_pairwise_disjoint := h.holes_pairwise_disjoint
  no_edges_between_holes := h.no_edges_between_holes
  holes_nonempty := h.holes_nonempty
  appendix_f_geometric_smallness := h.appendix_f_geometric_smallness
  activity_stronglyMeasurable := h.activity_stronglyMeasurable
  probability_law := h.probability_law
  amplitude_nonneg := h.amplitude_nonneg
  amplitude_le_one := h.amplitude_le_one
  profile_constant_nonneg := h.profile_constant_nonneg
  hbar_nonneg := h.hbar_nonneg
  kappa_margin := h.kappa_margin
  kappa0_gt_one := h.kappa0_gt_one
  coupling_positive := h.coupling_positive
  half_budget := h.half_budget
  profile_bound := h.profile_bound
  epsilon_positive := h.epsilon_positive
  time_decay_positive := h.time_decay_positive
  beta_flow_positive := h.beta_flow_positive
  coupling_small := h.coupling_small
  coupling_recursion := h.coupling_recursion
  ir_bound := h.ir_bound
  rooted_hsharp_remainder_identity :=
    BalabanCMP116Lemma3SourceAssumptions.rooted_hsharp_remainder_identity_rawSource h

/-- Package resummation-source assumptions into the existing raw-source M3
frontier.

This is the constructor parallel to
`CMP116RawSourceM3Frontier.of_lemma3SourceAssumptions`, with the monolithic
Lemma 3 scale-family estimate replaced by the explicit Eq. (2.29), P-stage,
and fixed-`P` residual-stage obligations carried by
`BalabanCMP116Lemma3ResummationSourceAssumptions`. -/
def CMP116RawSourceM3Frontier.of_lemma3ResummationSourceAssumptions
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {hp : ∀ _t _k : ℕ, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {z0Weight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ℝ}
    {z0PrimeWeight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ιZ0' t k → ℝ}
    (h :
      BalabanCMP116Lemma3ResummationSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pWeight z0Weight z0PrimeWeight
        ν covIR Rsc g
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    CMP116RawSourceM3Frontier
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport
      (cmp116Lemma3ScaleWeight
        sourceMetric
        (fun t k => (hp t k).blockScale)
        (fun t k => (hp t k).delta)
        (fun t k => (hp t k).kappa))
      ν covIR Rsc g
      (cmp116Lemma3ScaleAmplitude
        (fun t k => (hp t k).C3)
        (fun t k => (hp t k).epsilon1))
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction :=
  CMP116RawSourceM3Frontier.of_lemma3SourceAssumptions
    (BalabanCMP116Lemma3ResummationSourceAssumptions.to_lemma3SourceAssumptions
      h)

/-- Method-style alias for
`CMP116RawSourceM3Frontier.of_balabanSourceAssumptions`. -/
def BalabanCMP116SourceAssumptions.to_m3Frontier
    (h :
      BalabanCMP116SourceAssumptions
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport weight
        ν covIR Rsc g amplitude
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    CMP116RawSourceM3Frontier
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport weight
      ν covIR Rsc g amplitude
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction :=
  CMP116RawSourceM3Frontier.of_balabanSourceAssumptions h

/-- Method-style alias for
`CMP116RawSourceM3Frontier.of_lemma3SourceAssumptions`. -/
def BalabanCMP116Lemma3SourceAssumptions.to_m3Frontier
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ}
    (h :
      BalabanCMP116Lemma3SourceAssumptions
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport
        sourceMetric blockScale C3 epsilon1 delta kappaSource
        ν covIR Rsc g
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    CMP116RawSourceM3Frontier
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport
      (cmp116Lemma3ScaleWeight sourceMetric blockScale delta kappaSource)
      ν covIR Rsc g
      (cmp116Lemma3ScaleAmplitude C3 epsilon1)
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction :=
  CMP116RawSourceM3Frontier.of_lemma3SourceAssumptions h

/-- Method-style alias for the resummation-source route into the raw-source M3
frontier. -/
def BalabanCMP116Lemma3ResummationSourceAssumptions.to_m3Frontier
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {hp : ∀ _t _k : ℕ, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {z0Weight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ℝ}
    {z0PrimeWeight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k → ιP t k →
          ιZ0 t k → ιZ0' t k → ℝ}
    (h :
      BalabanCMP116Lemma3ResummationSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pWeight z0Weight z0PrimeWeight
        ν covIR Rsc g
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    CMP116RawSourceM3Frontier
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport
      (cmp116Lemma3ScaleWeight
        sourceMetric
        (fun t k => (hp t k).blockScale)
        (fun t k => (hp t k).delta)
        (fun t k => (hp t k).kappa))
      ν covIR Rsc g
      (cmp116Lemma3ScaleAmplitude
        (fun t k => (hp t k).C3)
        (fun t k => (hp t k).epsilon1))
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction :=
  CMP116RawSourceM3Frontier.of_lemma3ResummationSourceAssumptions h

/-- The checked source-theorem target is discharged by pure record packaging. -/
theorem balabanCMP116SourceTheorem_of_assumptions :
    BalabanCMP116SourceTheorem
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport weight
      ν covIR Rsc g amplitude
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction := by
  intro h
  exact h.to_m3Frontier

end

end YangMills.RG

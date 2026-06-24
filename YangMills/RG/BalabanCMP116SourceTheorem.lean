/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma3
import YangMills.RG.PhysicalGaugeCMP116RawM3

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

/-- Translate the CMP116 Lemma 3 source metric into the repository's shifted
Appendix-F modified metric.

The hypothesis compares the complete exponents, so any normalization,
scale-transfer factor, or metric loss remains explicit. -/
theorem balabanCMP116Lemma3Weight_domination
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    (Λ : Finset (OmegaPolymerType HF z))
    {sourceMetric : OmegaPolymerType HF z → ℕ}
    {blockScale : ℕ}
    {delta kappaSource kappa : ℝ}
    (metric_comparison :
      ∀ X, X ∈ Λ →
        kappa *
            (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          balabanCMP116Lemma3DecayRate
              blockScale delta kappaSource *
            (sourceMetric X : ℝ)) :
  ∀ X, X ∈ Λ →
      balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetric X ≤
        appendixFHoleExpWeight HF kappa X.val := by
  intro X hX
  unfold balabanCMP116Lemma3Weight cmp116Lemma3Weight appendixFHoleExpWeight
  exact Real.exp_le_exp.mpr
    (neg_le_neg (by
      simpa [balabanCMP116Lemma3DecayRate, mul_assoc] using
        metric_comparison X hX))

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

/-- Add the final CMP116 Lemma 3 estimate to the separated Gaussian,
root-localization, Hessian-identification, and local-activity source package. -/
def of_lemma3ActivityEstimate
    {ι : Type*}
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {physicalActivity :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {dNext : ι → ℝ}
    {C3 epsilon1 delta blockScale kappa : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (source :
      PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
        D root physicalGaussian
        rootLocalization
        wilsonHessianIdentification
        localActivityConstruction)
    (estimate :
      CMP116Lemma3ActivityEstimate
        physicalActivity dNext
        C3 epsilon1 delta blockScale kappa) :
    PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
      D root physicalGaussian physicalActivity
      (cmp116Lemma3Weight dNext delta blockScale kappa)
      (C3 * epsilon1)
      rootLocalization
      wilsonHessianIdentification
      localActivityConstruction :=
  of_components
    source.gaussian_pushforward
    source.root_localization
    source.wilson_hessian_identification
    source.local_activity_construction
    (balabanLemma3_rawActivityDecay estimate)

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
                source.rawSource
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
  raw_source := h.rawSource
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
    h.rooted_hsharp_remainder_identity_rawSource

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

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeCMP116RawHsharpFrontier
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

/-- Coarse audit class for fields of `BalabanCMP116SourceAssumptions`. -/
inductive BalabanCMP116SourceFieldKind where
  | physicalSource
  | support
  | geometric
  | analytic
  | measureTheoretic
  | rgFlow
deriving DecidableEq, BEq, Repr

/-- One constructor for each field of `BalabanCMP116SourceAssumptions`. -/
inductive BalabanCMP116SourceField where
  | covarianceRootCertificate
  | rootLocalization
  | gaussianPushforward
  | wilsonHessianIdentification
  | localPhysicalActivityConstruction
  | spectatorSupportSubset
  | fluctuationSupportSubset
  | activityStronglyMeasurable
  | rawPointwiseDecay
  | amplitudeNonneg
  | weightNonneg
  | activeSupportSubsetOmega
  | activeSupportSubsetSkeleton
  | weightDomination
  | probabilityLaw
  | holesPairwiseDisjoint
  | noEdgesBetweenHoles
  | holesNonempty
  | appendixFGeometricSmallness
  | rootedHsharpRemainderIdentity
  | amplitudeLeOne
  | profileConstantNonneg
  | hbarNonneg
  | kappaMargin
  | kappa0GtOne
  | timeDecayPositive
  | halfBudget
  | profileBound
  | epsilonPositive
  | betaFlowPositive
  | couplingPositive
  | couplingSmall
  | couplingRecursion
  | irBound
deriving DecidableEq, BEq, Repr

namespace BalabanCMP116SourceField

/-- Stable list of all unfolded Balaban CMP116 source-assumption fields. -/
def all : List BalabanCMP116SourceField :=
  [ covarianceRootCertificate
  , rootLocalization
  , gaussianPushforward
  , wilsonHessianIdentification
  , localPhysicalActivityConstruction
  , spectatorSupportSubset
  , fluctuationSupportSubset
  , activityStronglyMeasurable
  , rawPointwiseDecay
  , amplitudeNonneg
  , weightNonneg
  , activeSupportSubsetOmega
  , activeSupportSubsetSkeleton
  , weightDomination
  , probabilityLaw
  , holesPairwiseDisjoint
  , noEdgesBetweenHoles
  , holesNonempty
  , appendixFGeometricSmallness
  , rootedHsharpRemainderIdentity
  , amplitudeLeOne
  , profileConstantNonneg
  , hbarNonneg
  , kappaMargin
  , kappa0GtOne
  , timeDecayPositive
  , halfBudget
  , profileBound
  , epsilonPositive
  , betaFlowPositive
  , couplingPositive
  , couplingSmall
  , couplingRecursion
  , irBound
  ]

/-- Classification of each unfolded source field by its role in the M3 route. -/
def kind : BalabanCMP116SourceField → BalabanCMP116SourceFieldKind
  | covarianceRootCertificate => .physicalSource
  | rootLocalization => .physicalSource
  | gaussianPushforward => .physicalSource
  | wilsonHessianIdentification => .physicalSource
  | localPhysicalActivityConstruction => .physicalSource
  | spectatorSupportSubset => .support
  | fluctuationSupportSubset => .support
  | activityStronglyMeasurable => .support
  | rawPointwiseDecay => .physicalSource
  | amplitudeNonneg => .analytic
  | weightNonneg => .analytic
  | activeSupportSubsetOmega => .support
  | activeSupportSubsetSkeleton => .support
  | weightDomination => .geometric
  | probabilityLaw => .measureTheoretic
  | holesPairwiseDisjoint => .geometric
  | noEdgesBetweenHoles => .geometric
  | holesNonempty => .geometric
  | appendixFGeometricSmallness => .geometric
  | rootedHsharpRemainderIdentity => .analytic
  | amplitudeLeOne => .analytic
  | profileConstantNonneg => .analytic
  | hbarNonneg => .analytic
  | kappaMargin => .analytic
  | kappa0GtOne => .analytic
  | timeDecayPositive => .rgFlow
  | halfBudget => .analytic
  | profileBound => .analytic
  | epsilonPositive => .rgFlow
  | betaFlowPositive => .rgFlow
  | couplingPositive => .rgFlow
  | couplingSmall => .rgFlow
  | couplingRecursion => .rgFlow
  | irBound => .rgFlow

end BalabanCMP116SourceField

/-- Source-assumption fields plus the derived record-package nodes they feed. -/
inductive BalabanCMP116SourceDependencyNode where
  | field : BalabanCMP116SourceField → BalabanCMP116SourceDependencyNode
  | rawSourcePackage
  | rawScaleFamilyProjection
  | rootedHsharpRawSourceIdentity
  | m3FrontierAssembly
deriving DecidableEq, BEq, Repr

namespace BalabanCMP116SourceDependencyNode

/-- Every node in the current source-assumption dependency graph. -/
def all : List BalabanCMP116SourceDependencyNode :=
  BalabanCMP116SourceField.all.map field ++
    [ rawSourcePackage
    , rawScaleFamilyProjection
    , rootedHsharpRawSourceIdentity
    , m3FrontierAssembly
    ]

/-- A topological rank.  Edges point only to lower-rank nodes. -/
def rank : BalabanCMP116SourceDependencyNode → Nat
  | field _ => 0
  | rawSourcePackage => 1
  | rawScaleFamilyProjection => 2
  | rootedHsharpRawSourceIdentity => 3
  | m3FrontierAssembly => 4

end BalabanCMP116SourceDependencyNode

namespace BalabanCMP116SourceDependencyGraph

/-- The five unfolded source components reassembled into the raw-source package. -/
def rawSourcePackageInputs : List BalabanCMP116SourceField :=
  [ .rootLocalization
  , .gaussianPushforward
  , .wilsonHessianIdentification
  , .localPhysicalActivityConstruction
  , .rawPointwiseDecay
  ]

/-- Inputs used when the canonical raw-source package feeds the scale family. -/
def rawScaleFamilyProjectionInputs : List BalabanCMP116SourceField :=
  [ .covarianceRootCertificate
  , .spectatorSupportSubset
  , .fluctuationSupportSubset
  , .amplitudeNonneg
  , .weightNonneg
  , .activityStronglyMeasurable
  , .activeSupportSubsetOmega
  , .activeSupportSubsetSkeleton
  , .weightDomination
  ]

/-- Inputs passed directly to the raw-source M3 frontier assembly. -/
def m3FrontierAssemblyInputs : List BalabanCMP116SourceField :=
  [ .covarianceRootCertificate
  , .spectatorSupportSubset
  , .fluctuationSupportSubset
  , .weightNonneg
  , .activeSupportSubsetOmega
  , .activeSupportSubsetSkeleton
  , .weightDomination
  , .holesPairwiseDisjoint
  , .noEdgesBetweenHoles
  , .holesNonempty
  , .appendixFGeometricSmallness
  , .activityStronglyMeasurable
  , .probabilityLaw
  , .amplitudeNonneg
  , .amplitudeLeOne
  , .profileConstantNonneg
  , .hbarNonneg
  , .kappaMargin
  , .kappa0GtOne
  , .couplingPositive
  , .halfBudget
  , .profileBound
  , .epsilonPositive
  , .timeDecayPositive
  , .betaFlowPositive
  , .couplingSmall
  , .couplingRecursion
  , .irBound
  ]

/-- Incoming edges for the executable source-assumption audit graph. -/
def dependencies :
    BalabanCMP116SourceDependencyNode → List BalabanCMP116SourceDependencyNode
  | .field _ => []
  | .rawSourcePackage =>
      rawSourcePackageInputs.map BalabanCMP116SourceDependencyNode.field
  | .rawScaleFamilyProjection =>
      .rawSourcePackage ::
        rawScaleFamilyProjectionInputs.map BalabanCMP116SourceDependencyNode.field
  | .rootedHsharpRawSourceIdentity =>
      [ .rawScaleFamilyProjection
      , .field .rootedHsharpRemainderIdentity
      ]
  | .m3FrontierAssembly =>
      .rawSourcePackage ::
        .rootedHsharpRawSourceIdentity ::
          m3FrontierAssemblyInputs.map BalabanCMP116SourceDependencyNode.field

/-- Derived proof-routing nodes, distinct from source-assumption fields. -/
def derivedNodes : List BalabanCMP116SourceDependencyNode :=
  [ .rawSourcePackage
  , .rawScaleFamilyProjection
  , .rootedHsharpRawSourceIdentity
  , .m3FrontierAssembly
  ]

/-- Derived nodes whose purpose is to feed another derived consumer. -/
def nonterminalDerivedNodes : List BalabanCMP116SourceDependencyNode :=
  [ .rawSourcePackage
  , .rawScaleFamilyProjection
  , .rootedHsharpRawSourceIdentity
  ]

/-- All incoming edges to derived consumers.  Field nodes have no dependencies. -/
def derivedDependencyInputs : List BalabanCMP116SourceDependencyNode :=
  dependencies .rawSourcePackage ++
    dependencies .rawScaleFamilyProjection ++
      dependencies .rootedHsharpRawSourceIdentity ++
        dependencies .m3FrontierAssembly

/-- All source fields consumed as inputs by at least one derived node. -/
def allInputFields : List BalabanCMP116SourceField :=
  rawSourcePackageInputs ++ rawScaleFamilyProjectionInputs ++
    m3FrontierAssemblyInputs ++ [.rootedHsharpRemainderIdentity]

/-- Source fields with a fixed coarse audit role. -/
def fieldsOfKind (k : BalabanCMP116SourceFieldKind) :
    List BalabanCMP116SourceField :=
  BalabanCMP116SourceField.all.filter
    (fun f => BalabanCMP116SourceField.kind f == k)

/-- Executable check for the current role distribution of the source frontier. -/
def sourceFieldKindProfileMatchesExpected : Bool :=
  (fieldsOfKind .physicalSource).length == 6 &&
    (fieldsOfKind .support).length == 5 &&
      (fieldsOfKind .geometric).length == 5 &&
        (fieldsOfKind .analytic).length == 10 &&
          (fieldsOfKind .measureTheoretic).length == 1 &&
            (fieldsOfKind .rgFlow).length == 7

/-- The raw-source package should consume only physical-source fields. -/
def rawSourcePackageInputsArePhysicalSource : Bool :=
  rawSourcePackageInputs.all
    (fun f => BalabanCMP116SourceField.kind f == .physicalSource)

/-- The final marginal/IR inputs are kept out of the raw-source package. -/
def rawSourcePackageInputsAvoidRGFlow : Bool :=
  rawSourcePackageInputs.all
    (fun f => !(BalabanCMP116SourceField.kind f == .rgFlow))

/-- Every dependency must point backward in the declared topological order. -/
def edgesPointBackward : Bool :=
  BalabanCMP116SourceDependencyNode.all.all
    (fun n =>
      (dependencies n).all
        (fun m =>
          BalabanCMP116SourceDependencyNode.rank m <
            BalabanCMP116SourceDependencyNode.rank n))

/-- Executable acyclicity check for this finite dependency graph. -/
def isAcyclic : Bool :=
  edgesPointBackward

/-- Every source-assumption field has a corresponding graph node. -/
def allSourceFieldsCovered : Bool :=
  BalabanCMP116SourceField.all.all
    (fun f => BalabanCMP116SourceDependencyNode.all.contains (.field f))

/-- Every source-assumption field is used by the current derived spine. -/
def allSourceFieldsUsed : Bool :=
  BalabanCMP116SourceField.all.all
    (fun f => allInputFields.contains f)

/-- Derived formal consumers are not source-assumption fields. -/
def derivedNodesHavePositiveRank : Bool :=
  derivedNodes.all
    (fun n => 0 < BalabanCMP116SourceDependencyNode.rank n)

/-- No intermediate derived node is orphaned in the current dependency spine. -/
def nonterminalDerivedNodesUsed : Bool :=
  nonterminalDerivedNodes.all
    (fun n => derivedDependencyInputs.contains n)

/-- Bounded reachability along incoming dependency edges. -/
def dependsOnWithin : Nat →
    BalabanCMP116SourceDependencyNode →
      BalabanCMP116SourceDependencyNode → Bool
  | 0, consumer, source => consumer == source
  | fuel + 1, consumer, source =>
      (consumer == source) ||
        (dependencies consumer).any
          (fun next => dependsOnWithin fuel next source)

/-- The finite fuel used for dependency-closure checks. -/
def dependencyClosureFuel : Nat :=
  BalabanCMP116SourceDependencyNode.all.length

/-- Every source field reaches the final raw-source M3 frontier assembly node. -/
def m3FrontierAssemblyDependsOnAllSourceFields : Bool :=
  BalabanCMP116SourceField.all.all
    (fun f =>
      dependsOnWithin dependencyClosureFuel .m3FrontierAssembly (.field f))

theorem isAcyclic_eq_true :
    isAcyclic = true := by
  decide

theorem allSourceFieldsCovered_eq_true :
    allSourceFieldsCovered = true := by
  decide

theorem allSourceFieldsUsed_eq_true :
    allSourceFieldsUsed = true := by
  decide

theorem sourceFieldKindProfileMatchesExpected_eq_true :
    sourceFieldKindProfileMatchesExpected = true := by
  decide

theorem rawSourcePackageInputsArePhysicalSource_eq_true :
    rawSourcePackageInputsArePhysicalSource = true := by
  decide

theorem rawSourcePackageInputsAvoidRGFlow_eq_true :
    rawSourcePackageInputsAvoidRGFlow = true := by
  decide

theorem derivedNodesHavePositiveRank_eq_true :
    derivedNodesHavePositiveRank = true := by
  decide

theorem nonterminalDerivedNodesUsed_eq_true :
    nonterminalDerivedNodesUsed = true := by
  decide

theorem m3FrontierAssemblyDependsOnAllSourceFields_eq_true :
    m3FrontierAssemblyDependsOnAllSourceFields = true := by
  decide

end BalabanCMP116SourceDependencyGraph

#guard BalabanCMP116SourceField.all.length == 34
#guard BalabanCMP116SourceDependencyNode.all.length == 38
#guard BalabanCMP116SourceDependencyGraph.isAcyclic
#guard BalabanCMP116SourceDependencyGraph.allSourceFieldsCovered
#guard BalabanCMP116SourceDependencyGraph.allSourceFieldsUsed
#guard BalabanCMP116SourceDependencyGraph.sourceFieldKindProfileMatchesExpected
#guard BalabanCMP116SourceDependencyGraph.rawSourcePackageInputsArePhysicalSource
#guard BalabanCMP116SourceDependencyGraph.rawSourcePackageInputsAvoidRGFlow
#guard BalabanCMP116SourceDependencyGraph.derivedNodesHavePositiveRank
#guard BalabanCMP116SourceDependencyGraph.nonterminalDerivedNodesUsed
#guard BalabanCMP116SourceDependencyGraph.m3FrontierAssemblyDependsOnAllSourceFields

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
supplied by the weighted post-`P` source package.

This is a source-boundary record.  It does not prove Eq. (2.29), the P-stage
source estimate, the post-`P` source estimate, the post-`P` majorization, the
activity identification, or any physical Gaussian/root/Wilson/local-activity
fact.  It only exposes the newest weighted post-`P` Lemma-3 package as a
first-class route into the existing raw-source M3 frontier while keeping all
physical, support, geometry, H#, marginal-flow, and IR fields explicit. -/
structure BalabanCMP116Lemma3WeightedPostPSourceAssumptions
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
    (pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
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

  weighted_postP_source :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude

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
    let rawSource :=
      CMP116Lemma3WeightedPostPScaleSourceAssumptions.rawSource
        gaussian_pushforward
        root_localization
        wilson_hessian_identification
        local_physical_activity_construction
        weighted_postP_source
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

namespace BalabanCMP116Lemma3WeightedPostPSourceAssumptions

section

variable
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
    {pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    {ν : ℕ → ℕ → Measure β}
    {covIR : ℕ → ℝ}
    {Rsc : ℕ → ℕ → ℝ}
    {g : ℕ → ℝ}
    {C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}

/-- Project weighted post-`P` source assumptions to the canonical Lemma-3
activity estimate. -/
def lemma3_activity_estimate
    (source :
      BalabanCMP116Lemma3WeightedPostPSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude
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
  CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate
    source.weighted_postP_source

/-- Canonical raw-source records extracted from weighted post-`P` source
assumptions. -/
def rawSource
    (source :
      BalabanCMP116Lemma3WeightedPostPSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude
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
  CMP116Lemma3WeightedPostPScaleSourceAssumptions.rawSource
    source.gaussian_pushforward
    source.root_localization
    source.wilson_hessian_identification
    source.local_physical_activity_construction
    source.weighted_postP_source

/-- Package weighted post-`P` source assumptions into the existing Lemma-3
source-assumption record. -/
def to_lemma3SourceAssumptions
    (source :
      BalabanCMP116Lemma3WeightedPostPSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude
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
    simpa [lemma3_activity_estimate,
      CMP116Lemma3WeightedPostPScaleSourceAssumptions.rawSource] using
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

/-- Constructor for weighted post-`P` source-frontier assumptions from explicit
Eq. (2.31) P-bond boundary data.

This is record assembly around
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries`.  It keeps
all physical/M3 obligations explicit and proves no Eq. (2.29), Eq. (2.31),
P-stage, post-`P`, activity-identification, termwise, or physical source fact. -/
def of_eq231_boundaries
    {ιB : ℕ → ℕ → Type*}
    {pGeometryWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {eq231LocalizationScale : ℕ → ℕ → ℕ}
    {gamma2 gk : ℕ → ℕ → ℝ}
    (covariance_root_certificate :
      ∀ t k,
        PhysicalLocalizedCovarianceRootCertificate
          (precision t k) (covariance t k) (root t k)
          (covNormBound t k) (rootNormBound t k)
          (covWeight t k) (rootWeight t k))
    (root_localization :
      ∀ t k, rootLocalization t k)
    (gaussian_pushforward :
      ∀ t k,
        (balabanCMP116Dmu0 (Cube d L) lieDim).map
            ((D t k).gaussianRootMap (root t k)) =
          physicalGaussian t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (spectator_support_subset :
      ∀ t k X,
        (physicalActivity t k X).spectatorSupport ⊆
          physicalActiveSupport t k X)
    (fluctuation_support_subset :
      ∀ t k X,
        (physicalActivity t k X).fluctuationSupport ⊆
          physicalActiveSupport t k X)
    (activity_stronglyMeasurable :
      ∀ t k X, ∀ ψ : ∀ _ : Cube d L, β,
        StronglyMeasurable
          (fun ξ : CMP116FluctuationField d L lieDim =>
            ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
              (Ψ := fun _ : Cube d L => β)
              (D t k)
              (fun X : OmegaPolymerType HF (z t k) => X)
              (spectatorPull t k)).activity
                (physicalActivity t k) X).globalEval ψ ξ))
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := ιB t k)
          (R t k).DIndex
          (R t k).PIndex
          (eq231LocalizationScale t k))
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (B t k).gapMass (B t k).pBonds Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity)
    (amplitude_nonneg :
      ∀ t k,
        0 ≤
          cmp116Lemma3ScaleAmplitude
            (fun t k => (hp t k).C3)
            (fun t k => (hp t k).epsilon1)
            t k)
    (active_support_subset_omega :
      ∀ t k X,
        physicalActiveSupport t k X ⊆
          (D t k).physicalBondsOfCells (D t k).siteMap.Omega)
    (active_support_subset_skeleton :
      ∀ t k X, X ∈ Λ t k →
        physicalActiveSupport t k X ⊆
          (D t k).physicalBondsOfCells (skeleton HF X.val))
    (weight_domination :
      ∀ t k X, X ∈ Λ t k →
        cmp116Lemma3ScaleWeight
            sourceMetric
            (fun t k => (hp t k).blockScale)
            (fun t k => (hp t k).delta)
            (fun t k => (hp t k).kappa)
            t k X ≤
          appendixFHoleExpWeight HF kappa X.val)
    (probability_law :
      ∀ t k, IsProbabilityMeasure (ν t k))
    (holes_pairwise_disjoint :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (no_edges_between_holes :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (holes_nonempty :
      ∀ H ∈ HF.holes, H.Nonempty)
    (appendix_f_geometric_smallness :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1)
    (rooted_hsharp_remainder_identity :
      let weighted_postP_source :=
        CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries
          eq229 B hepsilon2_nonneg hpointwise hsourceBracket
          hgeometry htarget hsmall hpResidual_nonneg postP activity
      let rawSource :=
        CMP116Lemma3WeightedPostPScaleSourceAssumptions.rawSource
          gaussian_pushforward
          root_localization
          wilson_hessian_identification
          local_physical_activity_construction
          weighted_postP_source
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
                (ν t k) P.val.val))
    (amplitude_le_one :
      ∀ t k,
        cmp116Lemma3ScaleAmplitude
            (fun t k => (hp t k).C3)
            (fun t k => (hp t k).epsilon1)
            t k ≤ 1)
    (profile_constant_nonneg :
      0 ≤ C)
    (hbar_nonneg :
      0 ≤ Hbar)
    (kappa_margin :
      4 * kappa0 + 3 ≤ kappa)
    (kappa0_gt_one :
      1 < kappa0)
    (time_decay_positive :
      0 < c0)
    (half_budget :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d kappa0 *
            (2 *
              cmp116Lemma3ScaleAmplitude
                (fun t k => (hp t k).C3)
                (fun t k => (hp t k).epsilon1)
                t k *
              appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2)
    (profile_bound :
      ∀ t k,
        4 * appendixFSecondUrsellMomentConstant d kappa0 *
            cmp116Lemma3ScaleAmplitude
              (fun t k => (hp t k).C3)
              (fun t k => (hp t k).epsilon1)
              t k *
            appendixFHoleRootSumConstant d kappa0 ≤
          C * Hbar *
            Real.exp (-(c0 * (t : ℝ))) *
            g k ^ kappa0)
    (epsilon_positive :
      0 < ε)
    (beta_flow_positive :
      0 < betaFlow)
    (coupling_positive :
      ∀ k, 0 < g k)
    (coupling_small :
      ∀ k, betaFlow * g k < 1)
    (coupling_recursion :
      ∀ k,
        g (k + 1) =
          g k * (1 - betaFlow * g k))
    (ir_bound :
      ∀ k : ℕ,
        |covIR k| ≤
          C1 * Real.exp (-(ε * (k : ℝ)))) :
    BalabanCMP116Lemma3WeightedPostPSourceAssumptions
      ιD ιP ιZ0 ιZ0' ιY
      zCarrier r z Λ D spectatorPull
      precision covariance root physicalGaussian
      covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport sourceMetric
      hp R DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude
      ν covIR Rsc g
      C1 C Hbar ε c0 betaFlow kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction where
  covariance_root_certificate := covariance_root_certificate
  root_localization := root_localization
  gaussian_pushforward := gaussian_pushforward
  wilson_hessian_identification := wilson_hessian_identification
  local_physical_activity_construction :=
    local_physical_activity_construction
  spectator_support_subset := spectator_support_subset
  fluctuation_support_subset := fluctuation_support_subset
  activity_stronglyMeasurable := activity_stronglyMeasurable
  weighted_postP_source :=
    CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries
      eq229 B hepsilon2_nonneg hpointwise hsourceBracket
      hgeometry htarget hsmall hpResidual_nonneg postP activity
  amplitude_nonneg := amplitude_nonneg
  active_support_subset_omega := active_support_subset_omega
  active_support_subset_skeleton := active_support_subset_skeleton
  weight_domination := weight_domination
  probability_law := probability_law
  holes_pairwise_disjoint := holes_pairwise_disjoint
  no_edges_between_holes := no_edges_between_holes
  holes_nonempty := holes_nonempty
  appendix_f_geometric_smallness := appendix_f_geometric_smallness
  rooted_hsharp_remainder_identity := by
    simpa using rooted_hsharp_remainder_identity
  amplitude_le_one := amplitude_le_one
  profile_constant_nonneg := profile_constant_nonneg
  hbar_nonneg := hbar_nonneg
  kappa_margin := kappa_margin
  kappa0_gt_one := kappa0_gt_one
  time_decay_positive := time_decay_positive
  half_budget := half_budget
  profile_bound := profile_bound
  epsilon_positive := epsilon_positive
  beta_flow_positive := beta_flow_positive
  coupling_positive := coupling_positive
  coupling_small := coupling_small
  coupling_recursion := coupling_recursion
  ir_bound := ir_bound

end

end BalabanCMP116Lemma3WeightedPostPSourceAssumptions

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

/-- Package weighted post-`P` source assumptions into the existing raw-source
M3 frontier.

This constructor is parallel to
`CMP116RawSourceM3Frontier.of_lemma3SourceAssumptions`, but derives the Lemma-3
scale-family estimate from the weighted post-`P` source package already carried
by `BalabanCMP116Lemma3WeightedPostPSourceAssumptions`. -/
def CMP116RawSourceM3Frontier.of_lemma3WeightedPostPSourceAssumptions
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
    {pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (h :
      BalabanCMP116Lemma3WeightedPostPSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude
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
    (BalabanCMP116Lemma3WeightedPostPSourceAssumptions.to_lemma3SourceAssumptions
      h)

/-- Direct M3-frontier constructor from Eq. (2.31) weighted post-`P`
source-boundary data.

This is only the composition of
`BalabanCMP116Lemma3WeightedPostPSourceAssumptions.of_eq231_boundaries` with
`CMP116RawSourceM3Frontier.of_lemma3WeightedPostPSourceAssumptions`.  It keeps
the Eq. (2.29), Eq. (2.31), post-`P`, activity, physical-source, and Appendix-F
inputs explicit and proves no new source estimate. -/
def CMP116RawSourceM3Frontier.of_eq231WeightedPostPSourceBoundaries
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {ιB : ℕ → ℕ → Type*}
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
    {pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    {pGeometryWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {eq231LocalizationScale : ℕ → ℕ → ℕ}
    {gamma2 gk : ℕ → ℕ → ℝ}
    (covariance_root_certificate :
      ∀ t k,
        PhysicalLocalizedCovarianceRootCertificate
          (precision t k) (covariance t k) (root t k)
          (covNormBound t k) (rootNormBound t k)
          (covWeight t k) (rootWeight t k))
    (root_localization :
      ∀ t k, rootLocalization t k)
    (gaussian_pushforward :
      ∀ t k,
        (balabanCMP116Dmu0 (Cube d L) lieDim).map
            ((D t k).gaussianRootMap (root t k)) =
          physicalGaussian t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (spectator_support_subset :
      ∀ t k X,
        (physicalActivity t k X).spectatorSupport ⊆
          physicalActiveSupport t k X)
    (fluctuation_support_subset :
      ∀ t k X,
        (physicalActivity t k X).fluctuationSupport ⊆
          physicalActiveSupport t k X)
    (activity_stronglyMeasurable :
      ∀ t k X, ∀ ψ : ∀ _ : Cube d L, β,
        StronglyMeasurable
          (fun ξ : CMP116FluctuationField d L lieDim =>
            ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
              (Ψ := fun _ : Cube d L => β)
              (D t k)
              (fun X : OmegaPolymerType HF (z t k) => X)
              (spectatorPull t k)).activity
                (physicalActivity t k) X).globalEval ψ ξ))
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := ιB t k)
          (R t k).DIndex
          (R t k).PIndex
          (eq231LocalizationScale t k))
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (B t k).gapMass (B t k).pBonds Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity)
    (amplitude_nonneg :
      ∀ t k,
        0 ≤
          cmp116Lemma3ScaleAmplitude
            (fun t k => (hp t k).C3)
            (fun t k => (hp t k).epsilon1)
            t k)
    (active_support_subset_omega :
      ∀ t k X,
        physicalActiveSupport t k X ⊆
          (D t k).physicalBondsOfCells (D t k).siteMap.Omega)
    (active_support_subset_skeleton :
      ∀ t k X, X ∈ Λ t k →
        physicalActiveSupport t k X ⊆
          (D t k).physicalBondsOfCells (skeleton HF X.val))
    (weight_domination :
      ∀ t k X, X ∈ Λ t k →
        cmp116Lemma3ScaleWeight
            sourceMetric
            (fun t k => (hp t k).blockScale)
            (fun t k => (hp t k).delta)
            (fun t k => (hp t k).kappa)
            t k X ≤
          appendixFHoleExpWeight HF kappa X.val)
    (probability_law :
      ∀ t k, IsProbabilityMeasure (ν t k))
    (holes_pairwise_disjoint :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (no_edges_between_holes :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (holes_nonempty :
      ∀ H ∈ HF.holes, H.Nonempty)
    (appendix_f_geometric_smallness :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1)
    (rooted_hsharp_remainder_identity :
      let weighted_postP_source :=
        CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries
          eq229 B hepsilon2_nonneg hpointwise hsourceBracket
          hgeometry htarget hsmall hpResidual_nonneg postP activity
      let rawSource :=
        CMP116Lemma3WeightedPostPScaleSourceAssumptions.rawSource
          gaussian_pushforward
          root_localization
          wilson_hessian_identification
          local_physical_activity_construction
          weighted_postP_source
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
                (ν t k) P.val.val))
    (amplitude_le_one :
      ∀ t k,
        cmp116Lemma3ScaleAmplitude
            (fun t k => (hp t k).C3)
            (fun t k => (hp t k).epsilon1)
            t k ≤ 1)
    (profile_constant_nonneg :
      0 ≤ C)
    (hbar_nonneg :
      0 ≤ Hbar)
    (kappa_margin :
      4 * kappa0 + 3 ≤ kappa)
    (kappa0_gt_one :
      1 < kappa0)
    (time_decay_positive :
      0 < c0)
    (half_budget :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d kappa0 *
            (2 *
              cmp116Lemma3ScaleAmplitude
                (fun t k => (hp t k).C3)
                (fun t k => (hp t k).epsilon1)
                t k *
              appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2)
    (profile_bound :
      ∀ t k,
        4 * appendixFSecondUrsellMomentConstant d kappa0 *
            cmp116Lemma3ScaleAmplitude
              (fun t k => (hp t k).C3)
              (fun t k => (hp t k).epsilon1)
              t k *
            appendixFHoleRootSumConstant d kappa0 ≤
          C * Hbar *
            Real.exp (-(c0 * (t : ℝ))) *
            g k ^ kappa0)
    (epsilon_positive :
      0 < ε)
    (beta_flow_positive :
      0 < betaFlow)
    (coupling_positive :
      ∀ k, 0 < g k)
    (coupling_small :
      ∀ k, betaFlow * g k < 1)
    (coupling_recursion :
      ∀ k,
        g (k + 1) =
          g k * (1 - betaFlow * g k))
    (ir_bound :
      ∀ k : ℕ,
        |covIR k| ≤
          C1 * Real.exp (-(ε * (k : ℝ)))) :
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
  CMP116RawSourceM3Frontier.of_lemma3WeightedPostPSourceAssumptions
    (BalabanCMP116Lemma3WeightedPostPSourceAssumptions.of_eq231_boundaries
      covariance_root_certificate
      root_localization
      gaussian_pushforward
      wilson_hessian_identification
      local_physical_activity_construction
      spectator_support_subset
      fluctuation_support_subset
      activity_stronglyMeasurable
      eq229
      B
      hepsilon2_nonneg
      hpointwise
      hsourceBracket
      hgeometry
      htarget
      hsmall
      hpResidual_nonneg
      postP
      activity
      amplitude_nonneg
      active_support_subset_omega
      active_support_subset_skeleton
      weight_domination
      probability_law
      holes_pairwise_disjoint
      no_edges_between_holes
      holes_nonempty
      appendix_f_geometric_smallness
      rooted_hsharp_remainder_identity
      amplitude_le_one
      profile_constant_nonneg
      hbar_nonneg
      kappa_margin
      kappa0_gt_one
      time_decay_positive
      half_budget
      profile_bound
      epsilon_positive
      beta_flow_positive
      coupling_positive
      coupling_small
      coupling_recursion
      ir_bound)

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

/-- Method-style alias for the weighted post-`P` source route into the
raw-source M3 frontier. -/
def BalabanCMP116Lemma3WeightedPostPSourceAssumptions.to_m3Frontier
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
    {pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (h :
      BalabanCMP116Lemma3WeightedPostPSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude
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
  CMP116RawSourceM3Frontier.of_lemma3WeightedPostPSourceAssumptions h

/-- The weighted post-`P` source-assumption record feeds the marginal M3
assembly after projecting through the named raw-source frontier.

This is source-independent theorem plumbing: the record still carries the
Eq. (2.29), Eq. (2.31), post-`P`, physical-source, Appendix-F, marginal-flow,
and IR obligations explicitly. -/
theorem BalabanCMP116Lemma3WeightedPostPSourceAssumptions.lattice_mass_gap_marginal
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
    {pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (h :
      BalabanCMP116Lemma3WeightedPostPSourceAssumptions
        ιD ιP ιZ0 ιZ0' ιY
        zCarrier r z Λ D spectatorPull
        precision covariance root physicalGaussian
        covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport sourceMetric
        hp R DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude
        ν covIR Rsc g
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction)
    (nsc : ℕ → ℕ) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t| ≤
        (C1 + cmp116RawHsharpUVAmplitude d C Hbar kappa0 *
          (∑' k, g k ^ kappa0)) *
          Real.exp (-(gap * (t : ℝ))) := by
  exact
    CMP116RawSourceM3Frontier.lattice_mass_gap_marginal
      (dPhys := dPhys) (N := N) (Nc := Nc)
      (d := d) (L := L) (lieDim := lieDim)
      (β := β) (HF := HF)
      (C1 := C1) (C := C) (Hbar := Hbar)
      (ε := ε) (c0 := c0) (betaFlow := betaFlow)
      (kappa := kappa) (kappa0 := kappa0)
      zCarrier r z Λ D spectatorPull precision covariance root
      physicalGaussian covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport
      (cmp116Lemma3ScaleWeight
        sourceMetric
        (fun t k => (hp t k).blockScale)
        (fun t k => (hp t k).delta)
        (fun t k => (hp t k).kappa))
      ν covIR Rsc nsc g
      (cmp116Lemma3ScaleAmplitude
        (fun t k => (hp t k).C3)
        (fun t k => (hp t k).epsilon1))
      rootLocalization wilsonHessianIdentification
      localActivityConstruction h.to_m3Frontier

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

/-- The resummation-source assumption record feeds the marginal M3 assembly
after projecting through the named raw-source frontier.

This is source-independent theorem plumbing: the record still carries the
Eq. (2.29), Eq. (2.31), residual-stage, physical-source, Appendix-F,
marginal-flow, and IR obligations explicitly. -/
theorem BalabanCMP116Lemma3ResummationSourceAssumptions.lattice_mass_gap_marginal
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
        localActivityConstruction)
    (nsc : ℕ → ℕ) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t| ≤
        (C1 + cmp116RawHsharpUVAmplitude d C Hbar kappa0 *
          (∑' k, g k ^ kappa0)) *
          Real.exp (-(gap * (t : ℝ))) := by
  exact
    CMP116RawSourceM3Frontier.lattice_mass_gap_marginal
      (dPhys := dPhys) (N := N) (Nc := Nc)
      (d := d) (L := L) (lieDim := lieDim)
      (β := β) (HF := HF)
      (C1 := C1) (C := C) (Hbar := Hbar)
      (ε := ε) (c0 := c0) (betaFlow := betaFlow)
      (kappa := kappa) (kappa0 := kappa0)
      zCarrier r z Λ D spectatorPull precision covariance root
      physicalGaussian covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport
      (cmp116Lemma3ScaleWeight
        sourceMetric
        (fun t k => (hp t k).blockScale)
        (fun t k => (hp t k).delta)
        (fun t k => (hp t k).kappa))
      ν covIR Rsc nsc g
      (cmp116Lemma3ScaleAmplitude
        (fun t k => (hp t k).C3)
        (fun t k => (hp t k).epsilon1))
      rootLocalization wilsonHessianIdentification
      localActivityConstruction h.to_m3Frontier

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

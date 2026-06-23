/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeCMP116ActivityAdapter

/-!
# Dictionary-backed physical/CMP116 Gaussian activity construction

This file assembles existing finite interfaces into canonical dictionary-backed
constructors.  The dictionary now determines the continuous coordinate
equivalence, the CMP116 root transport coordinates, the Gaussian coordinate
map, and the localized CMP116 family used by the physical transport record.

Honest scope: all analytic source facts remain explicit fields or hypotheses.
In particular, this file does not prove that the dictionary/root map preserves a
Gaussian law, does not localize the exact covariance root, does not identify a
Wilson Hessian, does not construct the physical local activity, and does not
prove a new decay estimate.
-/

namespace YangMills.RG

open MeasureTheory
open scoped RealInnerProductSpace

namespace PhysicalGaugeCMP116Dictionary

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- The scalar-coordinate dictionary as a continuous linear equivalence. -/
noncomputable def fluctuationFieldContinuousLinearEquiv
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim) :
    CMP116FluctuationField d L lieDim ≃L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc :=
  D.fluctuationFieldLinearEquiv.toContinuousLinearEquiv

@[simp] theorem fluctuationFieldContinuousLinearEquiv_apply
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (ξ : CMP116FluctuationField d L lieDim) :
    D.fluctuationFieldContinuousLinearEquiv ξ =
      D.pullFluctuationCochain ξ :=
  rfl

@[simp] theorem fluctuationFieldContinuousLinearEquiv_symm_apply
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A : PhysicalGaugeOneCochain dPhys N Nc) :
    D.fluctuationFieldContinuousLinearEquiv.symm A =
      D.pushFluctuation A :=
  rfl

/-- The continuous dictionary commutes with CMP116 coordinate projection and
physical projection onto the bonds assigned to the same cube set. -/
theorem fluctuationFieldContinuousLinearEquiv_support_projection
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (X : Finset (Cube d L)) :
    D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap.comp
        (cmp116FieldProjection (lieDim := lieDim) X) =
      (physicalBondProjection
        (physicalBondsOver D.siteMap.bondToCube X)).comp
        D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap := by
  ext ξ b
  by_cases hb : D.siteMap.bondToCube b ∈ X
  · simp [fluctuationFieldContinuousLinearEquiv,
      pullFluctuationCochain_apply, physicalBondProjection,
      cmp116FieldProjection, hb]
  · simp [fluctuationFieldContinuousLinearEquiv,
      pullFluctuationCochain_apply, pullFluctuationAtBond,
      sunLieCoordOfScalars, physicalBondProjection,
      cmp116FieldProjection, hb]

/-- The canonical Gaussian coordinate map for the source change of variables:
first pull CMP116 product coordinates through the dictionary, then apply the
physical covariance-root map. -/
noncomputable def gaussianRootMap
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc) :
    CMP116FluctuationField d L lieDim →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc :=
  root.comp D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem gaussianRootMap_apply
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (ξ : CMP116FluctuationField d L lieDim) :
    D.gaussianRootMap root ξ =
      root (D.pullFluctuationCochain ξ) :=
  rfl

/-- Instantiate the Gaussian-change record with the canonical dictionary/root
coordinate map.  The measure pushforward identity is still supplied explicitly. -/
noncomputable def PhysicalGaugeCMP116GaussianChange.ofDictionaryRoot
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (hpush :
      (balabanCMP116Dmu0 (Cube d L) lieDim).map
          (D.gaussianRootMap root) =
        physicalGaussian) :
    PhysicalGaugeCMP116GaussianChange D where
  gaussianCoordinateMap := D.gaussianRootMap root
  physicalGaussian := physicalGaussian
  gaussianCoordinateMap_measurable :=
    (D.gaussianRootMap root).continuous.measurable
  map_gaussianChangeOfVariables := hpush

@[simp] theorem PhysicalGaugeCMP116GaussianChange.ofDictionaryRoot_map
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (hpush :
      (balabanCMP116Dmu0 (Cube d L) lieDim).map
          (D.gaussianRootMap root) =
        physicalGaussian) :
    (PhysicalGaugeCMP116GaussianChange.ofDictionaryRoot
      D root physicalGaussian hpush).gaussianCoordinateMap =
      D.gaussianRootMap root :=
  rfl

/-- Consume a Gaussian change-of-variables record as an exact Bochner-integral
rewrite.  This is only the measure-pushforward consequence of the record; it
does not assert any covariance, localization, or physical Hessian semantics. -/
theorem PhysicalGaugeCMP116GaussianChange.integral_gaussianCoordinateMap_eq
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (change : PhysicalGaugeCMP116GaussianChange D)
    (f : PhysicalGaugeOneCochain dPhys N Nc → ℂ)
    (hf : AEStronglyMeasurable f change.physicalGaussian) :
    ∫ ξ, f (change.gaussianCoordinateMap ξ)
        ∂(balabanCMP116Dmu0 (Cube d L) lieDim) =
      ∫ A, f A ∂change.physicalGaussian := by
  have hfm :
      AEStronglyMeasurable f
        ((balabanCMP116Dmu0 (Cube d L) lieDim).map
          change.gaussianCoordinateMap) := by
    simpa [change.map_gaussianChangeOfVariables] using hf
  rw [← change.map_gaussianChangeOfVariables]
  exact (integral_map
    change.gaussianCoordinateMap_measurable.aemeasurable hfm).symm

/-- Canonical dictionary/root specialization of the Gaussian pushforward
integral rewrite.  The hypothesis `hpush` remains the full analytic Gaussian
source statement; the theorem only rewrites consumers through the canonical
coordinate map `D.gaussianRootMap root`. -/
theorem PhysicalGaugeCMP116GaussianChange.integral_ofDictionaryRoot
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (hpush :
      (balabanCMP116Dmu0 (Cube d L) lieDim).map
          (D.gaussianRootMap root) =
        physicalGaussian)
    (f : PhysicalGaugeOneCochain dPhys N Nc → ℂ)
    (hf : AEStronglyMeasurable f physicalGaussian) :
    ∫ ξ, f (D.gaussianRootMap root ξ)
        ∂(balabanCMP116Dmu0 (Cube d L) lieDim) =
      ∫ A, f A ∂physicalGaussian := by
  simpa using
    (PhysicalGaugeCMP116GaussianChange.integral_gaussianCoordinateMap_eq
      D
      (PhysicalGaugeCMP116GaussianChange.ofDictionaryRoot
        D root physicalGaussian hpush)
      f hf)

end PhysicalGaugeCMP116Dictionary

namespace PhysicalRootToCMP116OperatorTransport

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- The physical/CMP116 dictionary supplies the coordinate and projection
fields of the covariance-root transport record.  Only the kernel-bound
conversion remains a source/geometric hypothesis. -/
noncomputable def ofDictionary
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
    (cmpWeight : Cube d L → Cube d L → ℝ)
    (hkernelTransport :
      PhysicalCovarianceKernelBound root rootWeight →
        CMP116LinearMapKernelBound
          (cmp116OperatorOfPhysical
            D.fluctuationFieldContinuousLinearEquiv root)
          cmpWeight) :
    PhysicalRootToCMP116OperatorTransport
      (d := d) (L := L) (lieDim := lieDim) root rootWeight where
  bondToCube := D.siteMap.bondToCube
  coordinates := D.fluctuationFieldContinuousLinearEquiv
  support_projection :=
    D.fluctuationFieldContinuousLinearEquiv_support_projection
  cmpWeight := cmpWeight
  root_kernel_bound_transport := hkernelTransport

@[simp] theorem ofDictionary_coordinates
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
    (cmpWeight : Cube d L → Cube d L → ℝ)
    (hkernelTransport :
      PhysicalCovarianceKernelBound root rootWeight →
        CMP116LinearMapKernelBound
          (cmp116OperatorOfPhysical
            D.fluctuationFieldContinuousLinearEquiv root)
          cmpWeight) :
    (ofDictionary D root rootWeight cmpWeight hkernelTransport).coordinates =
      D.fluctuationFieldContinuousLinearEquiv :=
  rfl

end PhysicalRootToCMP116OperatorTransport

/-- Source-identification package for dictionary-backed localized Gaussian
activity data.

The proposition parameters should eventually be replaced by concrete named
source statements.  Keeping them separated prevents the source theorem from
collapsing Gaussian pushforward, root localization, Wilson Hessian
identification, and local activity construction into a single opaque field. -/
structure PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop) : Prop where
  gaussian_pushforward :
    (balabanCMP116Dmu0 (Cube d L) lieDim).map
        (D.gaussianRootMap root) =
      physicalGaussian
  root_localization : rootLocalization
  wilson_hessian_identification : wilsonHessianIdentification
  local_activity_construction : localActivityConstruction

namespace PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- The Gaussian-change record carried by the separated localized-Gaussian
source package.  This is only a repackaging of the explicit pushforward field;
the source package still has to prove that field. -/
noncomputable def gaussianChange
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (hsource :
      PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
        D root physicalGaussian rootLocalization
        wilsonHessianIdentification localActivityConstruction) :
    PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange D :=
  PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange.ofDictionaryRoot
    D root physicalGaussian hsource.gaussian_pushforward

@[simp] theorem gaussianChange_map
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (hsource :
      PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
        D root physicalGaussian rootLocalization
        wilsonHessianIdentification localActivityConstruction) :
    hsource.gaussianChange.gaussianCoordinateMap =
      D.gaussianRootMap root :=
  rfl

/-- Source-package form of the canonical Gaussian pushforward integral
rewrite.  This exposes the existing `gaussian_pushforward` field to downstream
activity estimates without restating the pushforward identity at every call
site. -/
theorem integral_gaussianRootMap_eq
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (hsource :
      PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
        D root physicalGaussian rootLocalization
        wilsonHessianIdentification localActivityConstruction)
    (f : PhysicalGaugeOneCochain dPhys N Nc → ℂ)
    (hf : AEStronglyMeasurable f physicalGaussian) :
    ∫ ξ, f (D.gaussianRootMap root ξ)
        ∂(balabanCMP116Dmu0 (Cube d L) lieDim) =
      ∫ A, f A ∂physicalGaussian :=
  PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange.integral_ofDictionaryRoot
    D root physicalGaussian hsource.gaussian_pushforward f hf

end PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses

/-- Build the existing localized-Gaussian activity certificate from separated
dictionary-backed source hypotheses, using the canonical amplitude
`H0 * weight`. -/
theorem physicalLocalizedGaussianActivityCertificate_of_cmp116Source
    {ι : Type*} {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound H0 : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport : ι → Finset (PhysicalBond dPhys N)}
    {weight : ι → ℝ}
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (hroot :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight)
    (hsource :
      PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
        D root physicalGaussian
        rootLocalization
        wilsonHessianIdentification
        localActivityConstruction)
    (hspectator :
      ∀ X, (physicalActivity X).spectatorSupport ⊆
        physicalActiveSupport X)
    (hfluctuation :
      ∀ X, (physicalActivity X).fluctuationSupport ⊆
        physicalActiveSupport X)
    (hH0 : 0 ≤ H0)
    (hweight : ∀ X, 0 ≤ weight X)
    (rawDecay :
      PhysicalGaugeRawActivityDecay physicalActivity weight H0) :
    PhysicalLocalizedGaussianActivityCertificate
      precision covariance root covNormBound rootNormBound covWeight
      rootWeight physicalActivity physicalActiveSupport
      (fun X => H0 * weight X) weight H0
      (PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
        D root physicalGaussian
        rootLocalization
        wilsonHessianIdentification
        localActivityConstruction) := by
  refine physicalLocalizedGaussianActivityCertificate_of_source
    hroot hsource hspectator hfluctuation ?_ hweight ?_ ?_
  · intro X
    exact mul_nonneg hH0 (hweight X)
  · intro X ψ φ
    exact rawDecay X ψ φ
  · intro X
    rfl

namespace BalabanCMP116LocalizedActivityFamily

variable {ι : Type*}
variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
variable {Ψ : Cube d L → Type*}

/-- Canonical CMP116 localized activity family induced by a dictionary and a
physical local-activity family. -/
noncomputable def ofDictionary
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (physicalActivity : ι → PhysicalGaugeLocalActivity dPhys N Nc)
    (physicalActiveSupport : ι → Finset (PhysicalBond dPhys N))
    (activity_stronglyMeasurable :
      ∀ X, ∀ ψ : ∀ c : Cube d L, Ψ c,
        StronglyMeasurable
          (fun ξ : CMP116FluctuationField d L lieDim =>
            ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
              D (fun X : ι => X) spectatorPull).activity
                physicalActivity X).globalEval ψ ξ))
    (spectatorSupport_subset :
      ∀ X, (physicalActivity X).spectatorSupport ⊆
        physicalActiveSupport X)
    (fluctuationSupport_subset :
      ∀ X, (physicalActivity X).fluctuationSupport ⊆
        physicalActiveSupport X)
    (activeSupport_subset_Omega :
      ∀ X, physicalActiveSupport X ⊆
        D.physicalBondsOfCells D.siteMap.Omega) :
    BalabanCMP116LocalizedActivityFamily
      (Cube d L) lieDim Ψ ι :=
  PhysicalGaugeCMP116ActivityAdapter.localizedFamilyOfDictionary
    D (fun X : ι => X) spectatorPull
    physicalActivity physicalActiveSupport activity_stronglyMeasurable
    spectatorSupport_subset fluctuationSupport_subset
    activeSupport_subset_Omega

@[simp] theorem ofDictionary_activity
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (physicalActivity : ι → PhysicalGaugeLocalActivity dPhys N Nc)
    (physicalActiveSupport : ι → Finset (PhysicalBond dPhys N))
    (activity_stronglyMeasurable :
      ∀ X, ∀ ψ : ∀ c : Cube d L, Ψ c,
        StronglyMeasurable
          (fun ξ : CMP116FluctuationField d L lieDim =>
            ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
              D (fun X : ι => X) spectatorPull).activity
                physicalActivity X).globalEval ψ ξ))
    (spectatorSupport_subset :
      ∀ X, (physicalActivity X).spectatorSupport ⊆
        physicalActiveSupport X)
    (fluctuationSupport_subset :
      ∀ X, (physicalActivity X).fluctuationSupport ⊆
        physicalActiveSupport X)
    (activeSupport_subset_Omega :
      ∀ X, physicalActiveSupport X ⊆
        D.physicalBondsOfCells D.siteMap.Omega)
    (X : ι) :
    (ofDictionary D spectatorPull physicalActivity physicalActiveSupport
      activity_stronglyMeasurable spectatorSupport_subset
      fluctuationSupport_subset activeSupport_subset_Omega).activity X =
      (PhysicalGaugeCMP116ActivityAdapter.ofDictionary
        D (fun X : ι => X) spectatorPull).activity physicalActivity X :=
  rfl

end BalabanCMP116LocalizedActivityFamily

namespace PhysicalGaugeCMP116ActivityTransport

variable {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
variable {lieDim : Nat} {Ψ : Cube d L → Type*}

/-- Construct the full physical/CMP116 activity transport record from the
dictionary-built localized family and a physical localized-Gaussian
certificate. -/
noncomputable def ofDictionary
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    {Λ : Finset (OmegaPolymerType HF z)}
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound H0 κ : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N)}
    {amplitude weight : OmegaPolymerType HF z → ℝ}
    {sourceConstruction : Prop}
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (hcert :
      PhysicalLocalizedGaussianActivityCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight physicalActivity physicalActiveSupport amplitude weight H0
        sourceConstruction)
    (activity_stronglyMeasurable :
      ∀ X, ∀ ψ : ∀ c : Cube d L, Ψ c,
        StronglyMeasurable
          (fun ξ : CMP116FluctuationField d L lieDim =>
            ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
              D (fun X : OmegaPolymerType HF z => X) spectatorPull).activity
                physicalActivity X).globalEval ψ ξ))
    (activeSupport_subset_Omega :
      ∀ X, physicalActiveSupport X ⊆
        D.physicalBondsOfCells D.siteMap.Omega)
    (activeSupport_subset_skeleton :
      ∀ X, X ∈ Λ →
        physicalActiveSupport X ⊆
          D.physicalBondsOfCells (skeleton HF X.val))
    (weight_domination :
      ∀ X, X ∈ Λ → weight X ≤ appendixFHoleExpWeight HF κ X.val) :
    PhysicalGaugeCMP116ActivityTransport (lieDim := lieDim) (Ψ := Ψ) HF z Λ
      precision covariance root covNormBound rootNormBound covWeight
      rootWeight physicalActivity physicalActiveSupport amplitude weight
      H0 κ sourceConstruction where
  certificate := hcert
  family :=
    BalabanCMP116LocalizedActivityFamily.ofDictionary
      D spectatorPull physicalActivity physicalActiveSupport
      activity_stronglyMeasurable
      hcert.spectator_support_subset
      hcert.fluctuation_support_subset
      activeSupport_subset_Omega
  spectatorTransport :=
    (PhysicalGaugeCMP116ActivityAdapter.ofDictionary
      D (fun X : OmegaPolymerType HF z => X) spectatorPull).pullSpectator
  fluctuationTransport := fun ξ b => D.pullFluctuationCochain ξ b
  globalEval_eq := by
    intro X ψ φ
    exact
      PhysicalGaugeCMP116ActivityAdapter.globalEval_activity_ofDictionary
        D (fun X : OmegaPolymerType HF z => X) spectatorPull
        physicalActivity X ψ φ
  activeSupport_subset_skeleton := by
    intro X hX
    simpa [BalabanCMP116LocalizedActivityFamily.ofDictionary] using
      ((PhysicalGaugeCMP116ActivityAdapter.activeSupport_ofDictionary_subset_iff
        D (fun X : OmegaPolymerType HF z => X) spectatorPull
        physicalActiveSupport X (skeleton HF X.val)).mpr
          (activeSupport_subset_skeleton X hX))
  weight_domination := weight_domination

@[simp] theorem ofDictionary_family_activity
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    {Λ : Finset (OmegaPolymerType HF z)}
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound H0 κ : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N)}
    {amplitude weight : OmegaPolymerType HF z → ℝ}
    {sourceConstruction : Prop}
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (hcert :
      PhysicalLocalizedGaussianActivityCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight physicalActivity physicalActiveSupport amplitude weight H0
        sourceConstruction)
    (activity_stronglyMeasurable :
      ∀ X, ∀ ψ : ∀ c : Cube d L, Ψ c,
        StronglyMeasurable
          (fun ξ : CMP116FluctuationField d L lieDim =>
            ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
              D (fun X : OmegaPolymerType HF z => X) spectatorPull).activity
                physicalActivity X).globalEval ψ ξ))
    (activeSupport_subset_Omega :
      ∀ X, physicalActiveSupport X ⊆
        D.physicalBondsOfCells D.siteMap.Omega)
    (activeSupport_subset_skeleton :
      ∀ X, X ∈ Λ →
        physicalActiveSupport X ⊆
          D.physicalBondsOfCells (skeleton HF X.val))
    (weight_domination :
      ∀ X, X ∈ Λ → weight X ≤ appendixFHoleExpWeight HF κ X.val)
    (X : OmegaPolymerType HF z) :
    ((ofDictionary (lieDim := lieDim) (Ψ := Ψ)
      D spectatorPull hcert activity_stronglyMeasurable
      activeSupport_subset_Omega activeSupport_subset_skeleton
      weight_domination).family.activity X) =
      (PhysicalGaugeCMP116ActivityAdapter.ofDictionary
        D (fun X : OmegaPolymerType HF z => X) spectatorPull).activity
          physicalActivity X :=
  rfl

end PhysicalGaugeCMP116ActivityTransport

end YangMills.RG

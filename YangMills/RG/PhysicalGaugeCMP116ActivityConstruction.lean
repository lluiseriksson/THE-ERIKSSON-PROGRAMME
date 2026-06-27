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

/-- The dictionary pull is bounded by the operator norm of the continuous
coordinate equivalence.  This exposes the finite dictionary constant without
claiming that the dictionary is an isometry. -/
theorem norm_pullFluctuationCochain_le
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (ξ : CMP116FluctuationField d L lieDim) :
    ‖D.pullFluctuationCochain ξ‖ ≤
      ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖ *
        ‖ξ‖ := by
  simpa [fluctuationFieldContinuousLinearEquiv_apply] using
    D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap.le_opNorm ξ

/-- The dictionary push is bounded by the operator norm of the inverse
continuous coordinate equivalence. -/
theorem norm_pushFluctuation_le
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A : PhysicalGaugeOneCochain dPhys N Nc) :
    ‖D.pushFluctuation A‖ ≤
      ‖D.fluctuationFieldContinuousLinearEquiv.symm.toContinuousLinearMap‖ *
        ‖A‖ := by
  simpa [fluctuationFieldContinuousLinearEquiv_symm_apply] using
    D.fluctuationFieldContinuousLinearEquiv.symm.toContinuousLinearMap.le_opNorm A

/-- The inverse dictionary norm controls the original CMP116 coordinate norm
through the pulled physical one-cochain. -/
theorem norm_le_inverse_opNorm_mul_norm_pullFluctuationCochain
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (ξ : CMP116FluctuationField d L lieDim) :
    ‖ξ‖ ≤
      ‖D.fluctuationFieldContinuousLinearEquiv.symm.toContinuousLinearMap‖ *
        ‖D.pullFluctuationCochain ξ‖ := by
  simpa [fluctuationFieldContinuousLinearEquiv_symm_apply] using
    D.fluctuationFieldContinuousLinearEquiv.symm.toContinuousLinearMap.le_opNorm
      (D.pullFluctuationCochain ξ)

/-- The forward dictionary norm controls the original physical one-cochain norm
through its pushed CMP116 coordinates. -/
theorem norm_le_opNorm_mul_norm_pushFluctuation
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A : PhysicalGaugeOneCochain dPhys N Nc) :
    ‖A‖ ≤
      ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖ *
        ‖D.pushFluctuation A‖ := by
  simpa [fluctuationFieldContinuousLinearEquiv_apply] using
    D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap.le_opNorm
      (D.pushFluctuation A)

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

/-- Operator-norm budget for the canonical dictionary/root Gaussian map.  This
is only the continuous-linear-map composition estimate; it does not identify a
Gaussian pushforward or a covariance. -/
theorem norm_gaussianRootMap_le
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc) :
    ‖D.gaussianRootMap root‖ ≤
      ‖root‖ *
        ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖ := by
  change
    ‖root.comp D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖ ≤
      ‖root‖ *
        ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖
  exact
    ContinuousLinearMap.opNorm_comp_le
      root
      D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap

/-- Pointwise norm budget for the dictionary/root Gaussian map. -/
theorem norm_gaussianRootMap_apply_le
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (ξ : CMP116FluctuationField d L lieDim) :
    ‖D.gaussianRootMap root ξ‖ ≤
      (‖root‖ *
        ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖) *
        ‖ξ‖ :=
  (D.gaussianRootMap root).le_of_opNorm_le
    (D.norm_gaussianRootMap_le root) ξ

/-- Operator-norm budget when the physical source theorem supplies an explicit
bound for the root. -/
theorem norm_gaussianRootMap_le_of_root_norm_le
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {rootNormBound : ℝ}
    (hroot : ‖root‖ ≤ rootNormBound) :
    ‖D.gaussianRootMap root‖ ≤
      rootNormBound *
        ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖ := by
  exact (D.norm_gaussianRootMap_le root).trans
    (mul_le_mul_of_nonneg_right hroot (norm_nonneg _))

/-- Pointwise dictionary/root Gaussian-map budget with an explicit source
root-norm bound. -/
theorem norm_gaussianRootMap_apply_le_of_root_norm_le
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {rootNormBound : ℝ}
    (hroot : ‖root‖ ≤ rootNormBound)
    (ξ : CMP116FluctuationField d L lieDim) :
    ‖D.gaussianRootMap root ξ‖ ≤
      (rootNormBound *
        ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖) *
        ‖ξ‖ :=
  (D.gaussianRootMap root).le_of_opNorm_le
    (D.norm_gaussianRootMap_le_of_root_norm_le hroot) ξ

/-- Operator-norm budget for the dictionary/root Gaussian map, consuming the
root-norm field of a localized covariance-root certificate. -/
theorem norm_gaussianRootMap_le_of_covarianceRootCertificate
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    (hcert :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight) :
    ‖D.gaussianRootMap root‖ ≤
      rootNormBound *
        ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖ :=
  D.norm_gaussianRootMap_le_of_root_norm_le hcert.root_norm_bound

/-- Pointwise dictionary/root Gaussian-map budget, consuming the root-norm field
of a localized covariance-root certificate. -/
theorem norm_gaussianRootMap_apply_le_of_covarianceRootCertificate
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    (hcert :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight)
    (ξ : CMP116FluctuationField d L lieDim) :
    ‖D.gaussianRootMap root ξ‖ ≤
      (rootNormBound *
        ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖) *
        ‖ξ‖ :=
  D.norm_gaussianRootMap_apply_le_of_root_norm_le
    hcert.root_norm_bound ξ

/-- The canonical physical Gaussian root map is the physical-coordinate
realization of the same root conjugated into CMP116 coordinates.

This is only exact dictionary algebra: it does not assert that the transported
map preserves the CMP116 product Gaussian law. -/
theorem gaussianRootMap_eq_coordinates_comp_cmp116OperatorOfPhysical
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc) :
    D.gaussianRootMap root =
      D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap.comp
        (cmp116OperatorOfPhysical
          D.fluctuationFieldContinuousLinearEquiv root) := by
  ext ξ
  simp [gaussianRootMap, cmp116OperatorOfPhysical]

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

/-- Structured CMP116 Gaussian-normalization source record.

The analytic content is still the source pushforward identity for the source
coordinate map.  This record separates the source coordinate and source
Gaussian measure from the dictionary/root specialization consumed downstream,
so later source work can replace the raw equality without changing every
localized-activity consumer. -/
structure CMP116GaussianPushforwardNormalization
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)) where
  sourceCoordinateMap :
    CMP116FluctuationField d L lieDim →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc
  sourcePhysicalGaussian :
    Measure (PhysicalGaugeOneCochain dPhys N Nc)
  coordinate_map_eq :
    sourceCoordinateMap = D.gaussianRootMap root
  physicalGaussian_eq :
    sourcePhysicalGaussian = physicalGaussian
  normalized_pushforward :
    (balabanCMP116Dmu0 (Cube d L) lieDim).map sourceCoordinateMap =
      sourcePhysicalGaussian

/-- Source/dictionary record identifying Balaban's Eq. (2.5)--(2.6) source
coordinate map with the repository dictionary/root Gaussian map. -/
structure CMP116GaussianCoordinateMapSource
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (sourceCoordinateMap :
      CMP116FluctuationField d L lieDim →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc) : Prop where
  coordinate_map_eq :
    sourceCoordinateMap = D.gaussianRootMap root

/-- Source/dictionary record identifying the source correlated fluctuation law
with the downstream physical Gaussian law consumed by raw-source records. -/
structure CMP116GaussianPhysicalLawSource
    (sourcePhysicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)) : Prop where
  physicalGaussian_eq :
    sourcePhysicalGaussian = physicalGaussian

/-- Source analytic record for the determinant/Jacobian-normalized
pushforward identity in CMP116 Eq. (2.5)--(2.6). -/
structure CMP116GaussianNormalizedPushforwardSource
    (sourceCoordinateMap :
      CMP116FluctuationField d L lieDim →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (sourcePhysicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)) : Prop where
  normalized_pushforward :
    (balabanCMP116Dmu0 (Cube d L) lieDim).map sourceCoordinateMap =
      sourcePhysicalGaussian

namespace CMP116GaussianPushforwardNormalization

/-- Build the structured Gaussian-normalization record from the exact
source-side coordinate map, source Gaussian law, dictionary identifications,
and determinant/Jacobian-normalized pushforward identity.

This is the source-facing endpoint for CMP116 Eq. (2.5)--(2.6): it names the
three facts that still have to be extracted from the paper and repository
dictionary, without pretending that this file proves the analytic
normalization theorem. -/
def of_sourceNormalizedChange
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    (sourceCoordinateMap :
      CMP116FluctuationField d L lieDim →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (sourcePhysicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (hcoordinate :
      sourceCoordinateMap = D.gaussianRootMap root)
    (hphysical :
      sourcePhysicalGaussian = physicalGaussian)
    (hnormalized :
      (balabanCMP116Dmu0 (Cube d L) lieDim).map sourceCoordinateMap =
        sourcePhysicalGaussian) :
    CMP116GaussianPushforwardNormalization D root physicalGaussian :=
  { sourceCoordinateMap := sourceCoordinateMap
    sourcePhysicalGaussian := sourcePhysicalGaussian
    coordinate_map_eq := hcoordinate
    physicalGaussian_eq := hphysical
    normalized_pushforward := hnormalized }

/-- Build the structured Gaussian-normalization record from the three
independent source records for coordinate-map identification, physical-law
identification, and normalized pushforward. -/
def of_sourceRecords
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    (sourceCoordinateMap :
      CMP116FluctuationField d L lieDim →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (sourcePhysicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (coordinateSource :
      CMP116GaussianCoordinateMapSource D root sourceCoordinateMap)
    (physicalLawSource :
      CMP116GaussianPhysicalLawSource
        sourcePhysicalGaussian physicalGaussian)
    (pushforwardSource :
      CMP116GaussianNormalizedPushforwardSource
        sourceCoordinateMap sourcePhysicalGaussian) :
    CMP116GaussianPushforwardNormalization D root physicalGaussian :=
  of_sourceNormalizedChange
    sourceCoordinateMap
    sourcePhysicalGaussian
    coordinateSource.coordinate_map_eq
    physicalLawSource.physicalGaussian_eq
    pushforwardSource.normalized_pushforward

/-- Recover the dictionary/root Gaussian pushforward consumed by existing
localized-activity source packages from the structured normalization record. -/
theorem gaussian_pushforward
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    (h :
      CMP116GaussianPushforwardNormalization D root physicalGaussian) :
    (balabanCMP116Dmu0 (Cube d L) lieDim).map
        (D.gaussianRootMap root) =
      physicalGaussian := by
  calc
    (balabanCMP116Dmu0 (Cube d L) lieDim).map
        (D.gaussianRootMap root)
        =
      (balabanCMP116Dmu0 (Cube d L) lieDim).map
        h.sourceCoordinateMap := by
          rw [← h.coordinate_map_eq]
    _ = h.sourcePhysicalGaussian := h.normalized_pushforward
    _ = physicalGaussian := h.physicalGaussian_eq

end CMP116GaussianPushforwardNormalization

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

/-- Dictionary-specialized localized CMP116 root map.  A physical kernel bound,
together with the dictionary kernel-bound transport and a finite-range CMP116
weight, gives the exact input/output support package consumed by later local
activity constructors. -/
noncomputable def localizedRootLinearMap_ofDictionary
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R) :
    CMP116LocalizedLinearMap
      (d := d) (L := L) (lieDim := lieDim)
      Xin
      (cmp116FiniteRangeClosure dist R Xin) :=
  localizedRootLinearMap
    (ofDictionary D root rootWeight cmpWeight hkernelTransport)
    hkernel dist R Xin hfinite

@[simp] theorem localizedRootLinearMap_ofDictionary_toContinuousLinearMap
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R) :
    (localizedRootLinearMap_ofDictionary
      D root rootWeight cmpWeight hkernelTransport
      hkernel dist R Xin hfinite).toContinuousLinearMap =
        (cmp116OperatorOfPhysical
          D.fluctuationFieldContinuousLinearEquiv root).comp
        (cmp116FieldProjection Xin) :=
  rfl

/-- Finite sum of dictionary-specialized localized root pieces over a supplied
finite family of input cube sets.  This is only support algebra for the sum of
projected root maps; it does not assert that these pieces reconstruct the full
root operator. -/
noncomputable def localizedRootLinearMapFinsetSum_ofDictionary
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R) :
    CMP116LocalizedLinearMap
      (d := d) (L := L) (lieDim := lieDim)
      (I.biUnion Xin)
      (I.biUnion fun i => cmp116FiniteRangeClosure dist R (Xin i)) :=
  CMP116LocalizedLinearMap.finsetSumVarying
    I
    Xin
    (fun i => cmp116FiniteRangeClosure dist R (Xin i))
    (fun i =>
      localizedRootLinearMap_ofDictionary
        D root rootWeight cmpWeight hkernelTransport
        hkernel dist R (Xin i) hfinite)

@[simp] theorem localizedRootLinearMapFinsetSum_ofDictionary_toContinuousLinearMap
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R) :
    (localizedRootLinearMapFinsetSum_ofDictionary
      I D root rootWeight cmpWeight hkernelTransport
      hkernel dist R Xin hfinite).toContinuousLinearMap =
      I.sum fun i =>
        (cmp116OperatorOfPhysical
          D.fluctuationFieldContinuousLinearEquiv root).comp
          (cmp116FieldProjection (Xin i)) := by
  simp [localizedRootLinearMapFinsetSum_ofDictionary]

/-- A finite sum of dictionary-localized root pieces depends only on the union
of its declared input cube sets. -/
theorem localizedRootLinearMapFinsetSum_ofDictionary_eq_of_agreeOn
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn (I.biUnion Xin) ξ η) :
    (localizedRootLinearMapFinsetSum_ofDictionary
      I D root rootWeight cmpWeight hkernelTransport
      hkernel dist R Xin hfinite).toContinuousLinearMap ξ =
      (localizedRootLinearMapFinsetSum_ofDictionary
        I D root rootWeight cmpWeight hkernelTransport
        hkernel dist R Xin hfinite).toContinuousLinearMap η :=
  (localizedRootLinearMapFinsetSum_ofDictionary
    I D root rootWeight cmpWeight hkernelTransport
    hkernel dist R Xin hfinite).eq_of_agreeOn hξη

/-- A finite sum of dictionary-localized root pieces is zero outside the union
of the corresponding finite-range closures. -/
theorem localizedRootLinearMapFinsetSum_ofDictionary_apply_eq_zero_outside
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R)
    (ξ : CMP116FluctuationField d L lieDim)
    {q : Cube d L}
    (hq :
      q ∉ I.biUnion fun i => cmp116FiniteRangeClosure dist R (Xin i))
    (a : Fin lieDim) :
    (localizedRootLinearMapFinsetSum_ofDictionary
      I D root rootWeight cmpWeight hkernelTransport
      hkernel dist R Xin hfinite).toContinuousLinearMap ξ q a = 0 :=
  (localizedRootLinearMapFinsetSum_ofDictionary
    I D root rootWeight cmpWeight hkernelTransport
    hkernel dist R Xin hfinite).apply_eq_zero_outside ξ hq a

/-- Pulling a finite sum of dictionary-localized root pieces to physical
coordinates preserves the declared input-agreement consequence. -/
theorem localizedRootLinearMapFinsetSum_ofDictionary_pull_eq_of_agreeOn
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn (I.biUnion Xin) ξ η) :
    D.pullFluctuationCochain
        ((localizedRootLinearMapFinsetSum_ofDictionary
          I D root rootWeight cmpWeight hkernelTransport
          hkernel dist R Xin hfinite).toContinuousLinearMap ξ) =
      D.pullFluctuationCochain
        ((localizedRootLinearMapFinsetSum_ofDictionary
          I D root rootWeight cmpWeight hkernelTransport
          hkernel dist R Xin hfinite).toContinuousLinearMap η) := by
  rw [localizedRootLinearMapFinsetSum_ofDictionary_eq_of_agreeOn
    I D root rootWeight cmpWeight hkernelTransport
    hkernel dist R Xin hfinite hξη]

/-- Pulling a finite sum of dictionary-localized root pieces to physical
coordinates is zero on every physical bond assigned outside the union of the
piece output closures. -/
theorem localizedRootLinearMapFinsetSum_ofDictionary_pull_apply_eq_zero_outside
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R)
    (ξ : CMP116FluctuationField d L lieDim)
    {b : PhysicalBond dPhys N}
    (hb :
      D.siteMap.bondToCube b ∉
        I.biUnion fun i => cmp116FiniteRangeClosure dist R (Xin i)) :
    D.pullFluctuationCochain
        ((localizedRootLinearMapFinsetSum_ofDictionary
          I D root rootWeight cmpWeight hkernelTransport
          hkernel dist R Xin hfinite).toContinuousLinearMap ξ) b = 0 := by
  apply (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).injective
  funext a
  let qa : CMP116CoordIndex d L lieDim := D.coordEquiv.symm (b, a)
  have hq :
      qa.1 ∉ I.biUnion fun i => cmp116FiniteRangeClosure dist R (Xin i) := by
    simpa [qa, D.coordEquiv_symm_cell b a] using hb
  have hzero :
      (localizedRootLinearMapFinsetSum_ofDictionary
        I D root rootWeight cmpWeight hkernelTransport
        hkernel dist R Xin hfinite).toContinuousLinearMap ξ qa.1 qa.2 = 0 :=
    localizedRootLinearMapFinsetSum_ofDictionary_apply_eq_zero_outside
      I D root rootWeight cmpWeight hkernelTransport
      hkernel dist R Xin hfinite ξ hq qa.2
  simpa [PhysicalGaugeCMP116Dictionary.pullFluctuationCochain,
    PhysicalGaugeCMP116Dictionary.sunLieCoordOfScalars, qa] using hzero

/-- A physical local activity evaluated on the physical pullback of a finite
sum of dictionary-localized root pieces depends only on the declared CMP116
input cube union.

This is only the `LocalActivity` consumer of the pulled-output equality above:
it does not assert a Gaussian pushforward identity, reconstruct the full
covariance root, or prove any activity-decay estimate. -/
theorem localizedRootLinearMapFinsetSum_ofDictionary_activity_globalEval_eq_of_agreeOn
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R)
    (activity : PhysicalGaugeLocalActivity dPhys N Nc)
    (ψ : PhysicalGaugeField dPhys N Nc)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn (I.biUnion Xin) ξ η) :
    activity.globalEval ψ
        (D.pullFluctuationCochain
          ((localizedRootLinearMapFinsetSum_ofDictionary
            I D root rootWeight cmpWeight hkernelTransport
            hkernel dist R Xin hfinite).toContinuousLinearMap ξ)) =
      activity.globalEval ψ
        (D.pullFluctuationCochain
          ((localizedRootLinearMapFinsetSum_ofDictionary
            I D root rootWeight cmpWeight hkernelTransport
            hkernel dist R Xin hfinite).toContinuousLinearMap η)) := by
  refine LocalActivity.globalEval_eq_of_agreeOn activity ?_ ?_
  · intro _b _hb
    rfl
  · intro b _hb
    have hpull :
        D.pullFluctuationCochain
            ((localizedRootLinearMapFinsetSum_ofDictionary
              I D root rootWeight cmpWeight hkernelTransport
              hkernel dist R Xin hfinite).toContinuousLinearMap ξ) =
          D.pullFluctuationCochain
            ((localizedRootLinearMapFinsetSum_ofDictionary
              I D root rootWeight cmpWeight hkernelTransport
              hkernel dist R Xin hfinite).toContinuousLinearMap η) :=
      localizedRootLinearMapFinsetSum_ofDictionary_pull_eq_of_agreeOn
        I D root rootWeight cmpWeight hkernelTransport
        hkernel dist R Xin hfinite hξη
    exact congrFun (congrArg (fun φ => φ.ofLp) hpull) b

/-- Exact activity-local agreement between the full physical Gaussian-root map
and a localized root-piece realization.

The equality is required only on the fluctuation support of the physical local
activity.  In particular, this proposition does not assert equality of the two
maps as global operators. -/
def ActivityLocalRootPieceAgreement
    (activity : PhysicalGaugeLocalActivity dPhys N Nc)
    (fullRoot rootPieces :
      CMP116FluctuationField d L lieDim →
        PhysicalGaugeOneCochain dPhys N Nc) : Prop :=
  ∀ ζ : CMP116FluctuationField d L lieDim,
    AgreeOn activity.fluctuationSupport
      (fun b => fullRoot ζ b)
      (fun b => rootPieces ζ b)

omit [NeZero L] in
/-- Agreement on a declared physical active support restricts to the exact
activity-local root-piece obligation whenever the fluctuation support is
contained in that active support. -/
theorem activityLocalRootPieceAgreement_of_agreeOn_activeSupport
    (activity : PhysicalGaugeLocalActivity dPhys N Nc)
    (fullRoot rootPieces :
      CMP116FluctuationField d L lieDim →
        PhysicalGaugeOneCochain dPhys N Nc)
    (activeSupport : Finset (PhysicalBond dPhys N))
    (hfluctuation : activity.fluctuationSupport ⊆ activeSupport)
    (hrootPieces :
      ∀ ζ : CMP116FluctuationField d L lieDim,
        AgreeOn activeSupport
          (fun b => fullRoot ζ b)
          (fun b => rootPieces ζ b)) :
    ActivityLocalRootPieceAgreement activity fullRoot rootPieces := by
  intro ζ b hb
  exact hrootPieces ζ b (hfluctuation hb)

/-- CMP116 agreement of a candidate root-piece map on a localization domain
pulls back to the physical activity-local agreement required by the full
dictionary Gaussian-root consumer.

This is only dictionary and support transport.  It does not prove the CMP116
agreement premise or any global equality of root operators. -/
theorem gaussianRootMap_agreeOn_activity_fluctuationSupport_of_cmp116_agreeOn
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (rootPieces :
      CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim)
    (Xloc : Finset (Cube d L))
    (activity : PhysicalGaugeLocalActivity dPhys N Nc)
    (hfluctuation :
      activity.fluctuationSupport ⊆ D.physicalBondsOfCells Xloc)
    (hrootPiecesCMP :
      ∀ ζ : CMP116FluctuationField d L lieDim,
        AgreeOn Xloc
          ((cmp116OperatorOfPhysical
            D.fluctuationFieldContinuousLinearEquiv root) ζ)
          (rootPieces ζ)) :
    ActivityLocalRootPieceAgreement activity
      (fun ζ => D.gaussianRootMap root ζ)
      (fun ζ => D.pullFluctuationCochain (rootPieces ζ)) := by
  intro ζ b hb
  have hpull :
      AgreeOn (D.physicalBondsOfCells Xloc)
        (D.pullFluctuationCochain
          ((cmp116OperatorOfPhysical
            D.fluctuationFieldContinuousLinearEquiv root) ζ))
        (D.pullFluctuationCochain (rootPieces ζ)) :=
    D.pullFluctuationCochain_agreeOn (hrootPiecesCMP ζ)
  have hmap :
      D.gaussianRootMap root ζ =
        D.pullFluctuationCochain
          ((cmp116OperatorOfPhysical
            D.fluctuationFieldContinuousLinearEquiv root) ζ) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T => T ζ)
        (D.gaussianRootMap_eq_coordinates_comp_cmp116OperatorOfPhysical root)
  exact
    (congrArg (fun A : PhysicalGaugeOneCochain dPhys N Nc => A.ofLp b)
      hmap).trans (hpull b (hfluctuation hb))

/-- Promote the input-locality of a finite sum of dictionary-localized root
pieces to the physical activity evaluated on the full dictionary Gaussian-root
map, provided the finite sum agrees with that root map on the activity's
fluctuation support.

The agreement hypothesis is deliberately activity-local.  It does not assert
that the finite pieces reconstruct the full covariance root as operators. -/
theorem gaussianRootMap_activity_globalEval_eq_of_agreeOn_of_localizedRootLinearMapFinsetSum
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R)
    (activity : PhysicalGaugeLocalActivity dPhys N Nc)
    (ψ : PhysicalGaugeField dPhys N Nc)
    (hrootPieces :
      ActivityLocalRootPieceAgreement activity
        (fun ζ => D.gaussianRootMap root ζ)
        (fun ζ =>
          D.pullFluctuationCochain
            ((localizedRootLinearMapFinsetSum_ofDictionary
              I D root rootWeight cmpWeight hkernelTransport
              hkernel dist R Xin hfinite).toContinuousLinearMap ζ)))
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn (I.biUnion Xin) ξ η) :
    activity.globalEval ψ
        (fun b => (D.gaussianRootMap root ξ) b) =
      activity.globalEval ψ
        (fun b => (D.gaussianRootMap root η) b) := by
  calc
    activity.globalEval ψ
        (fun b => (D.gaussianRootMap root ξ) b) =
      activity.globalEval ψ
        (D.pullFluctuationCochain
          ((localizedRootLinearMapFinsetSum_ofDictionary
            I D root rootWeight cmpWeight hkernelTransport
            hkernel dist R Xin hfinite).toContinuousLinearMap ξ)) := by
        refine LocalActivity.globalEval_eq_of_agreeOn activity ?_ ?_
        · intro _b _hb
          rfl
        · exact hrootPieces ξ
    _ =
      activity.globalEval ψ
        (D.pullFluctuationCochain
          ((localizedRootLinearMapFinsetSum_ofDictionary
            I D root rootWeight cmpWeight hkernelTransport
            hkernel dist R Xin hfinite).toContinuousLinearMap η)) :=
        localizedRootLinearMapFinsetSum_ofDictionary_activity_globalEval_eq_of_agreeOn
          I D root rootWeight cmpWeight hkernelTransport
          hkernel dist R Xin hfinite activity ψ hξη
    _ =
      activity.globalEval ψ
        (fun b => (D.gaussianRootMap root η) b) := by
        symm
        refine LocalActivity.globalEval_eq_of_agreeOn activity ?_ ?_
        · intro _b _hb
          rfl
        · exact hrootPieces η

/-- A finite sum of physical local activities evaluated on the physical
pullback of a finite dictionary-localized root-piece sum also depends only on
the declared CMP116 input cube union. -/
theorem localizedRootLinearMapFinsetSum_ofDictionary_activityFamily_sum_globalEval_eq_of_agreeOn
    {ι κ : Type*} [DecidableEq ι]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R)
    (J : Finset κ)
    (activity : κ → PhysicalGaugeLocalActivity dPhys N Nc)
    (ψ : PhysicalGaugeField dPhys N Nc)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn (I.biUnion Xin) ξ η) :
    (∑ X ∈ J,
        (activity X).globalEval ψ
          (D.pullFluctuationCochain
            ((localizedRootLinearMapFinsetSum_ofDictionary
              I D root rootWeight cmpWeight hkernelTransport
              hkernel dist R Xin hfinite).toContinuousLinearMap ξ))) =
      (∑ X ∈ J,
        (activity X).globalEval ψ
          (D.pullFluctuationCochain
            ((localizedRootLinearMapFinsetSum_ofDictionary
              I D root rootWeight cmpWeight hkernelTransport
              hkernel dist R Xin hfinite).toContinuousLinearMap η))) := by
  refine Finset.sum_congr rfl ?_
  intro X _hX
  exact
    localizedRootLinearMapFinsetSum_ofDictionary_activity_globalEval_eq_of_agreeOn
      I D root rootWeight cmpWeight hkernelTransport
      hkernel dist R Xin hfinite (activity X) ψ hξη

/-- Packaged `LocalActivity.finsetSum` version of the finite-family consumer. -/
theorem localizedRootLinearMapFinsetSum_ofDictionary_activityFamily_finsetSum_globalEval_eq_of_agreeOn
    {ι κ : Type*} [DecidableEq ι] [DecidableEq (PhysicalBond dPhys N)]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R)
    (J : Finset κ)
    (activity : κ → PhysicalGaugeLocalActivity dPhys N Nc)
    (ψ : PhysicalGaugeField dPhys N Nc)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn (I.biUnion Xin) ξ η) :
    (LocalActivity.finsetSum J activity).globalEval ψ
        (D.pullFluctuationCochain
          ((localizedRootLinearMapFinsetSum_ofDictionary
            I D root rootWeight cmpWeight hkernelTransport
            hkernel dist R Xin hfinite).toContinuousLinearMap ξ)) =
      (LocalActivity.finsetSum J activity).globalEval ψ
        (D.pullFluctuationCochain
          ((localizedRootLinearMapFinsetSum_ofDictionary
            I D root rootWeight cmpWeight hkernelTransport
            hkernel dist R Xin hfinite).toContinuousLinearMap η)) := by
  simpa [LocalActivity.globalEval_finsetSum] using
    localizedRootLinearMapFinsetSum_ofDictionary_activityFamily_sum_globalEval_eq_of_agreeOn
      I D root rootWeight cmpWeight hkernelTransport
      hkernel dist R Xin hfinite J activity ψ hξη

/-- Appendix-F-style Mayer-cover product version of the finite-family
consumer.  It propagates the finite-piece root-sum input-dependence through
the raw Mayer factors `exp(H) - 1`. -/
theorem localizedRootLinearMapFinsetSum_ofDictionary_mayerCoverActivity_globalEval_eq_of_agreeOn
    {ι κ : Type*} [DecidableEq ι] [DecidableEq (PhysicalBond dPhys N)]
    (I : Finset ι)
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
          cmpWeight)
    (hkernel : PhysicalCovarianceKernelBound root rootWeight)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ)
    (Xin : ι → Finset (Cube d L))
    (hfinite : CMP116KernelFiniteRange cmpWeight dist R)
    (J : Finset κ)
    (activity : κ → PhysicalGaugeLocalActivity dPhys N Nc)
    (ψ : PhysicalGaugeField dPhys N Nc)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn (I.biUnion Xin) ξ η) :
    (LocalActivity.mayerCoverActivity J activity).globalEval ψ
        (D.pullFluctuationCochain
          ((localizedRootLinearMapFinsetSum_ofDictionary
            I D root rootWeight cmpWeight hkernelTransport
            hkernel dist R Xin hfinite).toContinuousLinearMap ξ)) =
      (LocalActivity.mayerCoverActivity J activity).globalEval ψ
        (D.pullFluctuationCochain
          ((localizedRootLinearMapFinsetSum_ofDictionary
            I D root rootWeight cmpWeight hkernelTransport
            hkernel dist R Xin hfinite).toContinuousLinearMap η)) := by
  rw [LocalActivity.globalEval_mayerCoverActivity]
  rw [LocalActivity.globalEval_mayerCoverActivity]
  refine Finset.prod_congr rfl ?_
  intro X _hX
  exact congrArg (fun z : ℂ => Complex.exp z - 1)
    (localizedRootLinearMapFinsetSum_ofDictionary_activity_globalEval_eq_of_agreeOn
      I D root rootWeight cmpWeight hkernelTransport
      hkernel dist R Xin hfinite (activity X.1) ψ hξη)

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

/-- Compatibility source package that adds the unfolded physical raw pointwise
estimate to the separated localized-Gaussian source facts.

This is intentionally still a source package: the new field is the analytic
raw estimate itself, not a disguised theorem proving it.  The canonical source
API should eventually replace this compatibility layer with structured source
objects and source estimates. -/
structure PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
    {ι : Type*} {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (physicalActivity : ι → PhysicalGaugeLocalActivity dPhys N Nc)
    (weight : ι → ℝ)
    (H0 : ℝ)
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop) : Prop
    extends
      PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
        D root physicalGaussian rootLocalization
        wilsonHessianIdentification localActivityConstruction where
  raw_pointwise_decay :
    ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
      ‖(physicalActivity X).globalEval ψ φ‖ ≤ H0 * weight X

namespace PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- Build the localized-Gaussian source package from the structured CMP116
Gaussian-normalization record and the remaining separated source facts. -/
def of_gaussianNormalization
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (gaussian_normalization :
      PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization
        D root physicalGaussian)
    (root_localization : rootLocalization)
    (wilson_hessian_identification : wilsonHessianIdentification)
    (local_activity_construction : localActivityConstruction) :
    PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
      D root physicalGaussian rootLocalization
      wilsonHessianIdentification localActivityConstruction where
  gaussian_pushforward := gaussian_normalization.gaussian_pushforward
  root_localization := root_localization
  wilson_hessian_identification := wilson_hessian_identification
  local_activity_construction := local_activity_construction

/-- Build the localized-Gaussian source package directly from the three
CMP116 Eq. (2.5)--(2.6) Gaussian source records and the remaining separated
source facts.  This keeps the caller-facing boundary at the exact source
records, rather than requiring callers to preassemble the intermediate
normalization record. -/
def of_sourceRecords
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (sourceCoordinateMap :
      CMP116FluctuationField d L lieDim →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (sourcePhysicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (coordinateSource :
      PhysicalGaugeCMP116Dictionary.CMP116GaussianCoordinateMapSource
        D root sourceCoordinateMap)
    (physicalLawSource :
      PhysicalGaugeCMP116Dictionary.CMP116GaussianPhysicalLawSource
        sourcePhysicalGaussian physicalGaussian)
    (pushforwardSource :
      PhysicalGaugeCMP116Dictionary.CMP116GaussianNormalizedPushforwardSource
        sourceCoordinateMap sourcePhysicalGaussian)
    (root_localization : rootLocalization)
    (wilson_hessian_identification : wilsonHessianIdentification)
    (local_activity_construction : localActivityConstruction) :
    PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
      D root physicalGaussian rootLocalization
      wilsonHessianIdentification localActivityConstruction :=
  of_gaussianNormalization
    (PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization.of_sourceRecords
      sourceCoordinateMap sourcePhysicalGaussian
      coordinateSource physicalLawSource pushforwardSource)
    root_localization wilson_hessian_identification
    local_activity_construction

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

/-- Source-package Gaussian integral rewrite specialized to a physical local
activity.  This is the concrete consumer form needed by source-faithful
activity estimates: the physical fluctuation field is first viewed as a
one-cochain `A`, then pulled back to CMP116 product coordinates through
`D.gaussianRootMap root`. -/
theorem integral_physicalActivity_gaussianRootMap_eq
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
    (activity : PhysicalGaugeLocalActivity dPhys N Nc)
    (ψ : PhysicalGaugeField dPhys N Nc)
    (hf :
      AEStronglyMeasurable
        (fun A : PhysicalGaugeOneCochain dPhys N Nc =>
          activity.globalEval ψ (fun b => A b))
        physicalGaussian) :
    ∫ ξ, activity.globalEval ψ
          (fun b => (D.gaussianRootMap root ξ) b)
        ∂(balabanCMP116Dmu0 (Cube d L) lieDim) =
      ∫ A, activity.globalEval ψ
          (fun b => A b)
        ∂physicalGaussian :=
  hsource.integral_gaussianRootMap_eq
    (fun A : PhysicalGaugeOneCochain dPhys N Nc =>
      activity.globalEval ψ (fun b => A b))
    hf

end PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses

namespace PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- Build the raw localized-Gaussian source package from the structured CMP116
Gaussian-normalization record plus the remaining raw-source facts. -/
def of_gaussianNormalization
    {ι : Type*}
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {physicalActivity : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {weight : ι → ℝ}
    {H0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (gaussian_normalization :
      PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization
        D root physicalGaussian)
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
  toPhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses :=
    PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.of_gaussianNormalization
      gaussian_normalization root_localization wilson_hessian_identification
      local_activity_construction
  raw_pointwise_decay := raw_pointwise_decay

/-- Build the raw localized-Gaussian source package directly from the three
CMP116 Eq. (2.5)--(2.6) Gaussian source records plus the remaining raw-source
facts.  This is the raw analogue of
`PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.of_sourceRecords`.
-/
def of_sourceRecords
    {ι : Type*}
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {physicalActivity : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {weight : ι → ℝ}
    {H0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (sourceCoordinateMap :
      CMP116FluctuationField d L lieDim →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (sourcePhysicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (coordinateSource :
      PhysicalGaugeCMP116Dictionary.CMP116GaussianCoordinateMapSource
        D root sourceCoordinateMap)
    (physicalLawSource :
      PhysicalGaugeCMP116Dictionary.CMP116GaussianPhysicalLawSource
        sourcePhysicalGaussian physicalGaussian)
    (pushforwardSource :
      PhysicalGaugeCMP116Dictionary.CMP116GaussianNormalizedPushforwardSource
        sourceCoordinateMap sourcePhysicalGaussian)
    (root_localization : rootLocalization)
    (wilson_hessian_identification : wilsonHessianIdentification)
    (local_activity_construction : localActivityConstruction)
    (raw_pointwise_decay :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        ‖(physicalActivity X).globalEval ψ φ‖ ≤ H0 * weight X) :
    PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
      D root physicalGaussian physicalActivity weight H0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction :=
  of_gaussianNormalization
    (PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization.of_sourceRecords
      sourceCoordinateMap sourcePhysicalGaussian
      coordinateSource physicalLawSource pushforwardSource)
    root_localization wilson_hessian_identification
    local_activity_construction raw_pointwise_decay

end PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses

/-- The raw-source compatibility package exposes the existing physical raw
decay predicate by projection from its unfolded pointwise estimate. -/
theorem physicalGaugeRawActivityDecay_of_cmp116RawSource
    {ι : Type*} {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {physicalActivity : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {weight : ι → ℝ}
    {H0 : ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (hsource :
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        D root physicalGaussian physicalActivity weight H0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    PhysicalGaugeRawActivityDecay physicalActivity weight H0 := by
  intro X ψ φ
  exact hsource.raw_pointwise_decay X ψ φ

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

/-- Build the existing localized-Gaussian activity certificate from the
raw-source compatibility package.  The source package supplies the unfolded
pointwise raw estimate, so no separate `PhysicalGaugeRawActivityDecay` premise
is needed. -/
theorem physicalLocalizedGaussianActivityCertificate_of_cmp116RawSource
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
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        D root physicalGaussian physicalActivity weight H0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction)
    (hspectator :
      ∀ X, (physicalActivity X).spectatorSupport ⊆
        physicalActiveSupport X)
    (hfluctuation :
      ∀ X, (physicalActivity X).fluctuationSupport ⊆
        physicalActiveSupport X)
    (hH0 : 0 ≤ H0)
    (hweight : ∀ X, 0 ≤ weight X) :
    PhysicalLocalizedGaussianActivityCertificate
      precision covariance root covNormBound rootNormBound covWeight
      rootWeight physicalActivity physicalActiveSupport
      (fun X => H0 * weight X) weight H0
      (PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        D root physicalGaussian physicalActivity weight H0
        rootLocalization
        wilsonHessianIdentification
        localActivityConstruction) := by
  refine physicalLocalizedGaussianActivityCertificate_of_source
    hroot hsource hspectator hfluctuation ?_ hweight ?_ ?_
  · intro X
    exact mul_nonneg hH0 (hweight X)
  · intro X ψ φ
    exact hsource.raw_pointwise_decay X ψ φ
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

/-- A physical/CMP116 activity transport package carries enough root-certificate
data to bound the dictionary Gaussian coordinate map.  The dictionary constant
is explicit; no isometry or Gaussian-law claim is made. -/
theorem norm_gaussianRootMap_le
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
    (T :
      PhysicalGaugeCMP116ActivityTransport (lieDim := lieDim) (Ψ := Ψ) HF z Λ
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight physicalActivity physicalActiveSupport amplitude weight
        H0 κ sourceConstruction) :
    ‖D.gaussianRootMap root‖ ≤
      rootNormBound *
        ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖ :=
  D.norm_gaussianRootMap_le_of_covarianceRootCertificate
    T.certificate.root_certificate

/-- Pointwise version of the transport-level dictionary Gaussian-map norm
budget. -/
theorem norm_gaussianRootMap_apply_le
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
    (T :
      PhysicalGaugeCMP116ActivityTransport (lieDim := lieDim) (Ψ := Ψ) HF z Λ
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight physicalActivity physicalActiveSupport amplitude weight
        H0 κ sourceConstruction)
    (ξ : CMP116FluctuationField d L lieDim) :
    ‖D.gaussianRootMap root ξ‖ ≤
      (rootNormBound *
        ‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖) *
        ‖ξ‖ :=
  D.norm_gaussianRootMap_apply_le_of_covarianceRootCertificate
    T.certificate.root_certificate ξ

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

namespace PhysicalGaugeCMP116ActivityTransport

/-- Canonical physical/CMP116 activity transport record constructed directly
from the raw-source compatibility package.

This is the namespaced entry point for the raw-source route.  It is only the
composition of the raw-source certificate constructor with the existing
dictionary-backed transport constructor; all analytic raw-source, root,
measurability, support, and weight-domination facts remain explicit
hypotheses. -/
noncomputable def of_cmp116RawSource
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
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
    {weight : OmegaPolymerType HF z → ℝ}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (hroot :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight)
    (hsource :
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        D root physicalGaussian physicalActivity weight H0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction)
    (hspectator :
      ∀ X, (physicalActivity X).spectatorSupport ⊆
        physicalActiveSupport X)
    (hfluctuation :
      ∀ X, (physicalActivity X).fluctuationSupport ⊆
        physicalActiveSupport X)
    (hH0 : 0 ≤ H0)
    (hweight : ∀ X, 0 ≤ weight X)
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
      rootWeight physicalActivity physicalActiveSupport
      (fun X => H0 * weight X) weight H0 κ
      (PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        D root physicalGaussian physicalActivity weight H0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :=
  ofDictionary (lieDim := lieDim) (Ψ := Ψ)
    D spectatorPull
    (physicalLocalizedGaussianActivityCertificate_of_cmp116RawSource
      hroot hsource hspectator hfluctuation hH0 hweight)
    activity_stronglyMeasurable
    activeSupport_subset_Omega
    activeSupport_subset_skeleton
    weight_domination

end PhysicalGaugeCMP116ActivityTransport

/-- Construct the full physical/CMP116 activity transport record directly from
the raw-source compatibility package.  This only composes existing adapters:
the raw pointwise estimate is still the `hsource.raw_pointwise_decay` field. -/
noncomputable def physicalGaugeCMP116ActivityTransport_of_cmp116RawSource
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
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
    {weight : OmegaPolymerType HF z → ℝ}
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (hroot :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight)
    (hsource :
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        D root physicalGaussian physicalActivity weight H0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction)
    (hspectator :
      ∀ X, (physicalActivity X).spectatorSupport ⊆
        physicalActiveSupport X)
    (hfluctuation :
      ∀ X, (physicalActivity X).fluctuationSupport ⊆
        physicalActiveSupport X)
    (hH0 : 0 ≤ H0)
    (hweight : ∀ X, 0 ≤ weight X)
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
      rootWeight physicalActivity physicalActiveSupport
      (fun X => H0 * weight X) weight H0 κ
      (PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        D root physicalGaussian physicalActivity weight H0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :=
  PhysicalGaugeCMP116ActivityTransport.of_cmp116RawSource
    (lieDim := lieDim) (Ψ := Ψ) D spectatorPull hroot hsource
    hspectator hfluctuation hH0 hweight
    activity_stronglyMeasurable
    activeSupport_subset_Omega
    activeSupport_subset_skeleton
    weight_domination

/-- A raw-source package plus dictionary/support transport hypotheses produces
the Appendix-F support package for the canonically transported CMP116 family. -/
theorem physicalGaugeCMP116SupportHypotheses_of_cmp116RawSource
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
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
    {weight : OmegaPolymerType HF z → ℝ}
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (hroot :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight)
    (hsource :
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        D root physicalGaussian physicalActivity weight H0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction)
    (hspectator :
      ∀ X, (physicalActivity X).spectatorSupport ⊆
        physicalActiveSupport X)
    (hfluctuation :
      ∀ X, (physicalActivity X).fluctuationSupport ⊆
        physicalActiveSupport X)
    (hH0 : 0 ≤ H0)
    (hweight : ∀ X, 0 ≤ weight X)
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
    BalabanCMP116AppendixFSupportHypotheses (lieDim := lieDim) (Ψ := Ψ)
      HF z Λ
      (physicalGaugeCMP116ActivityTransport_of_cmp116RawSource
        (lieDim := lieDim) (Ψ := Ψ) spectatorPull hroot hsource
        hspectator hfluctuation hH0 hweight activity_stronglyMeasurable
        activeSupport_subset_Omega activeSupport_subset_skeleton
        weight_domination).family := by
  let T :=
    physicalGaugeCMP116ActivityTransport_of_cmp116RawSource
      (lieDim := lieDim) (Ψ := Ψ) spectatorPull hroot hsource
      hspectator hfluctuation hH0 hweight activity_stronglyMeasurable
      activeSupport_subset_Omega activeSupport_subset_skeleton
      weight_domination
  exact physicalGaugeCMP116SupportHypotheses_of_transport T

/-- A raw-source package plus dictionary/support/weight transport hypotheses
produces the CMP116 raw metric-decay predicate for the canonically transported
family. -/
theorem balabanCMP116RawMetricDecay_of_cmp116RawSource
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
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
    {weight : OmegaPolymerType HF z → ℝ}
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (hroot :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight)
    (hsource :
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        D root physicalGaussian physicalActivity weight H0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction)
    (hspectator :
      ∀ X, (physicalActivity X).spectatorSupport ⊆
        physicalActiveSupport X)
    (hfluctuation :
      ∀ X, (physicalActivity X).fluctuationSupport ⊆
        physicalActiveSupport X)
    (hH0 : 0 ≤ H0)
    (hweight : ∀ X, 0 ≤ weight X)
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
    BalabanCMP116RawMetricDecay HF z Λ
      (physicalGaugeCMP116ActivityTransport_of_cmp116RawSource
        (lieDim := lieDim) (Ψ := Ψ) spectatorPull hroot hsource
        hspectator hfluctuation hH0 hweight activity_stronglyMeasurable
        activeSupport_subset_Omega activeSupport_subset_skeleton
        weight_domination).family H0 κ := by
  let T :=
    physicalGaugeCMP116ActivityTransport_of_cmp116RawSource
      (lieDim := lieDim) (Ψ := Ψ) spectatorPull hroot hsource
      hspectator hfluctuation hH0 hweight activity_stronglyMeasurable
      activeSupport_subset_Omega activeSupport_subset_skeleton
      weight_domination
  exact
    balabanCMP116RawMetricDecay_of_physicalGaugeRawActivityDecay T
      (physicalGaugeRawActivityDecay_of_cmp116RawSource hsource) hH0

/-- The same raw-source package gives the exact Appendix-F `hraw` pointwise
shape for the canonically transported CMP116 family. -/
theorem balabanCMP116_hraw_of_cmp116RawSource
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
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
    {weight : OmegaPolymerType HF z → ℝ}
    {D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {physicalGaussian :
      Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : Prop}
    (spectatorPull :
      ∀ b : PhysicalBond dPhys N,
        Ψ (D.siteMap.bondToCube b) → SUNLieCoord Nc)
    (hroot :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight)
    (hsource :
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        D root physicalGaussian physicalActivity weight H0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction)
    (hspectator :
      ∀ X, (physicalActivity X).spectatorSupport ⊆
        physicalActiveSupport X)
    (hfluctuation :
      ∀ X, (physicalActivity X).fluctuationSupport ⊆
        physicalActiveSupport X)
    (hH0 : 0 ≤ H0)
    (hweight : ∀ X, 0 ≤ weight X)
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
    ∀ (ψ : ∀ b : Cube d L, Ψ b)
      (φ : ∀ _ : Cube d L, Fin lieDim → Real) X, X ∈ Λ →
      ‖((physicalGaugeCMP116ActivityTransport_of_cmp116RawSource
        (lieDim := lieDim) (Ψ := Ψ) spectatorPull hroot hsource
        hspectator hfluctuation hH0 hweight activity_stronglyMeasurable
        activeSupport_subset_Omega activeSupport_subset_skeleton
        weight_domination).family.activity X).globalEval ψ φ‖ ≤
        H0 * appendixFHoleExpWeight HF κ X.val := by
  let T :=
    physicalGaugeCMP116ActivityTransport_of_cmp116RawSource
      (lieDim := lieDim) (Ψ := Ψ) spectatorPull hroot hsource
      hspectator hfluctuation hH0 hweight activity_stronglyMeasurable
      activeSupport_subset_Omega activeSupport_subset_skeleton
      weight_domination
  exact balabanCMP116_hraw_of_physicalGaugeCMP116ActivityTransport T hH0

end YangMills.RG

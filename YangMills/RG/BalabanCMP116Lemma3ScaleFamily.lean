/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma3
import YangMills.RG.BalabanCMP116Eq229
import YangMills.RG.BalabanCMP116Lemma3ResidualStages
import YangMills.RG.BalabanCMP116Lemma3RawSourceAdapter

/-!
# CMP116 Lemma 3 scale families

This module packages the isolated CMP116 Lemma 3 activity estimate over a
dependent two-scale family.  It supplies the canonical Lemma-3 weight and
amplitude at each `(t, k)` and turns separated Gaussian/root/Hessian/activity
source facts plus the Lemma 3 estimate into the raw-source records consumed by
`physicalGaugeCMP116RawSourceScaleFamily`.

Honest scope: this file proves no CMP116 analytic constants, no metric
comparison, no Gaussian pushforward, no covariance-root localization, no
Wilson-Hessian identification, no local physical activity construction, and no
rooted H# identity.  It only packages already supplied per-scale facts.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- Canonical CMP116 Lemma 3 source weight at scale `(t, k)`. -/
noncomputable def cmp116Lemma3ScaleWeight
    {ι : ℕ → ℕ → Type*}
    (sourceMetric : ∀ t k, ι t k → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (delta kappaSource : ℕ → ℕ → ℝ)
    (t k : ℕ) : ι t k → ℝ :=
  balabanCMP116Lemma3Weight
    (blockScale t k) (delta t k) (kappaSource t k)
    (sourceMetric t k)

/-- Canonical CMP116 Lemma 3 amplitude at scale `(t, k)`. -/
def cmp116Lemma3ScaleAmplitude
    (C3 epsilon1 : ℕ → ℕ → ℝ)
    (t k : ℕ) : ℝ :=
  C3 t k * epsilon1 t k

/-- The canonical CMP116 Lemma 3 scale-family weight is nonnegative. -/
theorem cmp116Lemma3ScaleWeight_nonneg
    {ι : ℕ → ℕ → Type*}
    (sourceMetric : ∀ t k, ι t k → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (delta kappaSource : ℕ → ℕ → ℝ)
    (t k : ℕ) (X : ι t k) :
    0 ≤
      cmp116Lemma3ScaleWeight
        sourceMetric blockScale delta kappaSource t k X := by
  exact
    balabanCMP116Lemma3Weight_nonneg
      (blockScale t k) (delta t k) (kappaSource t k)
      (sourceMetric t k) X

/-- Dependent two-scale family of CMP116 Lemma 3 activity estimates.

The index type may vary with `(t, k)`, e.g.
`OmegaPolymerType HF (z t k)`.  This is a compatibility package for already
identified admissible domains; it does not prove that every repository polymer
is a native Balaban Lemma 3 domain. -/
def CMP116Lemma3ActivityEstimateScaleFamily
    {ι : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (physicalActivity :
      ∀ t k, ι t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric : ∀ t k, ι t k → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ) : Prop :=
  ∀ t k,
    CMP116Lemma3ActivityEstimate
      (physicalActivity t k)
      (sourceMetric t k)
      (blockScale t k)
      (C3 t k)
      (epsilon1 t k)
      (delta t k)
      (kappaSource t k)

/-- Source-neutral boundary identifying a CMP116 resummation with the physical
activity and giving the pointwise termwise norm estimate consumed by Lemma 3.

This record proves neither field.  It only names the two activity/termwise
obligations that are shared by the CMP116 Lemma-3 source packages. -/
structure CMP116Lemma3ActivityTermwiseScaleBoundary
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc) :
    Prop where

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

/-- Package separated per-scale source facts and a Lemma 3 scale-family
estimate into canonical raw-source records.

This is the scale-family version of
`PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimate`.
-/
def rawSource_of_lemma3ActivityEstimate
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {D :
      ∀ _t _k : ℕ,
        PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ,
        Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (gaussian_pushforward :
      ∀ t k,
        (balabanCMP116Dmu0 (Cube d L) lieDim).map
            ((D t k).gaussianRootMap (root t k)) =
          physicalGaussian t k)
    (root_localization :
      ∀ t k, rootLocalization t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (lemma3_activity_estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric
        blockScale C3 epsilon1 delta kappaSource) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k)
        (cmp116Lemma3ScaleAmplitude C3 epsilon1 t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  fun t k =>
    PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimate
        {
          gaussian_pushforward := gaussian_pushforward t k
          root_localization := root_localization t k
          wilson_hessian_identification :=
            wilson_hessian_identification t k
          local_activity_construction :=
            local_physical_activity_construction t k
        }
        (lemma3_activity_estimate t k)

namespace PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses

/-- Scale-family constructor from an already packaged separated source family.

This form is useful when the Gaussian/root/Hessian/activity source facts have
already been bundled as
`PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses` at every scale.
-/
def of_lemma3ActivityEstimateScaleFamily
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {D :
      ∀ _t _k : ℕ,
        PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ,
        Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (source :
      ∀ t k,
        PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
          (D t k)
          (root t k)
          (physicalGaussian t k)
          (rootLocalization t k)
          (wilsonHessianIdentification t k)
          (localActivityConstruction t k))
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric
        blockScale C3 epsilon1 delta kappaSource) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k)
        (cmp116Lemma3ScaleAmplitude C3 epsilon1 t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_lemma3ActivityEstimate
    (fun t k => (source t k).gaussian_pushforward)
    (fun t k => (source t k).root_localization)
    (fun t k => (source t k).wilson_hessian_identification)
    (fun t k => (source t k).local_activity_construction)
    estimate

end PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses

/-- Build a CMP116 Lemma 3 scale family from per-scale finite resummation data.

The theorem does not prove the termwise estimates or the summed-weight budget;
it only applies the already verified single-scale resummation bridge at every
`(t, k)`. -/
theorem cmp116Lemma3ActivityEstimateScaleFamily_of_resummation
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (hglobal :
      ∀ t k Z ψ φ,
        (physicalActivity t k Z).globalEval ψ φ =
          balabanCMP116H (R t k) Z ψ φ)
    (hterm :
      ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
        ∀ ψ φ,
          ‖(R t k).summand
              Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            (R t k).termWeight
              Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hbudget :
      ∀ t k Z,
        Finset.sum (cmp116HIndexFinset (R t k) Z)
          (fun x =>
            (R t k).termWeight
              Z x.1.1 x.1.2 x.2.1 x.2.2) ≤
          ((hp t k).C3 * (hp t k).epsilon1) *
            balabanCMP116Lemma3Weight
              (hp t k).blockScale
              (hp t k).delta
              (hp t k).kappa
              (sourceMetric t k)
              Z) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) := by
  intro t k
  exact
    cmp116Lemma3ActivityEstimate_of_resummation
      (hp t k) (R t k) (sourceMetric t k)
      (physicalActivity t k)
      (hglobal t k)
      (hterm t k)
      (hbudget t k)

/-- Build a CMP116 Lemma 3 scale family from Eq. (2.29) and explicit residual
post-D estimates at every scale.

This is the scale-family version of
`cmp116Lemma3ActivityEstimate_of_eq229_postD`.  It removes the separate
monolithic `hbudget` premise for this route, but still requires the source
identification, complex termwise estimate, Eq. (2.29), and complete residual
`P/Z0/Z0'` bound pointwise at each `(t, k)`. -/
theorem cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_postD
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (hEq229 :
      ∀ t k,
        CMP116Eq229Summability
          (R t k).DIndex
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k))
    (hglobal :
      ∀ t k Z ψ φ,
        (physicalActivity t k Z).globalEval ψ φ =
          balabanCMP116H (R t k) Z ψ φ)
    (hterm :
      ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
        ∀ ψ φ,
          ‖(R t k).summand
              Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            (R t k).termWeight
              Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hpostD :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        Finset.sum ((R t k).PIndex Z D) (fun P =>
          Finset.sum ((R t k).Z0Index Z D P) (fun Z0 =>
            Finset.sum ((R t k).Z0PrimeIndex Z D P Z0) (fun Z0' =>
              (R t k).termWeight Z D P Z0 Z0'))) ≤
          (((hp t k).C3 * (hp t k).epsilon1) *
            balabanCMP116Lemma3Weight
              (hp t k).blockScale
              (hp t k).delta
              (hp t k).kappa
              (sourceMetric t k)
              Z) *
            Finset.prod (DParts t k Z D)
              (cmp116Eq229Weight
                (alpha6 t k)
                (hp t k).delta
                (hp t k).kappa
                (eq229Metric t k Z))) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) := by
  intro t k
  exact
    cmp116Lemma3ActivityEstimate_of_eq229_postD
      (hp t k) (R t k) (sourceMetric t k)
      (physicalActivity t k)
      (DParts t k)
      (alpha6 t k)
      (eq229Metric t k)
      (hEq229 t k)
      (hglobal t k)
      (hterm t k)
      (hpostD t k)

/-- Build a CMP116 Lemma 3 scale family from Eq. (2.29), source-neutral
residual-stage summability, and pointwise residual factorization at every
scale.

This is the scale-family version of
`cmp116H_termWeightSum_le_of_eq229_of_residualStages` composed with the
finite-resummation activity bridge.  The residual predicates remain explicit;
the theorem does not assign them to CMP116 equation numbers. -/
theorem cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_residualStages
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (z0Weight :
      ∀ t k, σ t k → ιD t k → ιP t k → ιZ0 t k → ℝ)
    (z0PrimeWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ιZ0 t k → ιZ0' t k → ℝ)
    (hEq229 :
      ∀ t k,
        CMP116Eq229Summability
          (R t k).DIndex
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k))
    (hPsum :
      ∀ t k,
        CMP116PResidualSummability
          (R t k).DIndex
          (R t k).PIndex
          (pWeight t k))
    (hZ0sum :
      ∀ t k,
        CMP116Z0ResidualSummability
          (R t k).DIndex
          (R t k).PIndex
          (R t k).Z0Index
          (z0Weight t k))
    (hZ0PrimeSum :
      ∀ t k,
        CMP116Z0PrimeResidualSummability
          (R t k).DIndex
          (R t k).PIndex
          (R t k).Z0Index
          (R t k).Z0PrimeIndex
          (z0PrimeWeight t k))
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k)
    (hglobal :
      ∀ t k Z ψ φ,
        (physicalActivity t k Z).globalEval ψ φ =
          balabanCMP116H (R t k) Z ψ φ)
    (hterm :
      ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
        ∀ ψ φ,
          ‖(R t k).summand
              Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            (R t k).termWeight
              Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hpWeight_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          0 ≤ pWeight t k Z D P)
    (hz0Weight_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0, Z0 ∈ (R t k).Z0Index Z D P →
            0 ≤ z0Weight t k Z D P Z0)
    (postDBase : ∀ t k, σ t k → ιD t k → ℝ)
    (hpostDBase_eq :
      ∀ t k Z D,
        postDBase t k Z D =
          (((hp t k).C3 * (hp t k).epsilon1) *
            balabanCMP116Lemma3Weight
              (hp t k).blockScale
              (hp t k).delta
              (hp t k).kappa
              (sourceMetric t k)
              Z) *
            Finset.prod (DParts t k Z D)
              (cmp116Eq229Weight
                (alpha6 t k)
                (hp t k).delta
                (hp t k).kappa
                (eq229Metric t k Z)))
    (hfactor :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0, Z0 ∈ (R t k).Z0Index Z D P →
            ∀ Z0', Z0' ∈ (R t k).Z0PrimeIndex Z D P Z0 →
              (R t k).termWeight Z D P Z0 Z0' ≤
                ((postDBase t k Z D * pWeight t k Z D P) *
                    z0Weight t k Z D P Z0) *
                  z0PrimeWeight t k Z D P Z0 Z0') :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) := by
  intro t k
  have hpostDBase_nonneg :
      ∀ Z D, D ∈ (R t k).DIndex Z →
        0 ≤ postDBase t k Z D := by
    intro Z D _
    rw [hpostDBase_eq t k Z D]
    exact
      mul_nonneg
        (mul_nonneg (hp t k).amplitude_nonneg
          (balabanCMP116Lemma3Weight_nonneg
            (hp t k).blockScale
            (hp t k).delta
            (hp t k).kappa
            (sourceMetric t k)
            Z))
        (Finset.prod_nonneg
          (fun Y _ =>
            cmp116Eq229Weight_nonneg
              (metric := eq229Metric t k Z) (halpha6 t k) Y))
  have hpostD :
      ∀ Z D, D ∈ (R t k).DIndex Z →
        Finset.sum ((R t k).PIndex Z D) (fun P =>
          Finset.sum ((R t k).Z0Index Z D P) (fun Z0 =>
            Finset.sum ((R t k).Z0PrimeIndex Z D P Z0) (fun Z0' =>
              (R t k).termWeight Z D P Z0 Z0'))) ≤
          (((hp t k).C3 * (hp t k).epsilon1) *
            balabanCMP116Lemma3Weight
              (hp t k).blockScale
              (hp t k).delta
              (hp t k).kappa
              (sourceMetric t k)
              Z) *
            Finset.prod (DParts t k Z D)
              (cmp116Eq229Weight
                (alpha6 t k)
                (hp t k).delta
                (hp t k).kappa
                (eq229Metric t k Z)) := by
    intro Z D hD
    have hpostD_base :
        Finset.sum ((R t k).PIndex Z D) (fun P =>
          Finset.sum ((R t k).Z0Index Z D P) (fun Z0 =>
            Finset.sum ((R t k).Z0PrimeIndex Z D P Z0) (fun Z0' =>
              (R t k).termWeight Z D P Z0 Z0'))) ≤
          postDBase t k Z D :=
      cmp116H_postD_sum_le_of_residualStages
        (R t k)
        (postDBase t k)
        (pWeight t k)
        (z0Weight t k)
        (z0PrimeWeight t k)
        (hPsum t k)
        (hZ0sum t k)
        (hZ0PrimeSum t k)
        hpostDBase_nonneg
        (hpWeight_nonneg t k)
        (hz0Weight_nonneg t k)
        (hfactor t k)
        Z D hD
    simpa [hpostDBase_eq t k Z D] using hpostD_base
  exact
    cmp116Lemma3ActivityEstimate_of_eq229_postD
      (hp t k) (R t k) (sourceMetric t k)
      (physicalActivity t k)
      (DParts t k)
      (alpha6 t k)
      (eq229Metric t k)
      (hEq229 t k)
      (hglobal t k)
      (hterm t k)
      hpostD

/-- Build a CMP116 Lemma 3 scale family from Eq. (2.29), a P-stage budget,
and fixed-`P` residual-stage summability at every scale.

This is the scale-family version of
`cmp116Lemma3ActivityEstimate_of_eq229_pStageResidualStages`.  The P-stage
budget and `Z0/Z0'` residual predicates remain explicit source obligations;
the theorem only applies the verified single-scale finite-summation bridge at
each `(t, k)`. -/
theorem cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageResidualStages
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (z0Weight :
      ∀ t k, σ t k → ιD t k → ιP t k → ιZ0 t k → ℝ)
    (z0PrimeWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ιZ0 t k → ιZ0' t k → ℝ)
    (hEq229 :
      ∀ t k,
        CMP116Eq229Summability
          (R t k).DIndex
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k))
    (hPStage :
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
                (eq229Metric t k Z))))
    (hZ0sum :
      ∀ t k,
        CMP116Z0ResidualSummability
          (R t k).DIndex
          (R t k).PIndex
          (R t k).Z0Index
          (z0Weight t k))
    (hZ0PrimeSum :
      ∀ t k,
        CMP116Z0PrimeResidualSummability
          (R t k).DIndex
          (R t k).PIndex
          (R t k).Z0Index
          (R t k).Z0PrimeIndex
          (z0PrimeWeight t k))
    (hglobal :
      ∀ t k Z ψ φ,
        (physicalActivity t k Z).globalEval ψ φ =
          balabanCMP116H (R t k) Z ψ φ)
    (hterm :
      ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
        ∀ ψ φ,
          ‖(R t k).summand
              Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            (R t k).termWeight
              Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hpWeight_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          0 ≤ pWeight t k Z D P)
    (hz0Weight_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0, Z0 ∈ (R t k).Z0Index Z D P →
            0 ≤ z0Weight t k Z D P Z0)
    (hfactor :
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
                  z0PrimeWeight t k Z D P Z0 Z0') :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) := by
  intro t k
  exact
    cmp116Lemma3ActivityEstimate_of_eq229_pStageResidualStages
      (hp t k) (R t k) (sourceMetric t k)
      (physicalActivity t k)
      (DParts t k)
      (alpha6 t k)
      (eq229Metric t k)
      (pWeight t k)
      (z0Weight t k)
      (z0PrimeWeight t k)
      (hEq229 t k)
      (hPStage t k)
      (hZ0sum t k)
      (hZ0PrimeSum t k)
      (hglobal t k)
      (hterm t k)
      (hpWeight_nonneg t k)
      (hz0Weight_nonneg t k)
      (hfactor t k)

/-- Build a CMP116 Lemma 3 scale family from Eq. (2.29), a P-stage budget,
and a direct combined post-`P` residual budget at every scale.

This route is for source statements that control the last `Z0/Z0'`
resummations together, or in an order not faithfully represented by the
normalized `Z0` then `Z0'` predicates.  It still carries activity
identification, termwise estimates, Eq. (2.29), the P-stage budget, and the
combined post-`P` residual estimate as explicit per-scale obligations. -/
theorem cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (hEq229 :
      ∀ t k,
        CMP116Eq229Summability
          (R t k).DIndex
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k))
    (hPStage :
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
                (eq229Metric t k Z))))
    (hpostP :
      ∀ t k,
        CMP116PostPResidualBound
          (hp t k) (R t k) (sourceMetric t k) (pWeight t k))
    (hglobal :
      ∀ t k Z ψ φ,
        (physicalActivity t k Z).globalEval ψ φ =
          balabanCMP116H (R t k) Z ψ φ)
    (hterm :
      ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
        ∀ ψ φ,
          ‖(R t k).summand
              Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            (R t k).termWeight
              Z x.1.1 x.1.2 x.2.1 x.2.2) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) := by
  intro t k
  exact
    cmp116Lemma3ActivityEstimate_of_eq229_pStagePostPResidualBound
      (hp t k) (R t k) (sourceMetric t k)
      (physicalActivity t k)
      (DParts t k)
      (alpha6 t k)
      (eq229Metric t k)
      (pWeight t k)
      (hEq229 t k)
      (hPStage t k)
      (hpostP t k)
      (hglobal t k)
      (hterm t k)

/-- Scale-family lift of the Eq. (2.29)-weighted P-stage adapter.

It turns normalized per-scale P residual summability into the exact
`CMP116PStageSummability` whose budget is the Eq. (2.29) fixed-`D` product. -/
theorem cmp116PStageSummabilityScaleFamily_of_pResidualSummability_weighted
    {σ ιD ιP ιY : ℕ → ℕ → Type*}
    (DIndex : ∀ t k, σ t k → Finset (ιD t k))
    (PIndex : ∀ t k, σ t k → ιD t k → Finset (ιP t k))
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 delta kappa : ℕ → ℕ → ℝ)
    (metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (hPResidual :
      ∀ t k,
        CMP116PResidualSummability
          (DIndex t k)
          (PIndex t k)
          (pResidualWeight t k))
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k) :
    ∀ t k,
      CMP116PStageSummability
        (DIndex t k)
        (PIndex t k)
        (cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (delta t k)
          (kappa t k)
          (metric t k)
          (pResidualWeight t k))
        (cmp116Eq229Product
          (DParts t k)
          (alpha6 t k)
          (delta t k)
          (kappa t k)
          (metric t k)) := by
  intro t k
  exact
    cmp116PStageSummability_of_pResidualSummability_weighted
      (DIndex t k)
      (PIndex t k)
      (DParts t k)
      (alpha6 t k)
      (delta t k)
      (kappa t k)
      (metric t k)
      (pResidualWeight t k)
      (hPResidual t k)
      (halpha6 t k)

/-- Build a CMP116 Lemma 3 scale family from Eq. (2.29), normalized
P-residual summability weighted by the Eq. (2.29) product, and a direct
combined post-`P` residual budget at every scale.

This removes the explicit `CMP116PStageSummability` premise on this route by
constructing it from the normalized P-residual estimate and `alpha6 >= 0`.
It proves no source estimate or source identification; Eq. (2.29), the
normalized P residual, the combined post-`P` residual estimate, activity
identification, and termwise bound remain explicit obligations. -/
theorem cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_weightedPResidualPostPResidualBound
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (hEq229 :
      ∀ t k,
        CMP116Eq229Summability
          (R t k).DIndex
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k))
    (hPResidual :
      ∀ t k,
        CMP116PResidualSummability
          (R t k).DIndex
          (R t k).PIndex
          (pResidualWeight t k))
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k)
    (hpostP :
      ∀ t k,
        CMP116PostPResidualBound
          (hp t k) (R t k) (sourceMetric t k)
          (cmp116Eq229WeightedPWeight
            (DParts t k)
            (alpha6 t k)
            (hp t k).delta
            (hp t k).kappa
            (eq229Metric t k)
            (pResidualWeight t k)))
    (hglobal :
      ∀ t k Z ψ φ,
        (physicalActivity t k Z).globalEval ψ φ =
          balabanCMP116H (R t k) Z ψ φ)
    (hterm :
      ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
        ∀ ψ φ,
          ‖(R t k).summand
              Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            (R t k).termWeight
              Z x.1.1 x.1.2 x.2.1 x.2.2) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) := by
  have hPStage :
      ∀ t k,
        CMP116PStageSummability
          (R t k).DIndex
          (R t k).PIndex
          (cmp116Eq229WeightedPWeight
            (DParts t k)
            (alpha6 t k)
            (hp t k).delta
            (hp t k).kappa
            (eq229Metric t k)
            (pResidualWeight t k))
          (fun Z D =>
            Finset.prod (DParts t k Z D)
              (cmp116Eq229Weight
                (alpha6 t k)
                (hp t k).delta
                (hp t k).kappa
                (eq229Metric t k Z))) := by
    intro t k
    simpa [cmp116Eq229Product] using
      cmp116PStageSummability_of_pResidualSummability_weighted
        (R t k).DIndex
        (R t k).PIndex
        (DParts t k)
        (alpha6 t k)
        (hp t k).delta
        (hp t k).kappa
        (eq229Metric t k)
        (pResidualWeight t k)
        (hPResidual t k)
        (halpha6 t k)
  exact
    cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      (fun t k =>
        cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k))
      hEq229
      hPStage
      hpostP
      hglobal
      hterm

/-- Pointwise scale-family majorization of the source-shaped post-`P`
amplitude/weight by the canonical CMP116 Lemma-3 base factor.

This predicate proves no source majorization.  It names the exact source-side
obligation consumed by the post-`P` residual adapter at every scale. -/
def CMP116PostPResidualSourceMajorizationScaleFamily
    {σ : ℕ → ℕ → Type*}
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ) : Prop :=
  ∀ t k Z,
    postPAmplitude t k * postPSourceWeight t k Z ≤
      (C3 t k * epsilon1 t k) *
        balabanCMP116Lemma3Weight
          (blockScale t k)
          (delta t k)
          (kappaSource t k)
          (sourceMetric t k)
          Z

/-- A scale family of source-shaped combined post-`P` estimates feeds the
canonical post-`P` residual consumer once the source amplitude/weight is
majorized pointwise and the `P` weight is nonnegative.

This is only the scale-family lift of
`cmp116PostPResidualBound_of_sourceBound`. -/
theorem cmp116PostPResidualBoundScaleFamily_of_sourceBound
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {Ψ Φ : Type*}
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          Ψ Φ)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (pWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (hsource :
      ∀ t k,
        CMP116PostPResidualSourceBound
          (R t k)
          (postPSourceWeight t k)
          (postPAmplitude t k)
          (pWeight t k))
    (hmajorization :
      CMP116PostPResidualSourceMajorizationScaleFamily
        sourceMetric
        (fun t k => (hp t k).blockScale)
        (fun t k => (hp t k).C3)
        (fun t k => (hp t k).epsilon1)
        (fun t k => (hp t k).delta)
        (fun t k => (hp t k).kappa)
        postPSourceWeight
        postPAmplitude)
    (hpWeight_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          0 ≤ pWeight t k Z D P) :
    ∀ t k,
      CMP116PostPResidualBound
        (hp t k)
        (R t k)
        (sourceMetric t k)
        (pWeight t k) := by
  intro t k
  exact
    cmp116PostPResidualBound_of_sourceBound
      (hp t k)
      (R t k)
      (sourceMetric t k)
      (postPSourceWeight t k)
      (postPAmplitude t k)
      (pWeight t k)
      (hsource t k)
      (hmajorization t k)
      (hpWeight_nonneg t k)

/-- Eq. (2.29) boundary for the weighted CMP116 post-`P` source package.

This names the Eq. (2.29) summability field and the nonnegativity of `alpha6`
needed to weight normalized P-residual sums. -/
structure CMP116Lemma3Eq229ScaleBoundary
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ) :
    Prop where

  eq229_summability :
    ∀ t k,
      CMP116Eq229Summability
        (R t k).DIndex
        (DParts t k)
        (alpha6 t k)
        (hp t k).delta
        (hp t k).kappa
        (eq229Metric t k)

  alpha6_nonneg :
    ∀ t k, 0 ≤ alpha6 t k

/-- P-stage source boundary for the weighted CMP116 post-`P` source package.

This records the source-shaped P-stage estimate, its scalar smallness
restriction, and pointwise nonnegativity of the normalized P-residual weight. -/
structure CMP116Lemma3PStageSourceScaleBoundary
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ) :
    Prop where

  p_stage_source_bound :
    ∀ t k,
      CMP116PStageSourceBound
        (R t k).DIndex
        (R t k).PIndex
        (pResidualWeight t k)
        (pStageBlockScale t k)
        (pEntropyConstant t k)
        (epsilon2 t k)
        (pStageKappa t k)

  p_stage_smallness :
    ∀ t k,
      2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
          pEntropyConstant t k * epsilon2 t k *
            Real.exp (5 * pStageKappa t k) ≤ 1

  p_residual_weight_nonneg :
    ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P

/-- Scale-family constructor for the P-stage source boundary from the
pointwise/geometric P-stage split.

This is still source-neutral: it packages the pointwise P-term estimate, the
finite geometric P-family summation consequence, the scalar smallness
restriction, and nonnegativity into the existing P-stage boundary record.  It
does not construct the source `P` families or prove any CMP116 scalar hierarchy.
-/
def CMP116Lemma3PStageSourceScaleBoundary.of_pointwise_geometric
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hgeometric :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        Finset.sum ((R t k).PIndex Z D)
            (fun P => pGeometryWeight t k Z D P) ≤
          pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k =>
    cmp116PStageSourceBound_of_pointwise_geometric
      (R t k).DIndex
      (R t k).PIndex
      (pResidualWeight t k)
      (pGeometryWeight t k)
      (pStageBlockScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (hepsilon2_nonneg t k)
      (hpointwise t k)
      (hgeometric t k)

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- Scale-family constructor for the P-stage source boundary from the explicit
CMP116 Eq. (2.31) bond-subset entropy boundary.

This is the theorem-fed variant of `of_pointwise_geometric`: it derives the
finite geometric P-family summation from `CMP116Eq231PBondBoundary` at each
scale, and derives the transcendental rate condition from the source-shaped
rate formula and an algebraic small-coupling inequality.  The source
construction of the `P` families, pointwise residual majorization, remaining
scalar smallness, and constant hierarchy remain explicit inputs. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise
    {σ ιD ιP ιZ0 ιZ0' β : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
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
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
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
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k =>
    cmp116PStageSourceBound_of_eq231_pointwise
      (R t k).DIndex
      (R t k).PIndex
      (pResidualWeight t k)
      (pGeometryWeight t k)
      (pStageBlockScale t k)
      (eq231LocalizationScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (gamma2 t k)
      (eq231Epsilon1 t k)
      (gk t k)
      (B t k)
      (hepsilon2_nonneg t k)
      (hpointwise t k)
      (hsourceBracket t k)
      (hgeometry t k)
      (htarget t k)

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- Scale-family constructor for the source-backed CMP116 Eq. (2.31) route
where the `P` index is the finite four-dimensional bond set itself.

Compared with `of_eq231_pointwise`, this source-facing route no longer asks
callers to supply an abstract `CMP116Eq231PBondBoundary`; it constructs that
boundary from `gapCubes`, the concrete four-direction carrier, and the one
remaining source-specific carrier-containment fact. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourceBondSets
    {σ ιD ιZ0 ιZ0' Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ)
    (gapCubes :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k))
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPcarrier :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          P ⊆
            gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)))
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
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k =>
    cmp116PStageSourceBound_of_eq231_sourceBondSets
      (R t k).DIndex
      (R t k).PIndex
      (pResidualWeight t k)
      (pGeometryWeight t k)
      (gapCubes t k)
      (pStageBlockScale t k)
      (eq231LocalizationScale t k)
      (hlocalizationScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (gamma2 t k)
      (eq231Epsilon1 t k)
      (gk t k)
      (hepsilon2_nonneg t k)
      (hPcarrier t k)
      (hpointwise t k)
      (hsourceBracket t k)
      (hgeometry t k)
      (htarget t k)

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- Scale-family constructor for the source-backed CMP116 Eq. (2.31) route
whose source `P` family is already presented as the filtered powerset of the
four-direction gap carrier.

Compared with `of_eq231_sourceBondSets`, this route replaces the live
source-specific carrier-containment hypothesis by the explicit statement that
`R.PIndex` is the filtered source family `cmp116Eq231SourcePIndex`.  Containment
then follows from powerset membership. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets
    {σ ιD ιZ0 ιZ0' Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ)
    (gapCubes :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k))
    (admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool)
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndex :
      ∀ t k Z D,
        (R t k).PIndex Z D =
          cmp116Eq231SourcePIndex
            (gapCubes t k) (admissible t k) Z D)
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
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k => by
    have hPIndex_fun :
        (R t k).PIndex =
          cmp116Eq231SourcePIndex
            (gapCubes t k) (admissible t k) := by
      funext Z D
      exact hPIndex t k Z D
    have hsource :
        CMP116PStageSourceBound
          (R t k).DIndex
          (cmp116Eq231SourcePIndex
            (gapCubes t k) (admissible t k))
          (pResidualWeight t k)
          (pStageBlockScale t k)
          (pEntropyConstant t k)
          (epsilon2 t k)
          (pStageKappa t k) :=
      cmp116PStageSourceBound_of_eq231_filteredBondSets
        (R t k).DIndex
        (gapCubes t k)
        (admissible t k)
        (pResidualWeight t k)
        (pGeometryWeight t k)
        (pStageBlockScale t k)
        (eq231LocalizationScale t k)
        (hlocalizationScale t k)
        (pEntropyConstant t k)
        (epsilon2 t k)
        (pStageKappa t k)
        (gamma2 t k)
        (eq231Epsilon1 t k)
        (gk t k)
        (hepsilon2_nonneg t k)
        (fun Z D hD P hP =>
          hpointwise t k Z D hD P
            (by simpa [hPIndex t k Z D] using hP))
        (hsourceBracket t k)
        (fun Z D hD P hP =>
          hgeometry t k Z D hD P
            (by simpa [hPIndex t k Z D] using hP))
        (htarget t k)
    simpa [hPIndex_fun] using hsource

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- Scale-family constructor for the source-backed CMP116 Eq. (2.31) route
from the exact pointwise source-membership theorem for `R.PIndex`.

Compared with `of_eq231_filteredBondSets`, this route does not require callers
to first prove the extensional equality
`R.PIndex = cmp116Eq231SourcePIndex gapCubes admissible`.  The pointwise iff
is precisely the source theorem still missing from the citation audit. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourcePIndexMemIff
    {σ ιD ιZ0 ιZ0' Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ)
    (gapCubes :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k))
    (admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool)
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndexMem :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          P ⊆ gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible t k Z D P = true)
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
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k =>
    cmp116PStageSourceBound_of_eq231_sourcePIndexMemIff
      (R t k).DIndex
      (R t k).PIndex
      (gapCubes t k)
      (admissible t k)
      (pResidualWeight t k)
      (pGeometryWeight t k)
      (pStageBlockScale t k)
      (eq231LocalizationScale t k)
      (hlocalizationScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (gamma2 t k)
      (eq231Epsilon1 t k)
      (gk t k)
      (hepsilon2_nonneg t k)
      (hPIndexMem t k)
      (hpointwise t k)
      (hsourceBracket t k)
      (hgeometry t k)
      (htarget t k)

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- The P-stage source boundary exposes normalized P-residual summability after
applying its explicit scalar smallness field.

This lets downstream finite-sum consumers use the P-stage boundary without
requiring the larger weighted post-`P` source package. -/
def CMP116Lemma3PStageSourceScaleBoundary.p_residual_summability
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    (source :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa) :
    ∀ t k,
      CMP116PResidualSummability
        (R t k).DIndex
        (R t k).PIndex
        (pResidualWeight t k) := by
  intro t k
  exact
    cmp116PResidualSummability_of_pStageSourceBound
      (R t k).DIndex
      (R t k).PIndex
      (pResidualWeight t k)
      (pStageBlockScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (source.p_stage_source_bound t k)
      (source.p_stage_smallness t k)

/-- Weighted post-`P` source boundary for the CMP116 Lemma-3 scale route.

This names the combined post-`P` source estimate for the Eq. (2.29)-weighted
P weights and the majorization by the canonical Lemma-3 base factor. -/
structure CMP116Lemma3WeightedPostPSourceScaleBoundary
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ) :
    Prop where

  postP_source_bound :
    ∀ t k,
      CMP116PostPResidualSourceBound
        (R t k)
        (postPSourceWeight t k)
        (postPAmplitude t k)
        (cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k))

  postP_majorization :
    CMP116PostPResidualSourceMajorizationScaleFamily
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      postPSourceWeight
      postPAmplitude

/-- The weighted post-`P` source boundary exposes the canonical post-`P`
residual bound once the Eq. (2.29) and P-stage boundaries supply weighted
P-weight nonnegativity.

This avoids assembling the larger weighted post-`P` source package when a
downstream proof only needs the post-`P` residual consumer. -/
def CMP116Lemma3WeightedPostPSourceScaleBoundary.postP_residual_bound
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude) :
    ∀ t k,
      CMP116PostPResidualBound
        (hp t k)
        (R t k)
        (sourceMetric t k)
        (cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k)) := by
  have hweighted_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          0 ≤
            cmp116Eq229WeightedPWeight
              (DParts t k)
              (alpha6 t k)
              (hp t k).delta
              (hp t k).kappa
              (eq229Metric t k)
              (pResidualWeight t k)
              Z D P := by
    intro t k Z D _ P _
    exact
      cmp116Eq229WeightedPWeight_nonneg
        (DParts := DParts t k)
        (metric := eq229Metric t k)
        (pResidualWeight := pResidualWeight t k)
        (eq229.alpha6_nonneg t k)
        (pStage.p_residual_weight_nonneg t k)
        Z D P
  exact
    cmp116PostPResidualBoundScaleFamily_of_sourceBound
      hp R sourceMetric postPSourceWeight postPAmplitude
      (fun t k =>
        cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k))
      postP.postP_source_bound
      postP.postP_majorization
      hweighted_nonneg

/-- Source-boundary package for the CMP116 Lemma-3 scale route that keeps the
final `Z0/Z0'` resummation as one combined post-`P` residual estimate.

This record deliberately does not introduce a standalone `Z0'` source scalar
or a fixed-`Z0` source summability theorem.  It only packages the exact
assumptions consumed by
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound`. -/
structure CMP116Lemma3PostPScaleSourceAssumptions
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ) :
    Prop where

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

  postP_residual_bound :
    ∀ t k,
      CMP116PostPResidualBound
        (hp t k) (R t k) (sourceMetric t k) (pWeight t k)

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

namespace CMP116Lemma3PostPScaleSourceAssumptions

/-- The post-`P` scale-source package exposes the shared
activity-identification/termwise-estimate boundary. -/
def activityTermwiseBoundary
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    (source :
      CMP116Lemma3PostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pWeight) :
    CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity where
  activity_identification := source.activity_identification
  termwise_estimate := source.termwise_estimate

/-- Projection from the post-`P` scale-source package to the existing CMP116
Lemma-3 activity scale-family estimate. -/
def lemma3_activity_estimate
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    (source :
      CMP116Lemma3PostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pWeight) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound
    hp R sourceMetric physicalActivity DParts alpha6 eq229Metric pWeight
    source.eq229_summability
    source.p_stage_summability
    source.postP_residual_bound
    source.activity_identification
    source.termwise_estimate

end CMP116Lemma3PostPScaleSourceAssumptions

/-- Source-boundary package for the Eq. (2.29)-weighted P-residual CMP116
Lemma-3 scale route.

This is the source-shaped companion to
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_weightedPResidualPostPResidualBound`.
It keeps the P-stage source bound, its scalar smallness restriction, pointwise
P-weight nonnegativity, the combined post-`P` source estimate, and the
post-`P` majorization as separate fields.  It proves no Eq. (2.29), no source
construction of the P family, and no combined post-`P` source estimate. -/
structure CMP116Lemma3WeightedPostPScaleSourceAssumptions
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ) :
    Prop where

  eq229_summability :
    ∀ t k,
      CMP116Eq229Summability
        (R t k).DIndex
        (DParts t k)
        (alpha6 t k)
        (hp t k).delta
        (hp t k).kappa
        (eq229Metric t k)

  p_stage_source_bound :
    ∀ t k,
      CMP116PStageSourceBound
        (R t k).DIndex
        (R t k).PIndex
        (pResidualWeight t k)
        (pStageBlockScale t k)
        (pEntropyConstant t k)
        (epsilon2 t k)
        (pStageKappa t k)

  p_stage_smallness :
    ∀ t k,
      2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
          pEntropyConstant t k * epsilon2 t k *
            Real.exp (5 * pStageKappa t k) ≤ 1

  alpha6_nonneg :
    ∀ t k, 0 ≤ alpha6 t k

  p_residual_weight_nonneg :
    ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P

  postP_source_bound :
    ∀ t k,
      CMP116PostPResidualSourceBound
        (R t k)
        (postPSourceWeight t k)
        (postPAmplitude t k)
        (cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k))

  postP_majorization :
    CMP116PostPResidualSourceMajorizationScaleFamily
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      postPSourceWeight
      postPAmplitude

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

namespace CMP116Lemma3WeightedPostPScaleSourceAssumptions

/-- The weighted post-`P` source package exposes the shared
activity-identification/termwise-estimate boundary. -/
def activityTermwiseBoundary
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (source :
      CMP116Lemma3WeightedPostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude) :
    CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity where
  activity_identification := source.activity_identification
  termwise_estimate := source.termwise_estimate

/-- Constructor for the weighted post-`P` source package from named
source-boundary subpackages.

This is only record assembly: Eq. (2.29), the P-stage source/smallness data,
the weighted post-`P` source/majorization data, and the activity-termwise
boundary are all supplied explicitly. -/
def of_boundaries
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude where
  eq229_summability := eq229.eq229_summability
  p_stage_source_bound := pStage.p_stage_source_bound
  p_stage_smallness := pStage.p_stage_smallness
  alpha6_nonneg := eq229.alpha6_nonneg
  p_residual_weight_nonneg := pStage.p_residual_weight_nonneg
  postP_source_bound := postP.postP_source_bound
  postP_majorization := postP.postP_majorization
  activity_identification := activity.activity_identification
  termwise_estimate := activity.termwise_estimate

/-- Constructor for the weighted post-`P` source package from Eq. (2.29), an
explicit Eq. (2.31) P-bond boundary, the weighted post-`P` boundary, and the
activity/termwise boundary.

This packages the same source-neutral composition as
`lemma3_activity_estimate_of_eq231_boundaries`, but keeps the resulting
`CMP116Lemma3WeightedPostPScaleSourceAssumptions` record available for
downstream projections.  It proves no source construction of the P family,
pointwise P-residual estimate, scalar hierarchy, post-`P` estimate, activity
identification, or termwise bound. -/
def of_eq231_boundaries
    {σ ιD ιP ιZ0 ιZ0' ιY β : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
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
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise
      R pResidualWeight pGeometryWeight
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      B hepsilon2_nonneg hpointwise hsourceBracket hgeometry htarget
      hsmall hpResidual_nonneg)
    postP
    activity

/-- Constructor for the weighted post-`P` source package from Eq. (2.29), the
filtered-powerset Eq. (2.31) P-family route, the weighted post-`P` boundary,
and the activity/termwise boundary.

Compared with `of_eq231_boundaries`, this route removes the abstract
`CMP116Eq231PBondBoundary` input and the per-`P` carrier-containment premise.
It still requires the source dictionary stating that `R.PIndex` is the filtered
source family `cmp116Eq231SourcePIndex gapCubes admissible`. -/
def of_eq231_filteredBondSets
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndex :
      ∀ t k Z D,
        (R t k).PIndex Z D =
          cmp116Eq231SourcePIndex
            (gapCubes t k) (admissible t k) Z D)
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
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
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
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets
      R pResidualWeight pGeometryWeight gapCubes admissible
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      hlocalizationScale hepsilon2_nonneg hPIndex hpointwise
      hsourceBracket hgeometry htarget hsmall hpResidual_nonneg)
    postP
    activity

/-- Constructor for the weighted post-`P` source package from Eq. (2.29), the
Eq. (2.31) source-membership theorem for `R.PIndex`, the weighted post-`P`
boundary, and the activity/termwise boundary.

This is the theorem-facing counterpart of `of_eq231_filteredBondSets`: the
future source theorem is the pointwise `PIndex` membership iff, not a separate
extensional equality proof generated outside the package. -/
def of_eq231_sourcePIndexMemIff
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndexMem :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          P ⊆ gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible t k Z D P = true)
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
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
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
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourcePIndexMemIff
      R pResidualWeight pGeometryWeight gapCubes admissible
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      hlocalizationScale hepsilon2_nonneg hPIndexMem hpointwise
      hsourceBracket hgeometry htarget hsmall hpResidual_nonneg)
    postP
    activity

/-- The weighted post-`P` source package exposes normalized P-residual
summability only after applying the explicit source scalar smallness field. -/
def p_residual_summability
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (source :
      CMP116Lemma3WeightedPostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude) :
    ∀ t k,
      CMP116PResidualSummability
        (R t k).DIndex
        (R t k).PIndex
        (pResidualWeight t k) := by
  intro t k
  exact
    cmp116PResidualSummability_of_pStageSourceBound
      (R t k).DIndex
      (R t k).PIndex
      (pResidualWeight t k)
      (pStageBlockScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (source.p_stage_source_bound t k)
      (source.p_stage_smallness t k)

/-- The source-shaped combined post-`P` bound in the weighted package feeds the
canonical post-`P` residual bound for the Eq. (2.29)-weighted P weights. -/
def postP_residual_bound
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (source :
      CMP116Lemma3WeightedPostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude) :
    ∀ t k,
      CMP116PostPResidualBound
        (hp t k)
        (R t k)
        (sourceMetric t k)
        (cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k)) := by
  have hweighted_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          0 ≤
            cmp116Eq229WeightedPWeight
              (DParts t k)
              (alpha6 t k)
              (hp t k).delta
              (hp t k).kappa
              (eq229Metric t k)
              (pResidualWeight t k)
              Z D P := by
    intro t k Z D _ P _
    exact
      cmp116Eq229WeightedPWeight_nonneg
        (DParts := DParts t k)
        (metric := eq229Metric t k)
        (pResidualWeight := pResidualWeight t k)
        (source.alpha6_nonneg t k)
        (source.p_residual_weight_nonneg t k)
        Z D P
  exact
    cmp116PostPResidualBoundScaleFamily_of_sourceBound
      hp R sourceMetric postPSourceWeight postPAmplitude
      (fun t k =>
        cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k))
      source.postP_source_bound
      source.postP_majorization
      hweighted_nonneg

/-- Projection from the weighted post-`P` scale-source package to the CMP116
Lemma-3 activity scale-family estimate. -/
def lemma3_activity_estimate
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (source :
      CMP116Lemma3WeightedPostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_weightedPResidualPostPResidualBound
    hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
    pResidualWeight
    source.eq229_summability
    source.p_residual_summability
    source.alpha6_nonneg
    source.postP_residual_bound
    source.activity_identification
    source.termwise_estimate

/-- Project a weighted post-`P` scale-source package to the raw-source records
consumed by the physical CMP116/Appendix-F path.

The package supplies the Lemma-3 activity estimate; the separated
Gaussian/root/Hessian/activity facts remain explicit. -/
def rawSource
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {D :
      ∀ _t _k : ℕ,
        PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ,
        Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {hp : ∀ _ _, CMP116Lemma3Parameters}
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
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (gaussian_pushforward :
      ∀ t k,
        (balabanCMP116Dmu0 (Cube d L) lieDim).map
            ((D t k).gaussianRootMap (root t k)) =
          physicalGaussian t k)
    (root_localization :
      ∀ t k, rootLocalization t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (source :
      CMP116Lemma3WeightedPostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude) :
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
    gaussian_pushforward
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    source.lemma3_activity_estimate

/-- Direct CMP116 Lemma-3 scale-family consumer from the named weighted
post-`P` boundary subpackages.

This only composes `of_boundaries` with `lemma3_activity_estimate`; all source,
smallness, majorization, activity-identification, and termwise-estimate
obligations remain explicit inputs. -/
def lemma3_activity_estimate_of_boundaries
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  lemma3_activity_estimate
    (of_boundaries eq229 pStage postP activity)

/-- Direct CMP116 Lemma-3 scale-family consumer from Eq. (2.29), the explicit
Eq. (2.31) P-bond entropy boundary, the weighted post-`P` boundary, and the
activity/termwise boundary.

This only composes `CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise`
with `lemma3_activity_estimate_of_boundaries`.  It removes the need for callers
to preassemble a P-stage source boundary when Eq. (2.31) bond data are already
available; all source construction, pointwise, smallness, post-`P`,
majorization, activity-identification, and termwise obligations remain explicit
inputs. -/
def lemma3_activity_estimate_of_eq231_boundaries
    {σ ιD ιP ιZ0 ιZ0' ιY β : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
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
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  lemma3_activity_estimate_of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise
      R pResidualWeight pGeometryWeight
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      B hepsilon2_nonneg hpointwise hsourceBracket hgeometry htarget
      hsmall hpResidual_nonneg)
    postP
    activity

/-- Direct CMP116 Lemma-3 scale-family consumer from Eq. (2.29), the
filtered-powerset Eq. (2.31) P-family route, the weighted post-`P` boundary,
and the activity/termwise boundary.

This is the filtered-P counterpart of
`lemma3_activity_estimate_of_eq231_boundaries`: it removes the abstract
Eq. (2.31) bond-boundary input once `R.PIndex` is explicitly identified with
`cmp116Eq231SourcePIndex gapCubes admissible`. -/
def lemma3_activity_estimate_of_eq231_filteredBondSets
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndex :
      ∀ t k Z D,
        (R t k).PIndex Z D =
          cmp116Eq231SourcePIndex
            (gapCubes t k) (admissible t k) Z D)
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
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
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
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  lemma3_activity_estimate
    (of_eq231_filteredBondSets
      eq229 hlocalizationScale hepsilon2_nonneg hPIndex hpointwise
      hsourceBracket hgeometry htarget hsmall hpResidual_nonneg
      postP activity)

/-- Direct CMP116 Lemma-3 scale-family consumer from Eq. (2.29), the
Eq. (2.31) source-membership theorem for `R.PIndex`, the weighted post-`P`
boundary, and the activity/termwise boundary.

This avoids exposing an auxiliary filtered-family equality to final
Lemma-3 consumers.  The remaining `hPIndexMem` premise is exactly the
source-to-Lean dictionary still requested from the CMP116/CMP109 source
audit. -/
def lemma3_activity_estimate_of_eq231_sourcePIndexMemIff
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndexMem :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          P ⊆ gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible t k Z D P = true)
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
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
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
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  lemma3_activity_estimate
    (of_eq231_sourcePIndexMemIff
      eq229 hlocalizationScale hepsilon2_nonneg hPIndexMem hpointwise
      hsourceBracket hgeometry htarget hsmall hpResidual_nonneg
      postP activity)

end CMP116Lemma3WeightedPostPScaleSourceAssumptions

/-- Build raw-source records directly from the named weighted post-`P` boundary
subpackages and the separated Gaussian/root/Hessian/activity source facts.

This is a thin composition of
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries`
with `rawSource_of_lemma3ActivityEstimate`; it proves none of the analytic or
physical source obligations supplied as inputs. -/
def rawSource_of_weightedPostPBoundaries
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {D :
      ∀ _t _k : ℕ,
        PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ,
        Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → Finset (ιY t k)}
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
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (gaussian_pushforward :
      ∀ t k,
        (balabanCMP116Dmu0 (Cube d L) lieDim).map
            ((D t k).gaussianRootMap (root t k)) =
          physicalGaussian t k)
    (root_localization :
      ∀ t k, rootLocalization t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
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
    gaussian_pushforward
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    (CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries
      eq229 pStage postP activity)

/-- Build raw-source records from Eq. (2.29), explicit Eq. (2.31) P-bond data,
the weighted post-`P` boundary, the activity/termwise boundary, and the
separated Gaussian/root/Hessian/activity source facts.

This is the Eq. (2.31)-specialized version of
`rawSource_of_weightedPostPBoundaries`.  It avoids requiring callers to
preassemble a `CMP116Lemma3PStageSourceScaleBoundary`; all Eq. (2.31), scalar,
post-`P`, activity, termwise, and physical source obligations are still
supplied explicitly. -/
def rawSource_of_eq231_weightedPostPBoundaries
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιP ιZ0 ιZ0' ιY β : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {D :
      ∀ _t _k : ℕ,
        PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim}
    {root :
      ∀ _t _k : ℕ,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc}
    {physicalGaussian :
      ∀ _t _k : ℕ,
        Measure (PhysicalGaugeOneCochain dPhys N Nc)}
    {physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (gaussian_pushforward :
      ∀ t k,
        (balabanCMP116Dmu0 (Cube d L) lieDim).map
            ((D t k).gaussianRootMap (root t k)) =
          physicalGaussian t k)
    (root_localization :
      ∀ t k, rootLocalization t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
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
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
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
    gaussian_pushforward
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    (CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_boundaries
      eq229 B hepsilon2_nonneg hpointwise hsourceBracket
      hgeometry htarget hsmall
      hpResidual_nonneg postP activity)

/-- Build a CMP116 Lemma 3 scale family from Eq. (2.29), a source-shaped
P-stage bound plus scalar smallness, and fixed-`P` residual-stage summability
at every scale.

This is the scale-family version of
`cmp116Lemma3ActivityEstimate_of_eq229_pStageSourceBound_residualStages`.
Only the P-stage source-neutral residual hypothesis is replaced by the
source-shaped P estimate; Eq. (2.29), `Z0/Z0'` residual stages, activity
identification, termwise estimates, nonnegativity, and factorization remain
explicit per-scale obligations. -/
theorem cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageSourceBound_residualStages
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (z0Weight :
      ∀ t k, σ t k → ιD t k → ιP t k → ιZ0 t k → ℝ)
    (z0PrimeWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ιZ0 t k → ιZ0' t k → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (hEq229 :
      ∀ t k,
        CMP116Eq229Summability
          (R t k).DIndex
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k))
    (hPsource :
      ∀ t k,
        CMP116PStageSourceBound
          (R t k).DIndex
          (R t k).PIndex
          (pWeight t k)
          (pStageBlockScale t k)
          (pEntropyConstant t k)
          (epsilon2 t k)
          (pStageKappa t k))
    (hPsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hZ0sum :
      ∀ t k,
        CMP116Z0ResidualSummability
          (R t k).DIndex
          (R t k).PIndex
          (R t k).Z0Index
          (z0Weight t k))
    (hZ0PrimeSum :
      ∀ t k,
        CMP116Z0PrimeResidualSummability
          (R t k).DIndex
          (R t k).PIndex
          (R t k).Z0Index
          (R t k).Z0PrimeIndex
          (z0PrimeWeight t k))
    (hglobal :
      ∀ t k Z ψ φ,
        (physicalActivity t k Z).globalEval ψ φ =
          balabanCMP116H (R t k) Z ψ φ)
    (hterm :
      ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
        ∀ ψ φ,
          ‖(R t k).summand
              Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            (R t k).termWeight
              Z x.1.1 x.1.2 x.2.1 x.2.2)
    (halpha6 :
      ∀ t k, 0 ≤ alpha6 t k)
    (hpWeight_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          0 ≤ pWeight t k Z D P)
    (hz0Weight_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0, Z0 ∈ (R t k).Z0Index Z D P →
            0 ≤ z0Weight t k Z D P Z0)
    (hfactor :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0, Z0 ∈ (R t k).Z0Index Z D P →
            ∀ Z0', Z0' ∈ (R t k).Z0PrimeIndex Z D P Z0 →
              (R t k).termWeight Z D P Z0 Z0' ≤
                ((((((hp t k).C3 * (hp t k).epsilon1) *
                    balabanCMP116Lemma3Weight
                      (hp t k).blockScale
                      (hp t k).delta
                      (hp t k).kappa
                      (sourceMetric t k)
                      Z) *
                    Finset.prod (DParts t k Z D)
                      (cmp116Eq229Weight
                        (alpha6 t k)
                        (hp t k).delta
                        (hp t k).kappa
                        (eq229Metric t k Z))) *
                    (pWeight t k Z D P)) *
                  (z0Weight t k Z D P Z0)) *
                  (z0PrimeWeight t k Z D P Z0 Z0')) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) := by
  intro t k
  exact
    cmp116Lemma3ActivityEstimate_of_eq229_pStageSourceBound_residualStages
      (hp t k) (R t k) (sourceMetric t k)
      (physicalActivity t k)
      (DParts t k)
      (alpha6 t k)
      (eq229Metric t k)
      (pWeight t k)
      (z0Weight t k)
      (z0PrimeWeight t k)
      (pStageBlockScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (hEq229 t k)
      (hPsource t k)
      (hPsmall t k)
      (hZ0sum t k)
      (hZ0PrimeSum t k)
      (hglobal t k)
      (hterm t k)
      (halpha6 t k)
      (hpWeight_nonneg t k)
      (hz0Weight_nonneg t k)
      (hfactor t k)

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma3
import YangMills.RG.BalabanCMP116Eq229
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

end YangMills.RG

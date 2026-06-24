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

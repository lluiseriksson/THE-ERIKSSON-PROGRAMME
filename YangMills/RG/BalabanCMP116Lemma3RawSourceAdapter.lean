/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma3Estimate
import YangMills.RG.PhysicalGaugeCMP116ActivityConstruction

/-!
# CMP116 Lemma 3 raw-source adapters

This module is the downstream compatibility layer from the isolated CMP116
Lemma 3 activity estimate into the existing physical/CMP116 raw-source
packages.

Honest scope: the adapters here package already supplied source facts.  They
do not prove the Lemma 3 resummation, construct the local activity, identify a
Wilson Hessian, prove covariance-root localization, or prove a Gaussian
pushforward.
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
  unfold balabanCMP116Lemma3Weight appendixFHoleExpWeight
  exact Real.exp_le_exp.mpr
    (neg_le_neg (metric_comparison X hX))

namespace PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses

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
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {C3 epsilon1 delta kappaSource : ℝ}
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
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource) :
    PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
      D root physicalGaussian physicalActivity
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (C3 * epsilon1)
      rootLocalization
      wilsonHessianIdentification
      localActivityConstruction where
  gaussian_pushforward := source.gaussian_pushforward
  root_localization := source.root_localization
  wilson_hessian_identification := source.wilson_hessian_identification
  local_activity_construction := source.local_activity_construction
  raw_pointwise_decay := balabanLemma3_rawActivityDecay estimate

end PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses

end YangMills.RG

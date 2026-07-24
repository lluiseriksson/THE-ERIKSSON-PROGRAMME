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

/-- Generate the CMP116 Lemma-3 exponent comparison from a source-metric
domination and a scale-independent rate margin.

This is the scalar part of the Lemma-3/App-F weight bridge: the geometric
content is the domination `d_M(X)+1 <= sourceMetric X`; the source-rate content
is the single margin `kappa <= balabanCMP116Lemma3DecayRate ...`. -/
theorem metric_comparison_of_sourceMetric_domination_and_rate_margin
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    (Λ : Finset (OmegaPolymerType HF z))
    {sourceMetric : OmegaPolymerType HF z → ℕ}
    {blockScale : ℕ}
    {delta kappaSource kappa : ℝ}
    (sourceMetric_domination :
      ∀ X, X ∈ Λ →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric X : ℝ))
    (rate_margin :
      kappa ≤
        balabanCMP116Lemma3DecayRate blockScale delta kappaSource)
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ X, X ∈ Λ →
      kappa *
          (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
        balabanCMP116Lemma3DecayRate
            blockScale delta kappaSource *
          (sourceMetric X : ℝ) := by
  intro X hX
  calc
    kappa * (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ))
        ≤ kappa * (sourceMetric X : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (sourceMetric_domination X hX) kappa_nonneg
    _ ≤
        balabanCMP116Lemma3DecayRate
            blockScale delta kappaSource *
          (sourceMetric X : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            rate_margin (Nat.cast_nonneg _)

/-- Dominate the CMP116 Lemma-3 source weight by the Appendix-F shifted metric
weight from the two smaller scalar obligations:

* `sourceMetric_domination`: the shifted modified metric is bounded by the
  source metric on the active finite family;
* `rate_margin`: the target Appendix-F rate fits inside the Lemma-3 source rate.

The theorem only closes this metric/rate bookkeeping layer; it does not prove
the Lemma-3 activity estimate or any physical raw-source bound. -/
theorem balabanCMP116Lemma3Weight_domination_of_sourceMetric_domination_and_rate_margin
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    (Λ : Finset (OmegaPolymerType HF z))
    {sourceMetric : OmegaPolymerType HF z → ℕ}
    {blockScale : ℕ}
    {delta kappaSource kappa : ℝ}
    (sourceMetric_domination :
      ∀ X, X ∈ Λ →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric X : ℝ))
    (rate_margin :
      kappa ≤
        balabanCMP116Lemma3DecayRate blockScale delta kappaSource)
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ X, X ∈ Λ →
      balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetric X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  balabanCMP116Lemma3Weight_domination
    Λ
    (sourceMetric := sourceMetric)
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    (metric_comparison_of_sourceMetric_domination_and_rate_margin
      Λ sourceMetric_domination rate_margin kappa_nonneg)

/-- Convention-robust bridge from an unshifted source metric to the shifted
Appendix-F weight.

When the source metric vanishes on singleton polymers, the valid geometric
comparison is `d_M(X) ≤ sourceMetric X`, not
`d_M(X) + 1 ≤ sourceMetric X`.  The missing unit is paid exactly by the
multiplicative factor `exp kappa`; the source decay itself remains unshifted. -/
theorem balabanCMP116Lemma3Weight_le_exp_mul_appendixFHoleExpWeight_of_unshiftedSourceMetric
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    (Λ : Finset (OmegaPolymerType HF z))
    {sourceMetric : OmegaPolymerType HF z → ℕ}
    {blockScale : ℕ}
    {delta kappaSource kappa : ℝ}
    (sourceMetric_domination :
      ∀ X, X ∈ Λ →
        (discreteModifiedMetric HF X.val : ℝ) ≤
          (sourceMetric X : ℝ))
    (rate_margin :
      kappa ≤
        balabanCMP116Lemma3DecayRate blockScale delta kappaSource)
    (kappa_nonneg : 0 ≤ kappa) :
    ∀ X, X ∈ Λ →
      balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetric X ≤
        Real.exp kappa *
          appendixFHoleExpWeight HF kappa X.val := by
  intro X hX
  let dM : ℝ := (discreteModifiedMetric HF X.val : ℝ)
  let m : ℝ := (sourceMetric X : ℝ)
  let sourceRate : ℝ :=
    balabanCMP116Lemma3DecayRate blockScale delta kappaSource
  have hdM : 0 ≤ dM := Nat.cast_nonneg _
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hmetric : kappa * dM ≤ sourceRate * m := by
    calc
      kappa * dM ≤ kappa * m :=
        mul_le_mul_of_nonneg_left
          (by simpa [dM, m] using sourceMetric_domination X hX)
          kappa_nonneg
      _ ≤ sourceRate * m :=
        mul_le_mul_of_nonneg_right rate_margin hm
  have hexp :
      Real.exp (-(sourceRate * m)) ≤
        Real.exp (-(kappa * dM)) :=
    Real.exp_le_exp.mpr (neg_le_neg hmetric)
  have hshift :
      Real.exp (-(kappa * dM)) =
        Real.exp kappa *
          Real.exp
            (-(kappa *
              (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)))) := by
    rw [← Real.exp_add]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [dM]
    ring
  unfold balabanCMP116Lemma3Weight appendixFHoleExpWeight
  simpa [sourceRate, m] using hexp.trans_eq hshift

/-- Scaled, convention-robust bridge from a shifted source metric to the
Appendix-F modified metric.

The geometric comparison is allowed to lose a fixed factor `metricScale`:

`d_M(X) + 1 ≤ metricScale * (sourceMetric X + 1)`.

If `metricScale * kappa` fits below the source decay rate, the one-unit
source normalization costs exactly `exp (metricScale * kappa)` in amplitude.
This is the form needed by the literal dimension-four equation-(2.30)
constant `metricScale = 24`. -/
theorem balabanCMP116Lemma3Weight_le_scaledExp_mul_appendixFHoleExpWeight
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    (Λ : Finset (OmegaPolymerType HF z))
    {sourceMetric : OmegaPolymerType HF z → ℕ}
    {blockScale : ℕ}
    {delta kappaSource metricScale kappa : ℝ}
    (sourceMetric_domination :
      ∀ X, X ∈ Λ →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          metricScale * ((sourceMetric X : ℝ) + 1))
    (rate_margin :
      metricScale * kappa ≤
        balabanCMP116Lemma3DecayRate blockScale delta kappaSource)
    (kappa_nonneg : 0 ≤ kappa) :
    ∀ X, X ∈ Λ →
      balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetric X ≤
        Real.exp (metricScale * kappa) *
          appendixFHoleExpWeight HF kappa X.val := by
  intro X hX
  let dM : ℝ := (discreteModifiedMetric HF X.val : ℝ)
  let m : ℝ := (sourceMetric X : ℝ)
  let sourceRate : ℝ :=
    balabanCMP116Lemma3DecayRate blockScale delta kappaSource
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hscaled :
      kappa * (dM + 1) ≤
        metricScale * kappa + sourceRate * m := by
    have hgeom :
        kappa * (dM + 1) ≤
          kappa * (metricScale * (m + 1)) := by
      apply mul_le_mul_of_nonneg_left _ kappa_nonneg
      simpa [dM, m, Nat.cast_add, Nat.cast_one] using
        sourceMetric_domination X hX
    have hrate :
        (metricScale * kappa) * m ≤ sourceRate * m := by
      exact mul_le_mul_of_nonneg_right rate_margin hm
    nlinarith
  have hexp :
      Real.exp (-(sourceRate * m)) ≤
        Real.exp
          (metricScale * kappa - kappa * (dM + 1)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hsplit :
      Real.exp
          (metricScale * kappa - kappa * (dM + 1)) =
        Real.exp (metricScale * kappa) *
          Real.exp (-(kappa * (dM + 1))) := by
    rw [← Real.exp_add]
    congr 1
  unfold balabanCMP116Lemma3Weight appendixFHoleExpWeight
  simpa [sourceRate, m, dM, Nat.cast_add, Nat.cast_one] using
    hexp.trans_eq hsplit

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

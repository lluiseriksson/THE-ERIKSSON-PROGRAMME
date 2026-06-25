/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma3ScaleFamily

/-!
# CMP116 equation (2.37) post-P majorization boundary

This module isolates the final post-`P` majorization supported by CMP116
equation (2.37), the following summation paragraph, and the displayed `C3`
shape on page 20.

Honest scope: this file does not prove the combined post-`P` source sum, does
not identify the dependent `Z0/Z0'` source indices with the repository
indices, and does not assign numerical values to any source `O(1)` constant.
It only packages a source-shaped exponent-absorption inequality and an
explicit amplitude comparison into the existing
`CMP116PostPResidualSourceMajorizationScaleFamily` consumer.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Source-shaped Eq. (2.37) majorization boundary for the post-`P` stage.

The field `residualExponent` represents the leftover page-20 exponential
factor, including the `alpha5`/cardinality contribution and any other residual
terms that must be absorbed into the reserve between the source
`(1 - 7*delta)/2` decay and the canonical Lemma-3 `(1 - 8*delta)/2` decay.

The amplitude comparison is deliberately stated directly as
`postPAmplitude <= C3*epsilon1`; distinct source occurrences of `O(1)` must be
majorized before this boundary is instantiated. -/
structure CMP116Eq237MajorizationBoundary
    {σ : ℕ → ℕ → Type*}
    (hp : ∀ _t _k, CMP116Lemma3Parameters)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ) where

  residualExponent : ∀ t k, σ t k → ℝ

  amplitude_nonneg :
    ∀ t k, 0 ≤ postPAmplitude t k

  amplitude_le_C3 :
    ∀ t k,
      postPAmplitude t k ≤
        (hp t k).C3 * (hp t k).epsilon1

  seven_delta_bound :
    ∀ t k Z,
      postPSourceWeight t k Z ≤
        Real.exp
          (residualExponent t k Z -
            ((1 - 7 * (hp t k).delta) / 2) *
              ((hp t k).blockScale : ℝ) *
              (hp t k).kappa *
              (sourceMetric t k Z : ℝ))

  residual_absorbed :
    ∀ t k Z,
      residualExponent t k Z ≤
        ((hp t k).delta / 2) *
          ((hp t k).blockScale : ℝ) *
          (hp t k).kappa *
          (sourceMetric t k Z : ℝ)

/-- Absorb the Eq. (2.37) residual exponent into the reserve between
`(1 - 7*delta)/2` and the canonical Lemma-3 `(1 - 8*delta)/2` decay. -/
theorem cmp116Eq237_residualExponent_absorbed
    {σ : ℕ → ℕ → Type*}
    (hp : ∀ _t _k, CMP116Lemma3Parameters)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (h :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight postPAmplitude) :
    ∀ t k Z,
      postPSourceWeight t k Z ≤
        balabanCMP116Lemma3Weight
          (hp t k).blockScale
          (hp t k).delta
          (hp t k).kappa
          (sourceMetric t k)
          Z := by
  intro t k Z
  let m : ℝ := (sourceMetric t k Z : ℝ)
  let sourceArg : ℝ :=
    h.residualExponent t k Z -
      ((1 - 7 * (hp t k).delta) / 2) *
        ((hp t k).blockScale : ℝ) *
        (hp t k).kappa *
        m
  let absorbedArg : ℝ :=
    ((hp t k).delta / 2) *
      ((hp t k).blockScale : ℝ) *
      (hp t k).kappa *
      m -
    ((1 - 7 * (hp t k).delta) / 2) *
      ((hp t k).blockScale : ℝ) *
      (hp t k).kappa *
      m
  have hsourceArg_le : sourceArg ≤ absorbedArg := by
    dsimp [sourceArg, absorbedArg, m]
    linarith [h.residual_absorbed t k Z]
  have habsorbedArg :
      absorbedArg =
        -((balabanCMP116Lemma3DecayRate
            (hp t k).blockScale
            (hp t k).delta
            (hp t k).kappa) *
          (sourceMetric t k Z : ℝ)) := by
    dsimp [absorbedArg, m, balabanCMP116Lemma3DecayRate]
    ring
  calc
    postPSourceWeight t k Z ≤ Real.exp sourceArg := by
      simpa [sourceArg, m] using h.seven_delta_bound t k Z
    _ ≤ Real.exp absorbedArg := by
      exact Real.exp_le_exp.mpr hsourceArg_le
    _ =
        balabanCMP116Lemma3Weight
          (hp t k).blockScale
          (hp t k).delta
          (hp t k).kappa
          (sourceMetric t k)
          Z := by
      rw [habsorbedArg]
      simp [balabanCMP116Lemma3Weight]

/-- CMP116 Eq. (2.37) post-`P` exponent absorption and the displayed `C3`
amplitude comparison imply the canonical post-`P` majorization consumed by the
Lemma-3 scale-family interface. -/
theorem cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237
    {σ : ℕ → ℕ → Type*}
    (hp : ∀ _t _k, CMP116Lemma3Parameters)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (h :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight postPAmplitude) :
    CMP116PostPResidualSourceMajorizationScaleFamily
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      postPSourceWeight
      postPAmplitude := by
  intro t k Z
  have hweight :
      postPSourceWeight t k Z ≤
        balabanCMP116Lemma3Weight
          (hp t k).blockScale
          (hp t k).delta
          (hp t k).kappa
          (sourceMetric t k)
          Z :=
    cmp116Eq237_residualExponent_absorbed
      hp sourceMetric postPSourceWeight postPAmplitude h t k Z
  calc
    postPAmplitude t k * postPSourceWeight t k Z ≤
        postPAmplitude t k *
          balabanCMP116Lemma3Weight
            (hp t k).blockScale
            (hp t k).delta
            (hp t k).kappa
            (sourceMetric t k)
            Z := by
      exact mul_le_mul_of_nonneg_left hweight (h.amplitude_nonneg t k)
    _ ≤
        ((hp t k).C3 * (hp t k).epsilon1) *
          balabanCMP116Lemma3Weight
            (hp t k).blockScale
            (hp t k).delta
            (hp t k).kappa
            (sourceMetric t k)
            Z := by
      exact
        mul_le_mul_of_nonneg_right
          (h.amplitude_le_C3 t k)
          (balabanCMP116Lemma3Weight_nonneg
            (hp t k).blockScale
            (hp t k).delta
            (hp t k).kappa
            (sourceMetric t k)
            Z)

/-- Build the weighted post-`P` boundary from a combined post-`P` source sum
and the Eq. (2.37)/`C3` majorization boundary.

This removes the independent caller-supplied `postP_majorization` field on
this source-facing route.  The combined finite post-`P` source estimate remains
an explicit input. -/
def CMP116Lemma3WeightedPostPSourceScaleBoundary.of_sourceBound_eq237Majorization
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
    (postPAmplitude : ℕ → ℕ → ℝ)
    (hsource :
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
            (pResidualWeight t k)))
    (hmajorization :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight postPAmplitude) :
    CMP116Lemma3WeightedPostPSourceScaleBoundary
      hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
      postPSourceWeight postPAmplitude where

  postP_source_bound := hsource

  postP_majorization :=
    cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237
      hp sourceMetric postPSourceWeight postPAmplitude hmajorization

namespace CMP116Lemma3WeightedPostPScaleSourceAssumptions

/-- Build the weighted post-`P` source package from Eq. (2.29), a supplied
P-stage source boundary, the combined post-`P` source sum, the Eq. (2.37)
majorization boundary, and the activity/termwise boundary.

Compared with `of_boundaries`, this route removes the caller-supplied
`CMP116Lemma3WeightedPostPSourceScaleBoundary` package.  The combined post-`P`
source estimate remains explicit, while the canonical post-`P` majorization is
generated from `CMP116Eq237MajorizationBoundary`. -/
def of_eq237Majorization
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
    (hsource :
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
            (pResidualWeight t k)))
    (hmajorization :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    pStage
    (CMP116Lemma3WeightedPostPSourceScaleBoundary.of_sourceBound_eq237Majorization
      hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
      postPSourceWeight postPAmplitude hsource hmajorization)
    activity

/-- Direct Lemma-3 scale-family consumer using the Eq. (2.37) majorization
boundary for the weighted post-`P` stage.

This is the estimate-level counterpart of `of_eq237Majorization`: it still
requires Eq. (2.29), the P-stage source boundary, the combined post-`P` source
sum, and the activity/termwise boundary explicitly. -/
def lemma3_activity_estimate_of_eq237Majorization
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
    (hsource :
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
            (pResidualWeight t k)))
    (hmajorization :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight postPAmplitude)
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
    (of_eq237Majorization eq229 pStage hsource hmajorization activity)

end CMP116Lemma3WeightedPostPScaleSourceAssumptions

end YangMills.RG

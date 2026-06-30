/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeFluctuationActivity

/-!
# CMP116 Lemma 3 activity estimate interface

This module isolates the activity-only conclusion interface for Balaban CMP116
Lemma 3 / equation (2.38).  It names the native source-metric exponential
weight, the final pointwise activity estimate, and the zero-content adapter into
`PhysicalGaugeRawActivityDecay`.

Honest scope: this file does not construct the localized activities, prove the
analytic Lemma 3 resummation, identify a Wilson Hessian, construct a covariance
root, or prove any Gaussian pushforward.  It is deliberately below all CMP116
source-frontier packaging.
-/

namespace YangMills.RG

/-- The exponent rate in the CMP116 Lemma 3 source weight. -/
noncomputable def balabanCMP116Lemma3DecayRate
    (blockScale : ℕ) (delta kappaSource : ℝ) : ℝ :=
  (1 - 8 * delta) * ((1 : ℝ) / 2) *
    (blockScale : ℝ) * kappaSource

/-- The dimensionless decay multiplier in the CMP116 Lemma 3 source weight. -/
noncomputable def balabanCMP116Lemma3DecayFactor
    (blockScale : ℕ) (delta : ℝ) : ℝ :=
  (1 - 8 * delta) * ((1 : ℝ) / 2) * (blockScale : ℝ)

/-- A source-friendly sufficient condition for the dimensionless Lemma-3
decay reserve.

This is only scalar arithmetic: it does not assert that CMP116 supplies
`delta <= 1/16` or `4 <= blockScale`.  It is useful when a source constant
hierarchy provides those two primitive bounds instead of the packaged reserve
`1 <= ((1 - 8*delta)/2) * blockScale`. -/
theorem balabanCMP116Lemma3DecayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
    {blockScale : ℕ} {delta : ℝ}
    (hdelta : delta ≤ (1 : ℝ) / 16)
    (hblock : 4 ≤ blockScale) :
    1 ≤ balabanCMP116Lemma3DecayFactor blockScale delta := by
  have hfactor :
      (1 : ℝ) / 2 ≤ 1 - 8 * delta := by
    linarith
  have hblock_real : (4 : ℝ) ≤ (blockScale : ℝ) := by
    exact_mod_cast hblock
  have hblock_half :
      (2 : ℝ) ≤ ((1 : ℝ) / 2) * (blockScale : ℝ) := by
    nlinarith
  have hfactor_nonneg :
      0 ≤ 1 - 8 * delta := by
    linarith
  have hmul :
      ((1 : ℝ) / 2) * 2 ≤
        (1 - 8 * delta) *
          (((1 : ℝ) / 2) * (blockScale : ℝ)) :=
    mul_le_mul hfactor hblock_half (by norm_num) hfactor_nonneg
  rw [balabanCMP116Lemma3DecayFactor]
  nlinarith [hmul]

/-- Reduce the Lemma-3/App-F rate margin to a source-rate comparison and the
dimensionless scale reserve `1 <= ((1 - 8*delta)/2) * L`.

This is only scalar arithmetic: it proves no CMP116 estimate and supplies no
source constants. -/
theorem balabanCMP116Lemma3_rate_margin_of_sourceRate_le_and_decayFactor
    {blockScale : ℕ} {delta kappaTarget kappaSource : ℝ}
    (htarget_le_source : kappaTarget ≤ kappaSource)
    (hkappaSource_nonneg : 0 ≤ kappaSource)
    (hfactor :
      1 ≤ balabanCMP116Lemma3DecayFactor blockScale delta) :
    kappaTarget ≤
      balabanCMP116Lemma3DecayRate blockScale delta kappaSource := by
  have hsource_le :
      kappaSource ≤
        balabanCMP116Lemma3DecayFactor blockScale delta * kappaSource := by
    simpa using
      (mul_le_mul_of_nonneg_right hfactor hkappaSource_nonneg)
  exact htarget_le_source.trans (by
    simpa [balabanCMP116Lemma3DecayRate,
      balabanCMP116Lemma3DecayFactor, mul_assoc] using hsource_le)

/-- Nonnegativity of the Lemma-3 decay rate from nonnegativity of its
dimensionless decay factor and the source rate.

This is scalar bookkeeping only: it does not prove any CMP116 component
estimate or identify source constants. -/
theorem balabanCMP116Lemma3DecayRate_nonneg_of_decayFactor_nonneg
    {blockScale : ℕ} {delta kappaSource : ℝ}
    (hfactor_nonneg :
      0 ≤ balabanCMP116Lemma3DecayFactor blockScale delta)
    (hkappaSource_nonneg : 0 ≤ kappaSource) :
    0 ≤
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource := by
  simpa [balabanCMP116Lemma3DecayRate,
    balabanCMP116Lemma3DecayFactor, mul_assoc] using
      mul_nonneg hfactor_nonneg hkappaSource_nonneg

/-- Nonnegativity of the Lemma-3 decay rate from the standard dimensionless
reserve `1 <= balabanCMP116Lemma3DecayFactor` and a nonnegative source rate.

This removes the separate `lemma3Rate_nonneg` scalar premise in downstream
transport packages whenever the same reserve used for the Lemma-3 rate margin
is available. -/
theorem balabanCMP116Lemma3DecayRate_nonneg_of_decayFactor_reserve
    {blockScale : ℕ} {delta kappaSource : ℝ}
    (hfactor :
      1 ≤ balabanCMP116Lemma3DecayFactor blockScale delta)
    (hkappaSource_nonneg : 0 ≤ kappaSource) :
    0 ≤
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource :=
  balabanCMP116Lemma3DecayRate_nonneg_of_decayFactor_nonneg
    (by linarith)
    hkappaSource_nonneg

/-- Nonnegativity of the Lemma-3 decay rate from the primitive source constant
bounds `delta <= 1/16` and `4 <= blockScale`.

This is only the scalar constant route into the rate nonnegativity premise; it
does not prove the source constant hierarchy itself. -/
theorem balabanCMP116Lemma3DecayRate_nonneg_of_delta_le_one_sixteen_and_four_le_blockScale
    {blockScale : ℕ} {delta kappaSource : ℝ}
    (hdelta : delta ≤ (1 : ℝ) / 16)
    (hblock : 4 ≤ blockScale)
    (hkappaSource_nonneg : 0 ≤ kappaSource) :
    0 ≤
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource :=
  balabanCMP116Lemma3DecayRate_nonneg_of_decayFactor_reserve
    (balabanCMP116Lemma3DecayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      hdelta hblock)
    hkappaSource_nonneg

/-- Native source-metric weight for the CMP116 Lemma 3 conclusion. -/
noncomputable def balabanCMP116Lemma3Weight
    {ι : Type*}
    (blockScale : ℕ)
    (delta kappaSource : ℝ)
    (sourceMetric : ι → ℕ)
    (X : ι) : ℝ :=
  Real.exp
    (-(balabanCMP116Lemma3DecayRate blockScale delta kappaSource *
      (sourceMetric X : ℝ)))

/-- The native CMP116 Lemma 3 source weight is nonnegative. -/
theorem balabanCMP116Lemma3Weight_nonneg
    {ι : Type*}
    (blockScale : ℕ)
    (delta kappaSource : ℝ)
    (sourceMetric : ι → ℕ)
    (X : ι) :
    0 ≤
      balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric X :=
  Real.exp_nonneg _

/-- Compare a CMP119 B/local native weight with the CMP116 Lemma-3 source
weight from the exact exponent comparison.

This is a dictionary lemma only: the source metric comparison and rate
comparison remain explicit, and no CMP119 or CMP116 estimate is proved here. -/
theorem cmp119BLocalWeight_le_balabanCMP116Lemma3Weight_of_exponent_comparison
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (exponent_comparison :
      ∀ X,
        balabanCMP116Lemma3DecayRate
            blockScale delta kappaSource *
          (sourceMetricLemma X : ℝ) ≤
        kappaB * sourceMetricB X) :
    ∀ X,
      cmp119BLocalWeight kappaB sourceMetricB X ≤
        balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetricLemma X := by
  intro X
  unfold cmp119BLocalWeight balabanCMP116Lemma3Weight
  exact Real.exp_le_exp.mpr
    (neg_le_neg (exponent_comparison X))

/-- The B/local metric nonnegativity needed for scalar transport follows from
dominating a Nat-valued Lemma-3 source metric.  Thus the B/local-to-Lemma-3
transport dictionary does not need to carry this as a separate source
obligation. -/
theorem cmp119BLocal_sourceMetricB_nonneg_of_sourceMetric_domination
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    (sourceMetric_domination :
      ∀ X, (sourceMetricLemma X : ℝ) ≤ sourceMetricB X) :
    ∀ X, 0 ≤ sourceMetricB X :=
  fun X => (Nat.cast_nonneg (sourceMetricLemma X)).trans
    (sourceMetric_domination X)

/-- Narrow B/local metric dictionary frontier.

This record names exactly the still-open comparison between the CMP116 Lemma-3
source metric and the CMP109/CMP119 B/local metric.  It does not define
`d_j(X)`, prove that CMP109/CMP119 print this inequality, prove CMP119
Eq. (2.42), identify the B/local activity with Lean `bloc`, prove the B/local
rate margin, or prove any component decay. -/
structure CMP119BLocalMetricDictionary
    {ι : Type*}
    (sourceMetricB : ι → ℝ)
    (sourceMetricLemma : ι → ℕ) : Prop where
  sourceMetric_domination :
    ∀ X, (sourceMetricLemma X : ℝ) ≤ sourceMetricB X

namespace CMP119BLocalMetricDictionary

/-- Project the narrow B/local metric dictionary to the scalar comparison
needed by `CMP119BLocalToLemma3WeightTransport.sourceMetric_domination`. -/
theorem to_sourceMetric_domination
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    (h :
      CMP119BLocalMetricDictionary
        sourceMetricB sourceMetricLemma) :
    ∀ X, (sourceMetricLemma X : ℝ) ≤ sourceMetricB X :=
  h.sourceMetric_domination

/-- Nat-valued metric helper for a later concrete `d_j` dictionary.

This is only coercion bookkeeping: it turns a Nat-valued comparison into the
Real-valued metric domination shape, and proves no CMP109/CMP119 source
identification. -/
theorem sourceMetric_domination_of_natMetric
    {ι : Type*}
    {dB sourceMetricLemma : ι → ℕ}
    (h : ∀ X, sourceMetricLemma X ≤ dB X) :
    ∀ X, (sourceMetricLemma X : ℝ) ≤ (dB X : ℝ) :=
  fun X => by exact_mod_cast h X

/-- Package a Nat-valued metric comparison as the narrow B/local metric
dictionary.

The comparison itself remains an explicit hypothesis; this constructor only
performs the Nat-to-Real coercion and does not define or prove the paper metric
comparison. -/
theorem of_natMetric
    {ι : Type*}
    {dB sourceMetricLemma : ι → ℕ}
    (h : ∀ X, sourceMetricLemma X ≤ dB X) :
    CMP119BLocalMetricDictionary
      (fun X => (dB X : ℝ)) sourceMetricLemma where
  sourceMetric_domination :=
    sourceMetric_domination_of_natMetric h

end CMP119BLocalMetricDictionary

/-- Narrow B/local scalar rate-margin dictionary frontier.

This record names exactly the still-open scalar comparison between the CMP116
Lemma-3 decay rate and the CMP119 B/local decay rate.  It proves no source
constant hierarchy, no CMP119 Eq. (2.42), no B/local activity identification,
and no component decay. -/
structure CMP119BLocalRateMarginDictionary
    (blockScale : ℕ)
    (delta kappaSource kappaB : ℝ) : Prop where
  rate_margin :
    balabanCMP116Lemma3DecayRate
      blockScale delta kappaSource ≤ kappaB

namespace CMP119BLocalRateMarginDictionary

/-- Project the narrow B/local rate dictionary to the scalar margin consumed by
`CMP119BLocalToLemma3WeightTransport.rate_margin`. -/
theorem to_rate_margin
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (h :
      CMP119BLocalRateMarginDictionary
        blockScale delta kappaSource kappaB) :
    balabanCMP116Lemma3DecayRate
      blockScale delta kappaSource ≤ kappaB :=
  h.rate_margin

end CMP119BLocalRateMarginDictionary

/-- Narrow B/local amplitude-relaxation dictionary frontier.

This record names exactly the two scalar amplitude facts needed to reuse a
CMP119 B/local source amplitude `HbSrc` inside a downstream E/R/B budget `Hb`.
It proves no CMP119 Eq. (2.42), no source amplitude hierarchy, no B/local
activity identification, and no component decay. -/
structure CMP119BLocalAmplitudeRelaxationDictionary
    (HbSrc Hb : ℝ) : Prop where
  HbSrc_nonneg :
    0 ≤ HbSrc
  HbSrc_le :
    HbSrc ≤ Hb

namespace CMP119BLocalAmplitudeRelaxationDictionary

/-- Project the source-amplitude nonnegativity consumed by B/local boundary
constructors. -/
theorem to_HbSrc_nonneg
    {HbSrc Hb : ℝ}
    (h :
      CMP119BLocalAmplitudeRelaxationDictionary HbSrc Hb) :
    0 ≤ HbSrc :=
  h.HbSrc_nonneg

/-- Project the scalar amplitude relaxation consumed by downstream B/local
transport constructors. -/
theorem to_HbSrc_le
    {HbSrc Hb : ℝ}
    (h :
      CMP119BLocalAmplitudeRelaxationDictionary HbSrc Hb) :
    HbSrc ≤ Hb :=
  h.HbSrc_le

/-- The downstream amplitude is nonnegative whenever the source amplitude is
nonnegative and relaxes into it. -/
theorem Hb_nonneg
    {HbSrc Hb : ℝ}
    (h :
      CMP119BLocalAmplitudeRelaxationDictionary HbSrc Hb) :
    0 ≤ Hb :=
  h.HbSrc_nonneg.trans h.HbSrc_le

/-- Build the B/local amplitude-relaxation dictionary from an explicit
nonnegative scalar slack.

This is scalar bookkeeping only: it proves no CMP119 Eq. (2.42), no source
amplitude hierarchy, no B/local activity identification, and no component
decay. -/
theorem of_slack
    {HbSrc Hb slack : ℝ}
    (hSrc : 0 ≤ HbSrc)
    (hSlack : 0 ≤ slack)
    (hHb : Hb = HbSrc + slack) :
    CMP119BLocalAmplitudeRelaxationDictionary HbSrc Hb := by
  refine ⟨hSrc, ?_⟩
  rw [hHb]
  exact le_add_of_nonneg_right hSlack

end CMP119BLocalAmplitudeRelaxationDictionary

/-- Narrow B/local activity-identification dictionary frontier.

This record names exactly the source-to-Lean identification needed to reuse the
CMP119 B/local paper-native scalar term as the Lean `bloc.globalEval` activity.
It proves no CMP119 Eq. (2.42), no source bound, no metric/rate dictionary, no
amplitude relaxation, and no component decay. -/
structure CMP119BLocalActivityIdentificationDictionary
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (sourceEval :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ)
    (bloc : ι → PhysicalGaugeLocalActivity dPhys N Nc) : Prop where
  bloc_identification :
    ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
      (bloc X).globalEval ψ φ = sourceEval X ψ φ

namespace CMP119BLocalActivityIdentificationDictionary

/-- Project the B/local activity-identification dictionary to the raw equality
consumed by the source-bound-to-activity routes. -/
theorem to_bloc_identification
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {sourceEval :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ}
    {bloc : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    (h :
      CMP119BLocalActivityIdentificationDictionary sourceEval bloc) :
    ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
      (bloc X).globalEval ψ φ = sourceEval X ψ φ :=
  h.bloc_identification

end CMP119BLocalActivityIdentificationDictionary

/-- A rate/metric sufficient condition for transporting the CMP119 B/local
native weight into the CMP116 Lemma-3 source weight.

The content is scalar bookkeeping: if the Lemma-3 source metric is dominated by
the B/local metric and the Lemma-3 decay rate is no larger than the B/local
rate, then the B/local exponential weight is bounded by the Lemma-3 weight. -/
theorem cmp119BLocalWeight_le_balabanCMP116Lemma3Weight_of_metric_domination_and_rate_margin
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (sourceMetric_domination :
      ∀ X, (sourceMetricLemma X : ℝ) ≤ sourceMetricB X)
    (rate_margin :
      balabanCMP116Lemma3DecayRate
          blockScale delta kappaSource ≤ kappaB)
    (lemma3Rate_nonneg :
      0 ≤
        balabanCMP116Lemma3DecayRate
          blockScale delta kappaSource) :
    ∀ X,
      cmp119BLocalWeight kappaB sourceMetricB X ≤
        balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetricLemma X :=
  cmp119BLocalWeight_le_balabanCMP116Lemma3Weight_of_exponent_comparison
    (sourceMetricB := sourceMetricB)
    (sourceMetricLemma := sourceMetricLemma)
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappaB := kappaB)
    (fun X => by
      calc
        balabanCMP116Lemma3DecayRate
              blockScale delta kappaSource *
            (sourceMetricLemma X : ℝ)
            ≤ balabanCMP116Lemma3DecayRate
                blockScale delta kappaSource *
              sourceMetricB X := by
              exact mul_le_mul_of_nonneg_left
                (sourceMetric_domination X) lemma3Rate_nonneg
        _ ≤ kappaB * sourceMetricB X := by
              exact mul_le_mul_of_nonneg_right
                rate_margin
                (cmp119BLocal_sourceMetricB_nonneg_of_sourceMetric_domination
                  sourceMetric_domination X))

/-- Dictionary package for transporting a CMP119 B/local native exponential
weight into the CMP116 Lemma-3 source weight.

The fields are exactly the remaining metric/rate obligations: identify the
source metrics well enough to dominate the Lemma-3 source metric by the
B/local metric, prove the B/local rate is large enough, and provide Lemma-3
rate nonnegativity.  B/local metric nonnegativity follows from metric
domination because the Lemma-3 source metric is Nat-valued.  This package
proves no CMP119 estimate and no source-to-Lean activity dictionary. -/
structure CMP119BLocalToLemma3WeightTransport
    {ι : Type*}
    (sourceMetricB : ι → ℝ)
    (sourceMetricLemma : ι → ℕ)
    (blockScale : ℕ)
    (delta kappaSource kappaB : ℝ) : Prop where
  sourceMetric_domination :
    ∀ X, (sourceMetricLemma X : ℝ) ≤ sourceMetricB X
  rate_margin :
    balabanCMP116Lemma3DecayRate
      blockScale delta kappaSource ≤ kappaB
  lemma3Rate_nonneg :
    0 ≤
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource

namespace CMP119BLocalToLemma3WeightTransport

/-- Project a B/local-to-Lemma-3 transport dictionary to the pointwise weight
domination consumed by the component-boundary transport layer. -/
theorem weight_domination
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (h :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetricLemma
        blockScale delta kappaSource kappaB) :
    ∀ X,
      cmp119BLocalWeight kappaB sourceMetricB X ≤
        balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetricLemma X :=
  cmp119BLocalWeight_le_balabanCMP116Lemma3Weight_of_metric_domination_and_rate_margin
    h.sourceMetric_domination
    h.rate_margin
    h.lemma3Rate_nonneg

/-- Build the B/local-to-Lemma-3 transport dictionary when the Lemma-3 rate
nonnegativity is supplied by the standard dimensionless decay-factor reserve.

The remaining source-specific facts are still explicit: B/local metric
domination and the B/local rate margin. -/
theorem of_decayFactor_reserve
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (sourceMetric_domination :
      ∀ X, (sourceMetricLemma X : ℝ) ≤ sourceMetricB X)
    (rate_margin :
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource ≤ kappaB)
    (hkappaSource_nonneg : 0 ≤ kappaSource)
    (decayFactor_reserve :
      1 ≤ balabanCMP116Lemma3DecayFactor blockScale delta) :
    CMP119BLocalToLemma3WeightTransport
      sourceMetricB sourceMetricLemma
      blockScale delta kappaSource kappaB where
  sourceMetric_domination := sourceMetric_domination
  rate_margin := rate_margin
  lemma3Rate_nonneg :=
    balabanCMP116Lemma3DecayRate_nonneg_of_decayFactor_reserve
      decayFactor_reserve hkappaSource_nonneg

/-- Build the B/local-to-Lemma-3 transport dictionary from the narrow B/local
metric dictionary and the standard dimensionless decay-factor reserve.

This closes only the transport constructor's `sourceMetric_domination` input by
projecting it from `CMP119BLocalMetricDictionary`.  The metric comparison itself,
the B/local rate margin, and the scalar reserve remain explicit hypotheses; no
CMP109 `d_j` definition, CMP119 Eq. (2.42), activity identification, component
decay, or total raw decay is proved here. -/
theorem of_metricDictionary_decayFactor_reserve
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (metricDictionary :
      CMP119BLocalMetricDictionary sourceMetricB sourceMetricLemma)
    (rate_margin :
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource ≤ kappaB)
    (hkappaSource_nonneg : 0 ≤ kappaSource)
    (decayFactor_reserve :
      1 ≤ balabanCMP116Lemma3DecayFactor blockScale delta) :
    CMP119BLocalToLemma3WeightTransport
      sourceMetricB sourceMetricLemma
      blockScale delta kappaSource kappaB :=
  CMP119BLocalToLemma3WeightTransport.of_decayFactor_reserve
    metricDictionary.to_sourceMetric_domination
    rate_margin
    hkappaSource_nonneg
    decayFactor_reserve

/-- Build the B/local-to-Lemma-3 transport dictionary from separate metric and
rate-margin dictionaries plus the standard dimensionless decay-factor reserve.

This projects the two named dictionary frontiers into the transport package.  It
does not prove the metric comparison, the B/local rate margin, CMP119 Eq. (2.42),
activity identification, component decay, or total raw decay. -/
theorem of_metricAndRateDictionaries_decayFactor_reserve
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (metricDictionary :
      CMP119BLocalMetricDictionary sourceMetricB sourceMetricLemma)
    (rateDictionary :
      CMP119BLocalRateMarginDictionary
        blockScale delta kappaSource kappaB)
    (hkappaSource_nonneg : 0 ≤ kappaSource)
    (decayFactor_reserve :
      1 ≤ balabanCMP116Lemma3DecayFactor blockScale delta) :
    CMP119BLocalToLemma3WeightTransport
      sourceMetricB sourceMetricLemma
      blockScale delta kappaSource kappaB :=
  CMP119BLocalToLemma3WeightTransport.of_metricDictionary_decayFactor_reserve
    metricDictionary
    rateDictionary.to_rate_margin
    hkappaSource_nonneg
    decayFactor_reserve

/-- Build the B/local-to-Lemma-3 transport dictionary from the primitive scalar
constant bounds `delta <= 1/16` and `4 <= blockScale`.

This proves only the Lemma-3 rate nonnegativity slot of the transport package
from those scalar bounds; it still does not prove the B/local source estimate,
the B/local metric dictionary, or the B/local rate margin.  B/local metric
nonnegativity is derived from metric domination. -/
theorem of_delta_le_one_sixteen_and_four_le_blockScale
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (sourceMetric_domination :
      ∀ X, (sourceMetricLemma X : ℝ) ≤ sourceMetricB X)
    (rate_margin :
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource ≤ kappaB)
    (hkappaSource_nonneg : 0 ≤ kappaSource)
    (delta_le_one_sixteen : delta ≤ (1 : ℝ) / 16)
    (four_le_blockScale : 4 ≤ blockScale) :
    CMP119BLocalToLemma3WeightTransport
      sourceMetricB sourceMetricLemma
      blockScale delta kappaSource kappaB :=
  CMP119BLocalToLemma3WeightTransport.of_decayFactor_reserve
    sourceMetric_domination
    rate_margin
    hkappaSource_nonneg
    (balabanCMP116Lemma3DecayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      delta_le_one_sixteen four_le_blockScale)

/-- Build the B/local-to-Lemma-3 transport dictionary from the narrow B/local
metric dictionary and primitive small-delta/large-block scalar bounds.

This is the metric-dictionary companion to
`of_delta_le_one_sixteen_and_four_le_blockScale`: it projects the supplied
`CMP119BLocalMetricDictionary` and derives only the Lemma-3 rate nonnegativity
bookkeeping from scalar bounds.  The actual metric dictionary field and the
B/local rate margin remain open inputs. -/
theorem of_metricDictionary_delta_le_one_sixteen_and_four_le_blockScale
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (metricDictionary :
      CMP119BLocalMetricDictionary sourceMetricB sourceMetricLemma)
    (rate_margin :
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource ≤ kappaB)
    (hkappaSource_nonneg : 0 ≤ kappaSource)
    (delta_le_one_sixteen : delta ≤ (1 : ℝ) / 16)
    (four_le_blockScale : 4 ≤ blockScale) :
    CMP119BLocalToLemma3WeightTransport
      sourceMetricB sourceMetricLemma
      blockScale delta kappaSource kappaB :=
  CMP119BLocalToLemma3WeightTransport.of_metricDictionary_decayFactor_reserve
    metricDictionary
    rate_margin
    hkappaSource_nonneg
    (balabanCMP116Lemma3DecayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      delta_le_one_sixteen four_le_blockScale)

/-- Build the B/local-to-Lemma-3 transport dictionary from separate metric and
rate-margin dictionaries plus primitive small-delta/large-block scalar bounds.

This is the dictionary-projection companion to
`of_metricDictionary_delta_le_one_sixteen_and_four_le_blockScale`; it only
threads named metric/rate dictionary inputs and derives the Lemma-3 rate
nonnegativity bookkeeping from scalar bounds. -/
theorem of_metricAndRateDictionaries_delta_le_one_sixteen_and_four_le_blockScale
    {ι : Type*}
    {sourceMetricB : ι → ℝ} {sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (metricDictionary :
      CMP119BLocalMetricDictionary sourceMetricB sourceMetricLemma)
    (rateDictionary :
      CMP119BLocalRateMarginDictionary
        blockScale delta kappaSource kappaB)
    (hkappaSource_nonneg : 0 ≤ kappaSource)
    (delta_le_one_sixteen : delta ≤ (1 : ℝ) / 16)
    (four_le_blockScale : 4 ≤ blockScale) :
    CMP119BLocalToLemma3WeightTransport
      sourceMetricB sourceMetricLemma
      blockScale delta kappaSource kappaB :=
  CMP119BLocalToLemma3WeightTransport.of_metricDictionary_delta_le_one_sixteen_and_four_le_blockScale
    metricDictionary
    rateDictionary.to_rate_margin
    hkappaSource_nonneg
    delta_le_one_sixteen
    four_le_blockScale

/-- Natural-valued B/local metric specialization of
`of_decayFactor_reserve`.

The genuine source dictionary still has to provide the B/local metric
domination, the B/local rate margin, and the scalar reserve. -/
theorem of_natMetric_decayFactor_reserve
    {ι : Type*}
    {sourceMetricB sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (sourceMetric_domination :
      ∀ X, sourceMetricLemma X ≤ sourceMetricB X)
    (rate_margin :
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource ≤ kappaB)
    (hkappaSource_nonneg : 0 ≤ kappaSource)
    (decayFactor_reserve :
      1 ≤ balabanCMP116Lemma3DecayFactor blockScale delta) :
    CMP119BLocalToLemma3WeightTransport
      (fun X => (sourceMetricB X : ℝ)) sourceMetricLemma
      blockScale delta kappaSource kappaB :=
  CMP119BLocalToLemma3WeightTransport.of_decayFactor_reserve
    (fun X => by exact_mod_cast sourceMetric_domination X)
    rate_margin
    hkappaSource_nonneg
    decayFactor_reserve

/-- Natural-valued B/local metric specialization with primitive
small-delta/large-block scalar bounds.

This is the Nat-metric companion to
`of_delta_le_one_sixteen_and_four_le_blockScale`: it discharges only the
Lemma-3 rate nonnegativity bookkeeping field.  The B/local metric domination
and B/local rate margin remain explicit source/dictionary obligations. -/
theorem of_natMetric_delta_le_one_sixteen_and_four_le_blockScale
    {ι : Type*}
    {sourceMetricB sourceMetricLemma : ι → ℕ}
    {blockScale : ℕ} {delta kappaSource kappaB : ℝ}
    (sourceMetric_domination :
      ∀ X, sourceMetricLemma X ≤ sourceMetricB X)
    (rate_margin :
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource ≤ kappaB)
    (hkappaSource_nonneg : 0 ≤ kappaSource)
    (delta_le_one_sixteen : delta ≤ (1 : ℝ) / 16)
    (four_le_blockScale : 4 ≤ blockScale) :
    CMP119BLocalToLemma3WeightTransport
      (fun X => (sourceMetricB X : ℝ)) sourceMetricLemma
      blockScale delta kappaSource kappaB :=
  CMP119BLocalToLemma3WeightTransport.of_natMetric_decayFactor_reserve
    sourceMetric_domination
    rate_margin
    hkappaSource_nonneg
    (balabanCMP116Lemma3DecayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      delta_le_one_sixteen four_le_blockScale)

end CMP119BLocalToLemma3WeightTransport

namespace PhysicalGaugeDimock318BLocalComponentBoundary

/-- Build the B/local component boundary at the CMP116 Lemma-3 source weight
from a CMP119 Eq. (2.42)-shaped B/local estimate and a packaged native-weight
transport dictionary.

This isolates the B/local field of the E/R/B boundary: the CMP119 component
estimate, the B/local-to-Lemma-3 metric/rate dictionary, and the amplitude
relaxation remain explicit inputs.  It proves no CMP119 estimate and no
source-to-Lean activity identification. -/
theorem of_cmp119BLocalActivityEstimate_lemma3WeightTransport
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {bloc : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {delta kappaSource HbSrc Hb kappaB : ℝ}
    (HbSrc_nonneg :
      0 ≤ HbSrc)
    (hB :
      CMP119BLocalActivityEstimate
        bloc sourceMetricB HbSrc kappaB)
    (HbSrc_le :
      HbSrc ≤ Hb)
    (transport :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetric
        blockScale delta kappaSource kappaB) :
    PhysicalGaugeDimock318BLocalComponentBoundary
      bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      Hb :=
  (PhysicalGaugeDimock318BLocalComponentBoundary.of_cmp119BLocalActivityEstimate
      HbSrc_nonneg hB).mono
    HbSrc_le
    (CMP119BLocalToLemma3WeightTransport.weight_domination transport)
    (fun X =>
      balabanCMP116Lemma3Weight_nonneg
        blockScale delta kappaSource sourceMetric X)

/-- Build the B/local component boundary at the CMP116 Lemma-3 source weight
from a CMP119 Eq. (2.42)-shaped B/local estimate, packaged native-weight
transport, and a packaged source-amplitude relaxation dictionary.

This is only the amplitude-dictionary variant of
`of_cmp119BLocalActivityEstimate_lemma3WeightTransport`; it proves none of the
source estimate, activity identification, metric dictionary, or rate margin. -/
theorem of_cmp119BLocalActivityEstimate_lemma3WeightTransport_amplitudeDictionary
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {bloc : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {delta kappaSource HbSrc Hb kappaB : ℝ}
    (amplitudeDictionary :
      CMP119BLocalAmplitudeRelaxationDictionary HbSrc Hb)
    (hB :
      CMP119BLocalActivityEstimate
        bloc sourceMetricB HbSrc kappaB)
    (transport :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetric
        blockScale delta kappaSource kappaB) :
    PhysicalGaugeDimock318BLocalComponentBoundary
      bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      Hb :=
  PhysicalGaugeDimock318BLocalComponentBoundary.of_cmp119BLocalActivityEstimate_lemma3WeightTransport
    amplitudeDictionary.to_HbSrc_nonneg
    hB
    amplitudeDictionary.to_HbSrc_le
    transport

end PhysicalGaugeDimock318BLocalComponentBoundary

namespace CMP119BLocalSourceBound

/-- Source-bound route to the B/local raw-decay field at the CMP116 Lemma-3
weight.

This theorem discharges only the `bloc_decay`-shaped obligation from a supplied
CMP119 Eq. (2.42)-shaped source bound, a supplied source-to-Lean B/local
activity identification, and the explicit B/local-to-Lemma-3 weight transport.
It proves neither Eq. (2.42), nor the activity identification, nor the
metric/rate transport dictionary. -/
theorem to_rawActivityDecay_lemma3WeightTransport
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {sourceEval :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ}
    {bloc : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {delta kappaSource HbSrc Hb kappaB : ℝ}
    (h :
      CMP119BLocalSourceBound
        sourceEval sourceMetricB HbSrc kappaB)
    (HbSrc_nonneg :
      0 ≤ HbSrc)
    (activity_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (bloc X).globalEval ψ φ = sourceEval X ψ φ)
    (HbSrc_le :
      HbSrc ≤ Hb)
    (transport :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetric
        blockScale delta kappaSource kappaB) :
    PhysicalGaugeRawActivityDecay
      bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      Hb :=
  (PhysicalGaugeDimock318BLocalComponentBoundary.of_cmp119BLocalActivityEstimate_lemma3WeightTransport
    HbSrc_nonneg
    (h.to_activityEstimate
      HbSrc_nonneg
      activity_identification
      (fun _ => le_rfl))
    HbSrc_le
    transport).to_rawActivityDecay

/-- Source-bound route to the B/local raw-decay field at the CMP116 Lemma-3
weight, using a packaged B/local source-amplitude relaxation dictionary.

This is only the amplitude-dictionary variant of
`to_rawActivityDecay_lemma3WeightTransport`; it proves none of the source bound,
activity identification, metric/rate transport, or total raw decay. -/
theorem to_rawActivityDecay_lemma3WeightTransport_amplitudeDictionary
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {sourceEval :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ}
    {bloc : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {delta kappaSource HbSrc Hb kappaB : ℝ}
    (h :
      CMP119BLocalSourceBound
        sourceEval sourceMetricB HbSrc kappaB)
    (amplitudeDictionary :
      CMP119BLocalAmplitudeRelaxationDictionary HbSrc Hb)
    (activity_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (bloc X).globalEval ψ φ = sourceEval X ψ φ)
    (transport :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetric
        blockScale delta kappaSource kappaB) :
    PhysicalGaugeRawActivityDecay
      bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      Hb :=
  h.to_rawActivityDecay_lemma3WeightTransport
    amplitudeDictionary.to_HbSrc_nonneg
    activity_identification
    amplitudeDictionary.to_HbSrc_le
    transport

/-- Source-bound route to the B/local raw-decay field at the CMP116 Lemma-3
weight, using a packaged B/local activity-identification dictionary.

This is only the activity-identification dictionary variant of
`to_rawActivityDecay_lemma3WeightTransport`; it proves none of the source bound,
amplitude relaxation, metric/rate transport, or total raw decay. -/
theorem to_rawActivityDecay_lemma3WeightTransport_activityDictionary
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {sourceEval :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ}
    {bloc : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {delta kappaSource HbSrc Hb kappaB : ℝ}
    (h :
      CMP119BLocalSourceBound
        sourceEval sourceMetricB HbSrc kappaB)
    (HbSrc_nonneg :
      0 ≤ HbSrc)
    (activityDictionary :
      CMP119BLocalActivityIdentificationDictionary sourceEval bloc)
    (HbSrc_le :
      HbSrc ≤ Hb)
    (transport :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetric
        blockScale delta kappaSource kappaB) :
    PhysicalGaugeRawActivityDecay
      bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      Hb :=
  h.to_rawActivityDecay_lemma3WeightTransport
    HbSrc_nonneg
    activityDictionary.to_bloc_identification
    HbSrc_le
    transport

/-- Source-bound route to the B/local raw-decay field at the CMP116 Lemma-3
weight, using packaged amplitude-relaxation and activity-identification
dictionaries.

This is only the combined dictionary variant of
`to_rawActivityDecay_lemma3WeightTransport`; it proves none of the source bound,
amplitude relaxation, activity identification, metric/rate transport, or total
raw decay. -/
theorem to_rawActivityDecay_lemma3WeightTransport_amplitudeAndActivityDictionaries
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {sourceEval :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ}
    {bloc : ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {delta kappaSource HbSrc Hb kappaB : ℝ}
    (h :
      CMP119BLocalSourceBound
        sourceEval sourceMetricB HbSrc kappaB)
    (amplitudeDictionary :
      CMP119BLocalAmplitudeRelaxationDictionary HbSrc Hb)
    (activityDictionary :
      CMP119BLocalActivityIdentificationDictionary sourceEval bloc)
    (transport :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetric
        blockScale delta kappaSource kappaB) :
    PhysicalGaugeRawActivityDecay
      bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      Hb :=
  h.to_rawActivityDecay_lemma3WeightTransport
    amplitudeDictionary.to_HbSrc_nonneg
    activityDictionary.to_bloc_identification
    amplitudeDictionary.to_HbSrc_le
    transport

end CMP119BLocalSourceBound

/-- Source-facing conclusion of CMP116 Lemma 3 / equation (2.38).

The intended index type contains only the admissible source domains.  If the
eventual physical activity is indexed by a larger type, that admissibility
restriction must be transported explicitly rather than silently strengthening
Lemma 3. -/
def CMP116Lemma3ActivityEstimate
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (physicalActivity :
      ι → PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric : ι → ℕ)
    (blockScale : ℕ)
    (C3 epsilon1 delta kappaSource : ℝ) : Prop :=
  ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
    ‖(physicalActivity X).globalEval ψ φ‖ ≤
      (C3 * epsilon1) *
        balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetric X

/-- Expose CMP116 Lemma 3 in the stable raw-activity predicate already consumed
by the physical/CMP116 construction layer. -/
theorem balabanLemma3_rawActivityDecay
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {physicalActivity :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {C3 epsilon1 delta kappaSource : ℝ}
    (hLemma3 :
      CMP116Lemma3ActivityEstimate
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource) :
    PhysicalGaugeRawActivityDecay
      physicalActivity
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (C3 * epsilon1) := by
  simpa [PhysicalGaugeRawActivityDecay,
    CMP116Lemma3ActivityEstimate] using hLemma3

/-- Source-facing pair of CMP116 Lemma 3 component estimates for the
`deltaE` and local-`R` pieces.

This deliberately does not include the `B`/large-field component.  The current
source frontier anchors that component to CMP119/CMP122 material, so callers
must supply its native decay separately before assembling the full E/R/B
boundary. -/
structure CMP116Lemma3DeltaRlocComponentEstimates
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (deltaE rloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric : ι → ℕ)
    (blockScale : ℕ)
    (Cdelta epsilonDelta Cr epsilonR delta kappaSource : ℝ) :
    Prop where
  HdeltaSrc_nonneg :
    0 ≤ Cdelta * epsilonDelta
  HrSrc_nonneg :
    0 ≤ Cr * epsilonR
  deltaE_estimate :
    CMP116Lemma3ActivityEstimate
      deltaE sourceMetric blockScale
      Cdelta epsilonDelta delta kappaSource
  rloc_estimate :
    CMP116Lemma3ActivityEstimate
      rloc sourceMetric blockScale
      Cr epsilonR delta kappaSource

/-- Source-native CMP116 Lemma 3 delta/local-`R` component estimates before the
CMP116 component notation is identified with Lean local activities.

This records the scalar source estimates against the native Lemma-3 source
weight.  The dictionaries identifying the paper-side delta and local-`R` terms
with `PhysicalGaugeLocalActivity.globalEval` remain explicit inputs to the
conversion theorem below. -/
structure CMP116Lemma3DeltaRlocSourceEstimates
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (sourceDelta sourceRloc :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ)
    (sourceMetric : ι → ℕ)
    (blockScale : ℕ)
    (Cdelta epsilonDelta Cr epsilonR delta kappaSource : ℝ) :
    Prop where
  HdeltaSrc_nonneg :
    0 ≤ Cdelta * epsilonDelta
  HrSrc_nonneg :
    0 ≤ Cr * epsilonR
  delta_source_estimate :
    ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
      ‖sourceDelta X ψ φ‖ ≤
        (Cdelta * epsilonDelta) *
          balabanCMP116Lemma3Weight
            blockScale delta kappaSource sourceMetric X
  rloc_source_estimate :
    ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
      ‖sourceRloc X ψ φ‖ ≤
        (Cr * epsilonR) *
          balabanCMP116Lemma3Weight
            blockScale delta kappaSource sourceMetric X

namespace CMP116Lemma3DeltaRlocSourceEstimates

/-- Convert the source-native delta estimate into the Lean Lemma-3 activity
estimate once the source delta scalar has been identified with the Lean
`deltaE` local activity. -/
theorem to_deltaEActivityEstimate
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {sourceDelta sourceRloc :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ}
    {deltaE :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource : ℝ}
    (h :
      CMP116Lemma3DeltaRlocSourceEstimates
        sourceDelta sourceRloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (deltaE_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (deltaE X).globalEval ψ φ = sourceDelta X ψ φ) :
    CMP116Lemma3ActivityEstimate
      deltaE sourceMetric blockScale
      Cdelta epsilonDelta delta kappaSource := by
  intro X ψ φ
  calc
    ‖(deltaE X).globalEval ψ φ‖ = ‖sourceDelta X ψ φ‖ := by
      rw [deltaE_identification X ψ φ]
    _ ≤
        (Cdelta * epsilonDelta) *
          balabanCMP116Lemma3Weight
            blockScale delta kappaSource sourceMetric X :=
      h.delta_source_estimate X ψ φ

/-- Convert the source-native local-`R` estimate into the Lean Lemma-3 activity
estimate once the source local-`R` scalar has been identified with the Lean
`rloc` local activity. -/
theorem to_rlocActivityEstimate
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {sourceDelta sourceRloc :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ}
    {rloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource : ℝ}
    (h :
      CMP116Lemma3DeltaRlocSourceEstimates
        sourceDelta sourceRloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (rloc_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (rloc X).globalEval ψ φ = sourceRloc X ψ φ) :
    CMP116Lemma3ActivityEstimate
      rloc sourceMetric blockScale
      Cr epsilonR delta kappaSource := by
  intro X ψ φ
  calc
    ‖(rloc X).globalEval ψ φ‖ = ‖sourceRloc X ψ φ‖ := by
      rw [rloc_identification X ψ φ]
    _ ≤
        (Cr * epsilonR) *
          balabanCMP116Lemma3Weight
            blockScale delta kappaSource sourceMetric X :=
      h.rloc_source_estimate X ψ φ

/-- Convert source-native CMP116 delta/local-`R` scalar estimates into the Lean
component-estimate record, provided the two source scalars have been identified
with the matching Lean local activities. -/
theorem to_deltaRlocComponentEstimates
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {sourceDelta sourceRloc :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ}
    {deltaE rloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource : ℝ}
    (h :
      CMP116Lemma3DeltaRlocSourceEstimates
        sourceDelta sourceRloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (deltaE_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (deltaE X).globalEval ψ φ = sourceDelta X ψ φ)
    (rloc_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (rloc X).globalEval ψ φ = sourceRloc X ψ φ) :
    CMP116Lemma3DeltaRlocComponentEstimates
      deltaE rloc sourceMetric blockScale
      Cdelta epsilonDelta Cr epsilonR delta kappaSource where
  HdeltaSrc_nonneg := h.HdeltaSrc_nonneg
  HrSrc_nonneg := h.HrSrc_nonneg
  deltaE_estimate :=
    h.to_deltaEActivityEstimate deltaE_identification
  rloc_estimate :=
    h.to_rlocActivityEstimate rloc_identification

end CMP116Lemma3DeltaRlocSourceEstimates

namespace CMP116Lemma3DeltaRlocComponentEstimates

/-- The `deltaE` half of a CMP116 Lemma 3 component pair as a raw-decay
obligation against the native Lemma-3 source weight. -/
theorem deltaE_decay
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {deltaE rloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource : ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource) :
    PhysicalGaugeRawActivityDecay
      deltaE
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) :=
  balabanLemma3_rawActivityDecay h.deltaE_estimate

/-- The local-`R` half of a CMP116 Lemma 3 component pair as a raw-decay
obligation against the native Lemma-3 source weight. -/
theorem rloc_decay
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {deltaE rloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource : ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource) :
    PhysicalGaugeRawActivityDecay
      rloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cr * epsilonR) :=
  balabanLemma3_rawActivityDecay h.rloc_estimate

/-- Assemble the full E/R/B component boundary from the CMP116-native
`deltaE`/local-`R` pair plus a separately supplied `B`/large-field decay.

This is a dictionary-facing adapter only: it proves no component estimate, no
E/R/B decomposition, and no physical activity identification. -/
theorem to_ERBComponentBoundary
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource HbSrc : ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (HbSrc_nonneg :
      0 ≤ HbSrc)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay
        bloc
        (balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetric)
        HbSrc) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) HbSrc where
  HdeltaSrc_nonneg := h.HdeltaSrc_nonneg
  HrSrc_nonneg := h.HrSrc_nonneg
  HbSrc_nonneg := HbSrc_nonneg
  decomposes := decomposes
  deltaE_decay := h.deltaE_decay
  rloc_decay := h.rloc_decay
  bloc_decay := bloc_decay

/-- Assemble the full E/R/B boundary from the CMP116-native `deltaE`/local-`R`
pair and an explicit B/local component boundary.

The B/local input is intentionally separate: its source anchors are CMP119/CMP122,
not CMP116 Lemma 3. -/
theorem to_ERBComponentBoundary_of_blocal
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource HbSrc : ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (hB :
      PhysicalGaugeDimock318BLocalComponentBoundary
        bloc
        (balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetric)
        HbSrc)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) HbSrc :=
  h.to_ERBComponentBoundary
    hB.HbSrc_nonneg
    decomposes
    hB.to_rawActivityDecay

/-- Assemble the E/R/B boundary from the named CMP116/CMP119/CMP122 source-facing
interfaces.

The inputs are still the real source obligations: the CMP116-native
`deltaE`/local-`R` component estimates, a separate CMP119/CMP122 B/local
component boundary, and the CMP119/CMP122 E/R/B decomposition dictionary.  This
theorem only composes those interfaces into the boundary record; it proves no
component estimate, no action-notation dictionary, and no physical activity
identification. -/
theorem to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_blocal
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource HbSrc : ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (hB :
      PhysicalGaugeDimock318BLocalComponentBoundary
        bloc
        (balabanCMP116Lemma3Weight
          blockScale delta kappaSource sourceMetric)
        HbSrc)
    (decomposes :
      CMP119CMP122ERBDecomposition activity deltaE rloc bloc) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) HbSrc :=
  h.to_ERBComponentBoundary_of_blocal
    hB
    (cmp119CMP122ERBDecomposition_decomposes decomposes)

/-- Assemble the E/R/B boundary when the B/local component boundary is proved
against its native source weight, then transported to the CMP116 Lemma-3 source
weight.

This is still only a dictionary-facing adapter: it proves no CMP116 component
estimate, no CMP119 B/local estimate, no E/R/B decomposition, and no
source-to-Lean activity identification.  The weight comparison and B/local
amplitude relaxation remain explicit inputs. -/
theorem to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_blocal_transport
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource HbSrc Hb : ℝ}
    {bWeight : ι → ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (hB :
      PhysicalGaugeDimock318BLocalComponentBoundary
        bloc bWeight HbSrc)
    (HbSrc_le : HbSrc ≤ Hb)
    (bWeight_le_lemma3 :
      ∀ X,
        bWeight X ≤
          balabanCMP116Lemma3Weight
            blockScale delta kappaSource sourceMetric X)
    (decomposes :
      CMP119CMP122ERBDecomposition activity deltaE rloc bloc) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) Hb :=
  h.to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_blocal
    (hB.mono
      HbSrc_le
      bWeight_le_lemma3
      (fun X =>
        balabanCMP116Lemma3Weight_nonneg
          blockScale delta kappaSource sourceMetric X))
    decomposes

/-- Assemble the E/R/B boundary when the B/local component boundary is proved
against the native CMP119 B/local weight, and the metric/rate dictionary
transports that native weight to the CMP116 Lemma-3 source weight.

This is still only source/dictionary composition: it proves no CMP119 B/local
estimate, no CMP116 component estimate, no E/R/B decomposition, and no
source-to-Lean activity identification.  The B/local metric domination and rate
comparison remain explicit frontier inputs. -/
theorem to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_blocal_metricTransport
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource HbSrc Hb kappaB : ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (hB :
      PhysicalGaugeDimock318BLocalComponentBoundary
        bloc (cmp119BLocalWeight kappaB sourceMetricB) HbSrc)
    (HbSrc_le : HbSrc ≤ Hb)
    (sourceMetric_domination :
      ∀ X, (sourceMetric X : ℝ) ≤ sourceMetricB X)
    (rate_margin :
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource ≤ kappaB)
    (lemma3Rate_nonneg :
      0 ≤
        balabanCMP116Lemma3DecayRate
          blockScale delta kappaSource)
    (decomposes :
      CMP119CMP122ERBDecomposition activity deltaE rloc bloc) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) Hb :=
  h.to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_blocal_transport
    hB
    HbSrc_le
    (cmp119BLocalWeight_le_balabanCMP116Lemma3Weight_of_metric_domination_and_rate_margin
      (sourceMetricB := sourceMetricB)
      (sourceMetricLemma := sourceMetric)
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappaB := kappaB)
      sourceMetric_domination
      rate_margin
      lemma3Rate_nonneg)
    decomposes

/-- Assemble the E/R/B boundary from a native B/local component boundary and a
single B/local-to-Lemma-3 weight-transport dictionary.

This is the packaged form of
`to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_blocal_metricTransport`:
the metric/rate transport premises are grouped in
`CMP119BLocalToLemma3WeightTransport`. -/
theorem to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_blocal_weightTransport
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource HbSrc Hb kappaB : ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (hB :
      PhysicalGaugeDimock318BLocalComponentBoundary
        bloc (cmp119BLocalWeight kappaB sourceMetricB) HbSrc)
    (HbSrc_le : HbSrc ≤ Hb)
    (transport :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetric
        blockScale delta kappaSource kappaB)
    (decomposes :
      CMP119CMP122ERBDecomposition activity deltaE rloc bloc) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) Hb :=
  h.to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_blocal_transport
    hB
    HbSrc_le
    (CMP119BLocalToLemma3WeightTransport.weight_domination transport)
    decomposes

/-- Source-shaped B/local estimate route into the E/R/B boundary.

The caller supplies the CMP119 Eq. (2.42)-shaped B/local estimate against its
native exponential weight.  This theorem only packages that estimate into the
B/local boundary and then applies the explicit metric/rate transport above. -/
theorem to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_cmp119BLocalActivityEstimate_metricTransport
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource HbSrc Hb kappaB : ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (HbSrc_nonneg : 0 ≤ HbSrc)
    (hB :
      CMP119BLocalActivityEstimate
        bloc sourceMetricB HbSrc kappaB)
    (HbSrc_le : HbSrc ≤ Hb)
    (sourceMetric_domination :
      ∀ X, (sourceMetric X : ℝ) ≤ sourceMetricB X)
    (rate_margin :
      balabanCMP116Lemma3DecayRate
        blockScale delta kappaSource ≤ kappaB)
    (lemma3Rate_nonneg :
      0 ≤
        balabanCMP116Lemma3DecayRate
          blockScale delta kappaSource)
    (decomposes :
      CMP119CMP122ERBDecomposition activity deltaE rloc bloc) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) Hb :=
  h.to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_blocal_metricTransport
    (PhysicalGaugeDimock318BLocalComponentBoundary.of_cmp119BLocalActivityEstimate
      HbSrc_nonneg hB)
    HbSrc_le
    sourceMetric_domination
    rate_margin
    lemma3Rate_nonneg
    decomposes

/-- Source-shaped B/local estimate route into the E/R/B boundary using a
single B/local-to-Lemma-3 weight-transport dictionary.

The component estimate remains an explicit source obligation; the transport
dictionary only packages the metric/rate comparison needed to reuse it at the
CMP116 Lemma-3 source weight. -/
theorem to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_cmp119BLocalActivityEstimate_weightTransport
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource HbSrc Hb kappaB : ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (HbSrc_nonneg : 0 ≤ HbSrc)
    (hB :
      CMP119BLocalActivityEstimate
        bloc sourceMetricB HbSrc kappaB)
    (HbSrc_le : HbSrc ≤ Hb)
    (transport :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetric
        blockScale delta kappaSource kappaB)
    (decomposes :
      CMP119CMP122ERBDecomposition activity deltaE rloc bloc) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) Hb :=
  h.to_ERBComponentBoundary_of_cmp119CMP122Decomposition_and_blocal_weightTransport
    (PhysicalGaugeDimock318BLocalComponentBoundary.of_cmp119BLocalActivityEstimate
      HbSrc_nonneg hB)
    HbSrc_le
    transport
    decomposes

/-- Source-facing E/R/B boundary route from named CMP116 and CMP119/CMP122
inputs.

This theorem removes the raw component-decay premises from the component
boundary constructor by using the supplied CMP116 delta/local-R component
estimate package and the supplied CMP119 B/local source-bound package.  It still
proves no CMP119 Eq. (2.42), no CMP119/CMP122 source decomposition, no
source-to-Lean activity identification, no B/local metric/rate dictionary, and
no total raw decay. -/
theorem to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_weightTransport
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {sourceEval sourceDelta sourceRloc sourceBloc :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ}
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource HbSrc Hb kappaB : ℝ}
    (h :
      CMP116Lemma3DeltaRlocComponentEstimates
        deltaE rloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (hsource :
      CMP119CMP122ERBSourceDecomposition
        sourceEval sourceDelta sourceRloc sourceBloc)
    (activity_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ = sourceEval X ψ φ)
    (deltaE_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (deltaE X).globalEval ψ φ = sourceDelta X ψ φ)
    (rloc_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (rloc X).globalEval ψ φ = sourceRloc X ψ φ)
    (bloc_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (bloc X).globalEval ψ φ = sourceBloc X ψ φ)
    (hB :
      CMP119BLocalSourceBound
        sourceBloc sourceMetricB HbSrc kappaB)
    (HbSrc_nonneg : 0 ≤ HbSrc)
    (HbSrc_le : HbSrc ≤ Hb)
    (transport :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetric
        blockScale delta kappaSource kappaB) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) Hb :=
  PhysicalGaugeDimock318ERBComponentBoundary.of_cmp119CMP122ERBSourceDecomposition_componentDecays
    h.HdeltaSrc_nonneg
    h.HrSrc_nonneg
    (le_trans HbSrc_nonneg HbSrc_le)
    hsource
    activity_identification
    deltaE_identification
    rloc_identification
    bloc_identification
    h.deltaE_decay
    h.rloc_decay
    (hB.to_rawActivityDecay_lemma3WeightTransport
      HbSrc_nonneg
      bloc_identification
      HbSrc_le
      transport)

end CMP116Lemma3DeltaRlocComponentEstimates

namespace CMP116Lemma3DeltaRlocSourceEstimates

/-- Fully source-native E/R/B boundary route from named CMP116 and CMP119/CMP122
inputs.

Compared with
`CMP116Lemma3DeltaRlocComponentEstimates.to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_weightTransport`,
this theorem does not require the caller to prepackage the CMP116 delta/local-`R`
source estimates as Lean component estimates.  It only composes the supplied
CMP116 source estimates, the supplied CMP119/CMP122 source decomposition, all
four source-to-Lean activity identifications, the supplied B/local source bound,
the source-amplitude comparison, and the B/local metric/rate transport
dictionary.  It proves none of those source facts, identifications, estimates,
or transport fields. -/
theorem to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_weightTransport
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {sourceEval sourceDelta sourceRloc sourceBloc :
      ι → PhysicalGaugeField dPhys N Nc → PhysicalGaugeField dPhys N Nc → ℂ}
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {sourceMetricB : ι → ℝ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR delta kappaSource HbSrc Hb kappaB : ℝ}
    (h :
      CMP116Lemma3DeltaRlocSourceEstimates
        sourceDelta sourceRloc sourceMetric blockScale
        Cdelta epsilonDelta Cr epsilonR delta kappaSource)
    (hsource :
      CMP119CMP122ERBSourceDecomposition
        sourceEval sourceDelta sourceRloc sourceBloc)
    (activity_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ = sourceEval X ψ φ)
    (deltaE_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (deltaE X).globalEval ψ φ = sourceDelta X ψ φ)
    (rloc_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (rloc X).globalEval ψ φ = sourceRloc X ψ φ)
    (bloc_identification :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (bloc X).globalEval ψ φ = sourceBloc X ψ φ)
    (hB :
      CMP119BLocalSourceBound
        sourceBloc sourceMetricB HbSrc kappaB)
    (HbSrc_nonneg : 0 ≤ HbSrc)
    (HbSrc_le : HbSrc ≤ Hb)
    (transport :
      CMP119BLocalToLemma3WeightTransport
        sourceMetricB sourceMetric
        blockScale delta kappaSource kappaB) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) Hb :=
  (h.to_deltaRlocComponentEstimates
    deltaE_identification
    rloc_identification).to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_weightTransport
      hsource
      activity_identification
      deltaE_identification
      rloc_identification
      bloc_identification
      hB
      HbSrc_nonneg
      HbSrc_le
      transport

end CMP116Lemma3DeltaRlocSourceEstimates

/-- Build the flexible Dimock E/R/B certificate directly from three CMP116
Lemma 3 component estimates.

This keeps the source theorem at the CMP116 Lemma 3 boundary: each component
estimate is stated in the native Lemma 3 source metric, while the shared
exponential weight nonnegativity and conversion to `PhysicalGaugeRawActivityDecay`
are discharged here. -/
theorem PhysicalGaugeDimock318FlexibleBudgetCertificate.of_cmp116Lemma3ComponentEstimates
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR Cb epsilonB delta kappaSource H0 : ℝ}
    (component_budget :
      (Cdelta * epsilonDelta) + (Cr * epsilonR) +
        (Cb * epsilonB) ≤ H0)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (deltaE_estimate :
      CMP116Lemma3ActivityEstimate
        deltaE sourceMetric blockScale
        Cdelta epsilonDelta delta kappaSource)
    (rloc_estimate :
      CMP116Lemma3ActivityEstimate
        rloc sourceMetric blockScale
        Cr epsilonR delta kappaSource)
    (bloc_estimate :
      CMP116Lemma3ActivityEstimate
        bloc sourceMetric blockScale
        Cb epsilonB delta kappaSource) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) (Cb * epsilonB) H0 := by
  exact
    PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays
      (balabanCMP116Lemma3Weight_nonneg
        blockScale delta kappaSource sourceMetric)
      component_budget
      decomposes
      (balabanLemma3_rawActivityDecay deltaE_estimate)
      (balabanLemma3_rawActivityDecay rloc_estimate)
      (balabanLemma3_rawActivityDecay bloc_estimate)

/-- Build the source-facing E/R/B component boundary from three native CMP116
Lemma 3 component estimates.

This is intentionally before any downstream budget or Appendix-F weight
transport: it exposes the exact boundary fields that still need source
construction, namely the E/R/B decomposition and the three component estimates
against the native Lemma-3 source weight.  It proves no component estimate and
does not identify the physical activity with the source activity. -/
theorem PhysicalGaugeDimock318ERBComponentBoundary.of_cmp116Lemma3ComponentEstimates
    {ι : Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : ι → ℕ}
    {blockScale : ℕ}
    {Cdelta epsilonDelta Cr epsilonR Cb epsilonB delta kappaSource : ℝ}
    (HdeltaSrc_nonneg :
      0 ≤ Cdelta * epsilonDelta)
    (HrSrc_nonneg :
      0 ≤ Cr * epsilonR)
    (HbSrc_nonneg :
      0 ≤ Cb * epsilonB)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (deltaE_estimate :
      CMP116Lemma3ActivityEstimate
        deltaE sourceMetric blockScale
        Cdelta epsilonDelta delta kappaSource)
    (rloc_estimate :
      CMP116Lemma3ActivityEstimate
        rloc sourceMetric blockScale
        Cr epsilonR delta kappaSource)
    (bloc_estimate :
      CMP116Lemma3ActivityEstimate
        bloc sourceMetric blockScale
        Cb epsilonB delta kappaSource) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc
      (balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric)
      (Cdelta * epsilonDelta) (Cr * epsilonR) (Cb * epsilonB) where
  HdeltaSrc_nonneg := HdeltaSrc_nonneg
  HrSrc_nonneg := HrSrc_nonneg
  HbSrc_nonneg := HbSrc_nonneg
  decomposes := decomposes
  deltaE_decay := balabanLemma3_rawActivityDecay deltaE_estimate
  rloc_decay := balabanLemma3_rawActivityDecay rloc_estimate
  bloc_decay := balabanLemma3_rawActivityDecay bloc_estimate

/-- Compatibility wrapper for the prior real-valued source metric interface.

The canonical Lemma 3 estimate above uses `balabanCMP116Lemma3Weight` with a
natural-valued source metric. -/
noncomputable def cmp116Lemma3Weight
    {ι : Type*}
    (dNext : ι → ℝ)
    (δ blockScale κ : ℝ)
    (Z : ι) : ℝ :=
  Real.exp
    (-((1 - 8 * δ) * (1 / 2 : ℝ) *
      blockScale * κ * dNext Z))

/-- The compatibility real-metric CMP116 Lemma 3 weight is nonnegative. -/
theorem cmp116Lemma3Weight_nonneg
    {ι : Type*}
    (dNext : ι → ℝ)
    (δ blockScale κ : ℝ)
    (Z : ι) :
    0 ≤ cmp116Lemma3Weight dNext δ blockScale κ Z :=
  Real.exp_nonneg _

end YangMills.RG

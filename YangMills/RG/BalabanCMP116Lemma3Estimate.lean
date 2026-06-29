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

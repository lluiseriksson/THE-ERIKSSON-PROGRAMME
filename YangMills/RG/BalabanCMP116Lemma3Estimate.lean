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

end CMP116Lemma3DeltaRlocComponentEstimates

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

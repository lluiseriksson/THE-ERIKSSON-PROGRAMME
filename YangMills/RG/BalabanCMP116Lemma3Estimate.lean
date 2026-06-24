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

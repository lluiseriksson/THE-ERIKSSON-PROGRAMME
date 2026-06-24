/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma3ScaleFamily

/-!
# CMP116 Lemma 3 admissible-domain adapter

This module records the source-boundary transport from CMP116's native
admissible-domain index type to a larger repository index type.

Honest scope: the adapter proves no admissibility theorem, no outside-domain
vanishing theorem, and no metric comparison.  It only packages the consequence
of supplying those facts explicitly.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

variable {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]

/-- Extend an admissible-subtype CMP116 source metric to the full index type.

Outside the admissible subtype this assigns `0`; the activity estimate theorem
below only uses this branch together with an explicit outside-domain zero
statement. -/
def cmp116AdmissibleMetricZeroExtension
    {ι : Type*}
    (admissible : ι → Prop)
    [DecidablePred admissible]
    (sourceMetric : {X : ι // admissible X} → ℕ) :
    ι → ℕ :=
  fun X =>
    if hX : admissible X then
      sourceMetric ⟨X, hX⟩
    else
      0

/-- Extend a CMP116 Lemma-3 activity estimate from the admissible source
subtype to the full repository index type by explicit zero extension.

The theorem does not assert that non-admissible activities vanish; that is the
`outside_zero` hypothesis. -/
theorem cmp116Lemma3ActivityEstimate_of_admissible_zeroExtension
    {ι : Type*}
    {admissible : ι → Prop}
    [DecidablePred admissible]
    {physicalActivity :
      ι → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric : {X : ι // admissible X} → ℕ}
    {blockScale : ℕ}
    {C3 epsilon1 delta kappaSource : ℝ}
    (hsource :
      CMP116Lemma3ActivityEstimate
        (fun X : {X : ι // admissible X} =>
          physicalActivity X.1)
        sourceMetric
        blockScale C3 epsilon1 delta kappaSource)
    (outside_zero :
      ∀ X, ¬ admissible X →
        ∀ ψ φ,
          (physicalActivity X).globalEval ψ φ = 0)
    (hamplitude_nonneg : 0 ≤ C3 * epsilon1) :
    CMP116Lemma3ActivityEstimate
      physicalActivity
      (cmp116AdmissibleMetricZeroExtension admissible sourceMetric)
      blockScale C3 epsilon1 delta kappaSource := by
  intro X ψ φ
  by_cases hX : admissible X
  · simpa [balabanCMP116Lemma3Weight,
      cmp116AdmissibleMetricZeroExtension, hX] using
      hsource ⟨X, hX⟩ ψ φ
  · rw [outside_zero X hX ψ φ, norm_zero]
    exact
      mul_nonneg hamplitude_nonneg
        (balabanCMP116Lemma3Weight_nonneg
          blockScale delta kappaSource
          (cmp116AdmissibleMetricZeroExtension admissible sourceMetric)
          X)

/-- Scale-family version of a native CMP116 Lemma-3 estimate on admissible
source domains. -/
def CMP116Lemma3AdmissibleActivityEstimateScaleFamily
    {ι : ℕ → ℕ → Type*}
    (admissible : ∀ t k, ι t k → Prop)
    [∀ t k, DecidablePred (admissible t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (physicalActivity :
      ∀ t k, ι t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, {X : ι t k // admissible t k X} → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ) : Prop :=
  ∀ t k,
    CMP116Lemma3ActivityEstimate
      (fun X : {X : ι t k // admissible t k X} =>
        physicalActivity t k X.1)
      (sourceMetric t k)
      (blockScale t k)
      (C3 t k)
      (epsilon1 t k)
      (delta t k)
      (kappaSource t k)

/-- Per-scale admissible metric extension. -/
def cmp116AdmissibleMetricScaleExtension
    {ι : ℕ → ℕ → Type*}
    (admissible : ∀ t k, ι t k → Prop)
    [∀ t k, DecidablePred (admissible t k)]
    (sourceMetric :
      ∀ t k, {X : ι t k // admissible t k X} → ℕ) :
    ∀ t k, ι t k → ℕ :=
  fun t k =>
    cmp116AdmissibleMetricZeroExtension
      (admissible t k) (sourceMetric t k)

/-- Extend a CMP116 Lemma-3 scale family from admissible source domains to the
full repository index type by explicit zero extension at every scale. -/
theorem cmp116Lemma3ActivityEstimateScaleFamily_of_admissible_zeroExtension
    {ι : ℕ → ℕ → Type*}
    {admissible : ∀ t k, ι t k → Prop}
    [∀ t k, DecidablePred (admissible t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {physicalActivity :
      ∀ t k, ι t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {sourceMetric :
      ∀ t k, {X : ι t k // admissible t k X} → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ}
    (hsource :
      CMP116Lemma3AdmissibleActivityEstimateScaleFamily
        admissible physicalActivity sourceMetric
        blockScale C3 epsilon1 delta kappaSource)
    (outside_zero :
      ∀ t k X, ¬ admissible t k X →
        ∀ ψ φ,
          (physicalActivity t k X).globalEval ψ φ = 0)
    (hamplitude_nonneg :
      ∀ t k, 0 ≤ C3 t k * epsilon1 t k) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      (cmp116AdmissibleMetricScaleExtension admissible sourceMetric)
      blockScale C3 epsilon1 delta kappaSource := by
  intro t k
  exact
    cmp116Lemma3ActivityEstimate_of_admissible_zeroExtension
      (admissible := admissible t k)
      (physicalActivity := physicalActivity t k)
      (sourceMetric := sourceMetric t k)
      (blockScale := blockScale t k)
      (C3 := C3 t k)
      (epsilon1 := epsilon1 t k)
      (delta := delta t k)
      (kappaSource := kappaSource t k)
      (hsource t k)
      (outside_zero t k)
      (hamplitude_nonneg t k)

/-- Dominate the zero-extended CMP116 Lemma-3 admissible source weight by the
Appendix-F shifted metric weight on a target finite family.

Both admissibility of the target family and the complete exponent comparison
remain explicit hypotheses. -/
theorem balabanCMP116Lemma3Weight_domination_of_admissible_metricComparison
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    (Λ : Finset (OmegaPolymerType HF z))
    {admissible : OmegaPolymerType HF z → Prop}
    [DecidablePred admissible]
    {sourceMetric : {X : OmegaPolymerType HF z // admissible X} → ℕ}
    {blockScale : ℕ}
    {delta kappaSource kappa : ℝ}
    (target_admissible :
      ∀ X, X ∈ Λ → admissible X)
    (metric_comparison :
      ∀ X (hXΛ : X ∈ Λ),
        kappa *
            (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          balabanCMP116Lemma3DecayRate
              blockScale delta kappaSource *
            (sourceMetric ⟨X, target_admissible X hXΛ⟩ : ℝ)) :
    ∀ X, X ∈ Λ →
      balabanCMP116Lemma3Weight
          blockScale delta kappaSource
          (cmp116AdmissibleMetricZeroExtension admissible sourceMetric)
          X ≤
        appendixFHoleExpWeight HF kappa X.val := by
  intro X hXΛ
  exact
    balabanCMP116Lemma3Weight_domination
      Λ
      (sourceMetric :=
        cmp116AdmissibleMetricZeroExtension admissible sourceMetric)
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappa := kappa)
      (fun Y hYΛ => by
        have hYadm : admissible Y := target_admissible Y hYΛ
        simpa [cmp116AdmissibleMetricZeroExtension, hYadm] using
          metric_comparison Y hYΛ)
      X hXΛ

end YangMills.RG

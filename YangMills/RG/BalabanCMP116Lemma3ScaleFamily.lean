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

/-- Generate the Lemma-3 source-metric domination from a source spanning set.

This is the geometric dictionary part of the Lemma-3/App-F bridge: when the
source metric is the cardinality of a connected set covering the active
skeleton of `X`, the shifted modified metric `d_M(X)+1` is automatically
bounded by that source metric. -/
theorem cmp116Lemma3SourceMetric_domination_of_spanning_sets
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X)) :
  ∀ t k X, X ∈ Λ t k →
      (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
        ((spanningSet t k X).card : ℝ) := by
  intro t k X hX
  exact_mod_cast
    (discreteModifiedMetric_add_one_le_card_of_spanning_set
      HF X.val (spanningSet t k X)
      X.property.right.right.right
      (hskel t k X hX)
      (hsub t k X hX)
      (hconn t k X hX))

/-- Source-metric domination from a spanning-set dictionary and a cardinality
comparison into the actual Lemma-3 source metric.

This is the form usually needed by the source records: the source may use a
metric coarser than the spanning-cardinality itself, so the remaining
dictionary obligation is just `|S_X| <= sourceMetric X`. -/
theorem cmp116Lemma3SourceMetric_domination_of_spanning_sets_le_sourceMetric
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (hcard_le :
      ∀ t k X, X ∈ Λ t k →
        ((spanningSet t k X).card : ℝ) ≤ (sourceMetric t k X : ℝ)) :
  ∀ t k X, X ∈ Λ t k →
      (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
        (sourceMetric t k X : ℝ) := by
  intro t k X hX
  exact
    (cmp116Lemma3SourceMetric_domination_of_spanning_sets
      Λ spanningSet hskel hsub hconn t k X hX).trans
      (hcard_le t k X hX)

/-- The self-spanning convention for the Lemma-3 active-family route.

This is the canonical low-risk dictionary choice `spanningSet t k X = X.val`.
It closes only the geometric spanning-set fields; the cardinality comparison
`X.val.card <= sourceMetric t k X` remains a separate source-metric obligation. -/
def cmp116Lemma3SelfSpanningSet
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ} :
    ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L) :=
  fun _ _ X => X.val

/-- Self-spanning skeleton coverage: `skeleton HF X.val` is contained in
`spanningSet t k X := X.val`. -/
theorem cmp116Lemma3SelfSpanningSet_skeleton_subset
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))) :
    ∀ t k X, X ∈ Λ t k →
      skeleton HF X.val ⊆
        cmp116Lemma3SelfSpanningSet (HF := HF) (z := z) t k X := by
  intro _ _ X _
  exact skeleton_subset HF X.val

/-- Self-spanning containment: `spanningSet t k X := X.val` is contained in
the active polymer support. -/
theorem cmp116Lemma3SelfSpanningSet_subset
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))) :
    ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3SelfSpanningSet (HF := HF) (z := z) t k X ⊆ X.val := by
  intro _ _ _ _ y hy
  exact hy

/-- Self-spanning connectedness: the chosen spanning set inherits
`cubeConnected` from the `OmegaPolymerType` structure. -/
theorem cmp116Lemma3SelfSpanningSet_cubeConnected
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))) :
    ∀ t k X, X ∈ Λ t k →
      cubeConnected
        (cmp116Lemma3SelfSpanningSet (HF := HF) (z := z) t k X) := by
  intro _ _ X _
  exact X.property.right.left

/-- Canonical source metric for the self-spanning Lemma-3 convention.

It uses the cardinality of the whole active polymer support.  This is a
dictionary-normalized route only; it does not identify the paper's physical
source metric when that metric is specified independently. -/
def cmp116Lemma3SelfCardSourceMetric
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ} :
    ∀ t k, OmegaPolymerType HF (z t k) → ℕ :=
  fun _ _ X => X.val.card

/-- The self-cardinality source metric closes the self-spanning
`card_le_sourceMetric` input by reflexivity. -/
theorem cmp116Lemma3SelfCardSourceMetric_card_le
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))) :
    ∀ t k X, X ∈ Λ t k →
      ((X.val.card : ℝ) ≤
        (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z) t k X : ℝ)) := by
  intro _ _ _ _
  exact le_rfl

/-- Source-metric domination for the concrete convention `spanningSet t k X = X.val`.

This closes the spanning-set coverage, containment, and connectedness fields
from the `OmegaPolymerType` structure itself.  The remaining dictionary
obligation is only the cardinality comparison into the chosen source metric. -/
theorem cmp116Lemma3SourceMetric_domination_of_self_le_sourceMetric
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((X.val.card : ℝ) ≤ (sourceMetric t k X : ℝ))) :
  ∀ t k X, X ∈ Λ t k →
      (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
        (sourceMetric t k X : ℝ) := by
  exact
    cmp116Lemma3SourceMetric_domination_of_spanning_sets_le_sourceMetric
      Λ
      (sourceMetric := sourceMetric)
      (cmp116Lemma3SelfSpanningSet (HF := HF) (z := z))
      (cmp116Lemma3SelfSpanningSet_skeleton_subset Λ)
      (cmp116Lemma3SelfSpanningSet_subset Λ)
      (cmp116Lemma3SelfSpanningSet_cubeConnected Λ)
      card_le_sourceMetric

/-- Source-metric domination for the canonical self-cardinality source metric.

This is the theorem-fed cardinality route for `sourceMetric t k X = X.val.card`.
It does not discharge the comparison into an independently specified coarser
source metric. -/
theorem cmp116Lemma3SourceMetric_domination_of_selfCardSourceMetric
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k))) :
  ∀ t k X, X ∈ Λ t k →
      (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
        (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z) t k X : ℝ) := by
  exact
    cmp116Lemma3SourceMetric_domination_of_self_le_sourceMetric
      Λ
      (sourceMetric := cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
      (cmp116Lemma3SelfCardSourceMetric_card_le Λ)

/-- Scale-family form of the CMP116 Lemma 3/App-F weight bridge.

It replaces the per-scale `weight_domination` obligation by two source-facing
checks: the shifted modified metric is bounded by the Lemma-3 source metric on
the active family, and the target Appendix-F rate is below the Lemma-3 decay
rate.  It still proves no activity estimate or source theorem. -/
theorem cmp116Lemma3ScaleWeight_domination_of_sourceMetric_domination_and_rate_margin
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        kappa ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val := by
  intro t k
  simpa [cmp116Lemma3ScaleWeight] using
    (balabanCMP116Lemma3Weight_domination_of_sourceMetric_domination_and_rate_margin
      (Λ t k)
      (sourceMetric := sourceMetric t k)
      (blockScale := blockScale t k)
      (delta := delta t k)
      (kappaSource := kappaSource t k)
      (kappa := kappa)
      (sourceMetric_domination t k)
      (rate_margin t k)
      kappa_nonneg)

/-- Spanning-set/rate-margin route to the Appendix-F weight-domination field.

This is the capstone for the geometric/rate bookkeeping path: a connected
spanning set covering the active skeleton supplies the Lemma-3 source metric,
and the scalar rate margin transports that source weight to the shifted
Appendix-F weight.  No component activity estimate is proved here. -/
theorem cmp116Lemma3ScaleWeight_domination_of_spanning_sets_and_rate_margin
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (rate_margin :
      ∀ t k,
        kappa ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          (fun t k X => (spanningSet t k X).card)
          blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_sourceMetric_domination_and_rate_margin
    Λ
    (sourceMetric := fun t k X => (spanningSet t k X).card)
    (cmp116Lemma3SourceMetric_domination_of_spanning_sets
      Λ spanningSet hskel hsub hconn)
    rate_margin
    kappa_nonneg

/-- Spanning-set/rate-margin route for a coarser source metric.

The source theorem may use a metric larger than the minimal connected
spanning-cardinality metric.  In that case it is enough to provide the
cardinality comparison into the source metric; the rest of the Appendix-F
weight-domination field is still discharged by the existing geometric and
rate-margin bridge. -/
theorem cmp116Lemma3ScaleWeight_domination_of_spanning_sets_le_sourceMetric_and_rate_margin
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((spanningSet t k X).card : ℝ) ≤ (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        kappa ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_sourceMetric_domination_and_rate_margin
    Λ
    (sourceMetric := sourceMetric)
    (cmp116Lemma3SourceMetric_domination_of_spanning_sets_le_sourceMetric
      Λ spanningSet hskel hsub hconn card_le_sourceMetric)
    rate_margin
    kappa_nonneg

/-- Lemma-3/App-F weight domination for the concrete self-spanning convention.

When the whole active polymer is used as the connected spanning set, the source
record no longer needs separate `spanningSet`, skeleton-cover, containment, or
connectedness fields.  The remaining geometric dictionary input is the
cardinality comparison `X.val.card <= sourceMetric t k X`, plus the scalar
rate margin. -/
theorem cmp116Lemma3ScaleWeight_domination_of_self_le_sourceMetric_and_rate_margin
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((X.val.card : ℝ) ≤ (sourceMetric t k X : ℝ)))
    (rate_margin :
      ∀ t k,
        kappa ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_sourceMetric_domination_and_rate_margin
    Λ
    (sourceMetric := sourceMetric)
    (cmp116Lemma3SourceMetric_domination_of_self_le_sourceMetric
      Λ card_le_sourceMetric)
    rate_margin
    kappa_nonneg

/-- Lemma-3/App-F weight domination for the canonical self-cardinality source
metric.

This removes the `card_le_sourceMetric` argument only for the definitionally
chosen metric `sourceMetric t k X = X.val.card`.  It proves no comparison into
an independently specified source metric. -/
theorem cmp116Lemma3ScaleWeight_domination_of_selfCardSourceMetric_and_rate_margin
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (rate_margin :
      ∀ t k,
        kappa ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
          blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_self_le_sourceMetric_and_rate_margin
    Λ
    (sourceMetric := cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    (cmp116Lemma3SelfCardSourceMetric_card_le Λ)
    rate_margin
    kappa_nonneg

/-- Scale-family rate-margin generator from the source-rate comparison and
the dimensionless Lemma-3 decay reserve.

This turns the abstract `rate_margin` argument used by the weight-domination
bridges into two smaller scalar checks at each scale: the Appendix-F target
rate is at most the native Lemma-3 source rate, and the factor
`((1 - 8*delta)/2) * blockScale` is at least one. -/
theorem cmp116Lemma3Scale_rate_margin_of_sourceRate_le_and_decayFactor
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k)) :
    ∀ t k,
      kappa ≤
        balabanCMP116Lemma3DecayRate
          (blockScale t k) (delta t k) (kappaSource t k) := by
  intro t k
  exact
    balabanCMP116Lemma3_rate_margin_of_sourceRate_le_and_decayFactor
      (target_le_source t k)
      (kappaSource_nonneg t k)
      (decayFactor_reserve t k)

/-- Scale-family form of the small-delta/large-block sufficient condition for
the Lemma-3 dimensionless decay reserve.

This replaces the packaged reserve
`1 <= balabanCMP116Lemma3DecayFactor (blockScale t k) (delta t k)` by two
primitive scalar checks at each scale.  It proves no source constant hierarchy:
the caller still has to provide `delta <= 1/16` and `4 <= blockScale` from a
source-faithful record. -/
theorem cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
    {blockScale : ℕ → ℕ → ℕ}
    {delta : ℕ → ℕ → ℝ}
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k) :
    ∀ t k,
      1 ≤
        balabanCMP116Lemma3DecayFactor
          (blockScale t k) (delta t k) := by
  intro t k
  exact
    balabanCMP116Lemma3DecayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (delta_le_one_sixteen t k)
      (four_le_blockScale t k)

/-- Constant source-rate convention for the Lemma-3 scale-family bridges.

This is a dictionary-normalized route only: the native Lemma-3 source rate is
chosen definitionally equal to the Appendix-F target rate at every scale.  It
does not identify a paper source constant hierarchy. -/
def cmp116Lemma3ConstantSourceRate (kappa : ℝ) : ℕ → ℕ → ℝ :=
  fun _ _ => kappa

/-- The constant source-rate convention closes `target_le_source` by
reflexivity. -/
theorem cmp116Lemma3ConstantSourceRate_target_le (kappa : ℝ) :
    ∀ t k, kappa ≤ cmp116Lemma3ConstantSourceRate kappa t k := by
  intro _ _
  exact le_rfl

/-- The constant source-rate convention transports target-rate
nonnegativity to source-rate nonnegativity. -/
theorem cmp116Lemma3ConstantSourceRate_nonneg
    {kappa : ℝ} (kappa_nonneg : 0 ≤ kappa) :
    ∀ t k, 0 ≤ cmp116Lemma3ConstantSourceRate kappa t k := by
  intro _ _
  exact kappa_nonneg

/-- Spanning-set route with the rate margin generated from source-rate and
decay-factor reserves.

This is the larger Lemma-3 bookkeeping capstone: the caller supplies the
source spanning-set dictionary, the source-metric cardinality comparison, the
Appendix-F/source-rate comparison, nonnegativity of the Lemma-3 source rate, and
the dimensionless decay-factor reserve.  The abstract `rate_margin` field is
then generated internally. -/
theorem cmp116Lemma3ScaleWeight_domination_of_spanning_sets_le_sourceMetric_and_sourceRate_le_and_decayFactor
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((spanningSet t k X).card : ℝ) ≤ (sourceMetric t k X : ℝ))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_spanning_sets_le_sourceMetric_and_rate_margin
    Λ
    (sourceMetric := sourceMetric)
    spanningSet
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    hskel
    hsub
    hconn
    card_le_sourceMetric
    (cmp116Lemma3Scale_rate_margin_of_sourceRate_le_and_decayFactor
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappa := kappa)
      target_le_source
      kappaSource_nonneg
      decayFactor_reserve)
    kappa_nonneg

/-- Self-spanning route with the rate margin generated from source-rate and
decay-factor reserves.

For the convention `spanningSet t k X = X.val`, the polymer structure already
supplies the geometric fields.  This fully reduced capstone leaves only the
source-metric cardinality comparison, the source-rate comparison, nonnegativity
of the Lemma-3 source rate, the decay-factor reserve, and the target-rate
nonnegativity. -/
theorem cmp116Lemma3ScaleWeight_domination_of_self_le_sourceMetric_and_sourceRate_le_and_decayFactor
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((X.val.card : ℝ) ≤ (sourceMetric t k X : ℝ)))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_self_le_sourceMetric_and_rate_margin
    Λ
    (sourceMetric := sourceMetric)
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    card_le_sourceMetric
    (cmp116Lemma3Scale_rate_margin_of_sourceRate_le_and_decayFactor
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappa := kappa)
      target_le_source
      kappaSource_nonneg
      decayFactor_reserve)
    kappa_nonneg

/-- Canonical self-cardinality source-metric capstone with source-rate and
decay-factor reserves.

This is the self-spanning route with `sourceMetric t k X = X.val.card`, so the
cardinality comparison is definitionally closed.  The scalar source-rate and
decay-factor reserves remain explicit. -/
theorem cmp116Lemma3ScaleWeight_domination_of_selfCardSourceMetric_and_sourceRate_le_and_decayFactor
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
          blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_self_le_sourceMetric_and_sourceRate_le_and_decayFactor
    Λ
    (sourceMetric := cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    (cmp116Lemma3SelfCardSourceMetric_card_le Λ)
    target_le_source
    kappaSource_nonneg
    decayFactor_reserve
    kappa_nonneg

/-- Canonical self-cardinality route with constant source rate.

This closes the source-rate comparison by the definitional convention
`kappaSource t k = kappa`.  The decay-factor reserve remains an explicit scalar
input; no paper constant hierarchy is proved. -/
theorem cmp116Lemma3ScaleWeight_domination_of_selfCardSourceMetric_and_constantSourceRate_decayFactor
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {blockScale : ℕ → ℕ → ℕ}
    {delta : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
          blockScale delta (cmp116Lemma3ConstantSourceRate kappa) t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_selfCardSourceMetric_and_sourceRate_le_and_decayFactor
    Λ
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := cmp116Lemma3ConstantSourceRate kappa)
    (kappa := kappa)
    (cmp116Lemma3ConstantSourceRate_target_le kappa)
    (cmp116Lemma3ConstantSourceRate_nonneg kappa_nonneg)
    decayFactor_reserve
    kappa_nonneg

/-- Spanning-set route with the Lemma-3 decay reserve generated from primitive
small-delta and large-block hypotheses.

This removes the abstract `decayFactor_reserve` field from callers while keeping
the actual source-facing scalar obligations explicit: `delta <= 1/16` and
`4 <= blockScale` at every active scale. -/
theorem cmp116Lemma3ScaleWeight_domination_of_spanning_sets_le_sourceMetric_and_sourceRate_le_and_delta_bounds
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((spanningSet t k X).card : ℝ) ≤ (sourceMetric t k X : ℝ))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_spanning_sets_le_sourceMetric_and_sourceRate_le_and_decayFactor
    Λ
    (sourceMetric := sourceMetric)
    spanningSet
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    hskel
    hsub
    hconn
    card_le_sourceMetric
    target_le_source
    kappaSource_nonneg
    (cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (blockScale := blockScale)
      (delta := delta)
      delta_le_one_sixteen
      four_le_blockScale)
    kappa_nonneg

/-- Self-spanning route with the Lemma-3 decay reserve generated from primitive
small-delta and large-block hypotheses. -/
theorem cmp116Lemma3ScaleWeight_domination_of_self_le_sourceMetric_and_sourceRate_le_and_delta_bounds
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((X.val.card : ℝ) ≤ (sourceMetric t k X : ℝ)))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_self_le_sourceMetric_and_sourceRate_le_and_decayFactor
    Λ
    (sourceMetric := sourceMetric)
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    card_le_sourceMetric
    target_le_source
    kappaSource_nonneg
    (cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (blockScale := blockScale)
      (delta := delta)
      delta_le_one_sixteen
      four_le_blockScale)
    kappa_nonneg

/-- Canonical self-cardinality source-metric capstone with primitive
small-delta and large-block scalar hypotheses. -/
theorem cmp116Lemma3ScaleWeight_domination_of_selfCardSourceMetric_and_sourceRate_le_and_delta_bounds
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
          blockScale delta kappaSource t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_selfCardSourceMetric_and_sourceRate_le_and_decayFactor
    Λ
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    target_le_source
    kappaSource_nonneg
    (cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (blockScale := blockScale)
      (delta := delta)
      delta_le_one_sixteen
      four_le_blockScale)
    kappa_nonneg

/-- Canonical self-cardinality route with constant source rate and primitive
small-delta/large-block scalar hypotheses. -/
theorem cmp116Lemma3ScaleWeight_domination_of_selfCardSourceMetric_and_constantSourceRate_delta_bounds
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {blockScale : ℕ → ℕ → ℕ}
    {delta : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa) :
  ∀ t k X, X ∈ Λ t k →
      cmp116Lemma3ScaleWeight
          (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
          blockScale delta (cmp116Lemma3ConstantSourceRate kappa) t k X ≤
        appendixFHoleExpWeight HF kappa X.val :=
  cmp116Lemma3ScaleWeight_domination_of_selfCardSourceMetric_and_constantSourceRate_decayFactor
    Λ
    (blockScale := blockScale)
    (delta := delta)
    (kappa := kappa)
    (cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (blockScale := blockScale)
      (delta := delta)
      delta_le_one_sixteen
      four_le_blockScale)
    kappa_nonneg

/-- Spanning-set Lemma-3/App-F weight domination over the active subtype.

The capstone is membership-restricted on `X ∈ Λ t k`; this form packages that
restriction as an unrestricted pointwise domination over the subtype used by
source-facing E/R/B component boundaries. -/
theorem cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_spanning_sets_le_sourceMetric_and_sourceRate_le_and_decayFactor
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((spanningSet t k X).card : ℝ) ≤ (sourceMetric t k X : ℝ))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa)
    (t k : ℕ) :
    ∀ X : {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k},
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X.1 ≤
        appendixFHoleExpWeight HF kappa X.1.val := by
  intro X
  exact
    cmp116Lemma3ScaleWeight_domination_of_spanning_sets_le_sourceMetric_and_sourceRate_le_and_decayFactor
      Λ
      (sourceMetric := sourceMetric)
      spanningSet
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappa := kappa)
      hskel
      hsub
      hconn
      card_le_sourceMetric
      target_le_source
      kappaSource_nonneg
      decayFactor_reserve
      kappa_nonneg
      t k X.1 X.2

/-- Spanning-set Lemma-3/App-F weight domination over the active subtype, with
the Lemma-3 decay reserve generated from primitive small-delta and large-block
hypotheses. -/
theorem cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_spanning_sets_le_sourceMetric_and_sourceRate_le_and_delta_bounds
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((spanningSet t k X).card : ℝ) ≤ (sourceMetric t k X : ℝ))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa)
    (t k : ℕ) :
    ∀ X : {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k},
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X.1 ≤
        appendixFHoleExpWeight HF kappa X.1.val :=
  cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_spanning_sets_le_sourceMetric_and_sourceRate_le_and_decayFactor
    Λ
    (sourceMetric := sourceMetric)
    spanningSet
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    hskel
    hsub
    hconn
    card_le_sourceMetric
    target_le_source
    kappaSource_nonneg
    (cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (blockScale := blockScale)
      (delta := delta)
      delta_le_one_sixteen
      four_le_blockScale)
    kappa_nonneg
    t k

/-- Self-spanning Lemma-3/App-F weight domination over the active subtype.

The capstone is membership-restricted on `X ∈ Λ t k`; this form packages that
restriction as an unrestricted pointwise domination over the subtype used by
source-facing E/R/B component boundaries. -/
theorem cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_self_sourceRate_le_and_decayFactor
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((X.val.card : ℝ) ≤ (sourceMetric t k X : ℝ)))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa)
    (t k : ℕ) :
    ∀ X : {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k},
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X.1 ≤
        appendixFHoleExpWeight HF kappa X.1.val := by
  intro X
  exact
    cmp116Lemma3ScaleWeight_domination_of_self_le_sourceMetric_and_sourceRate_le_and_decayFactor
      Λ
      (sourceMetric := sourceMetric)
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappa := kappa)
      card_le_sourceMetric
      target_le_source
      kappaSource_nonneg
      decayFactor_reserve
      kappa_nonneg
      t k X.1 X.2

/-- Self-spanning Lemma-3/App-F weight domination over the active subtype, with
the Lemma-3 decay reserve generated from primitive small-delta and large-block
hypotheses. -/
theorem cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_self_sourceRate_le_and_delta_bounds
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((X.val.card : ℝ) ≤ (sourceMetric t k X : ℝ)))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa)
    (t k : ℕ) :
    ∀ X : {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k},
      cmp116Lemma3ScaleWeight
          sourceMetric blockScale delta kappaSource t k X.1 ≤
        appendixFHoleExpWeight HF kappa X.1.val :=
  cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_self_sourceRate_le_and_decayFactor
    Λ
    (sourceMetric := sourceMetric)
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    card_le_sourceMetric
    target_le_source
    kappaSource_nonneg
    (cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (blockScale := blockScale)
      (delta := delta)
      delta_le_one_sixteen
      four_le_blockScale)
    kappa_nonneg
    t k

/-- Active-subtype form of the canonical self-cardinality source-metric
capstone. -/
theorem cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_selfCardSourceMetric_sourceRate_le_and_decayFactor
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa)
    (t k : ℕ) :
    ∀ X : {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k},
      cmp116Lemma3ScaleWeight
          (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
          blockScale delta kappaSource t k X.1 ≤
        appendixFHoleExpWeight HF kappa X.1.val := by
  intro X
  exact
    cmp116Lemma3ScaleWeight_domination_of_selfCardSourceMetric_and_sourceRate_le_and_decayFactor
      Λ
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappa := kappa)
      target_le_source
      kappaSource_nonneg
      decayFactor_reserve
      kappa_nonneg
      t k X.1 X.2

/-- Active-subtype canonical self-cardinality route with constant source rate.
The decay-factor reserve remains explicit. -/
theorem cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_selfCardSourceMetric_constantSourceRate_decayFactor
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {blockScale : ℕ → ℕ → ℕ}
    {delta : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa)
    (t k : ℕ) :
    ∀ X : {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k},
      cmp116Lemma3ScaleWeight
          (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
          blockScale delta (cmp116Lemma3ConstantSourceRate kappa) t k X.1 ≤
        appendixFHoleExpWeight HF kappa X.1.val := by
  intro X
  exact
    cmp116Lemma3ScaleWeight_domination_of_selfCardSourceMetric_and_constantSourceRate_decayFactor
      Λ
      (blockScale := blockScale)
      (delta := delta)
      (kappa := kappa)
      decayFactor_reserve
      kappa_nonneg
      t k X.1 X.2

/-- Active-subtype canonical self-cardinality source-metric capstone with
primitive small-delta and large-block scalar hypotheses. -/
theorem cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_selfCardSourceMetric_sourceRate_le_and_delta_bounds
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa)
    (t k : ℕ) :
    ∀ X : {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k},
      cmp116Lemma3ScaleWeight
          (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
          blockScale delta kappaSource t k X.1 ≤
        appendixFHoleExpWeight HF kappa X.1.val :=
  cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_selfCardSourceMetric_sourceRate_le_and_decayFactor
    Λ
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    target_le_source
    kappaSource_nonneg
    (cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (blockScale := blockScale)
      (delta := delta)
      delta_le_one_sixteen
      four_le_blockScale)
    kappa_nonneg
    t k

/-- Active-subtype canonical self-cardinality route with constant source rate
and primitive small-delta/large-block scalar hypotheses. -/
theorem cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_selfCardSourceMetric_constantSourceRate_delta_bounds
    {d L : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {blockScale : ℕ → ℕ → ℕ}
    {delta : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa)
    (t k : ℕ) :
    ∀ X : {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k},
      cmp116Lemma3ScaleWeight
          (cmp116Lemma3SelfCardSourceMetric (HF := HF) (z := z))
          blockScale delta (cmp116Lemma3ConstantSourceRate kappa) t k X.1 ≤
        appendixFHoleExpWeight HF kappa X.1.val :=
  cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_selfCardSourceMetric_constantSourceRate_decayFactor
    Λ
    (blockScale := blockScale)
    (delta := delta)
    (kappa := kappa)
    (cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (blockScale := blockScale)
      (delta := delta)
      delta_le_one_sixteen
      four_le_blockScale)
    kappa_nonneg
    t k

/-- Eliminate a source-facing E/R/B boundary using the self-spanning Lemma-3
weight capstone.

This is the boundary-record version of the existing component-decay transport:
the record supplies the source-native E/R/B decays and decomposition, while the
self capstone supplies the active-subtype `sourceWeight_le` input. -/
theorem PhysicalGaugeDimock318ERBComponentBoundary.to_flexibleBudgetCertificate_cmp116Lemma3ScaleWeight_self_sourceRate_le_and_decayFactor
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((X.val.card : ℝ) ≤ (sourceMetric t k X : ℝ)))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa)
    {t k : ℕ}
    {activity deltaE rloc bloc :
      {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k} →
        PhysicalGaugeLocalActivity dPhys N Nc}
    {HdeltaSrc HrSrc HbSrc Hdelta Hr Hb H0 : ℝ}
    (h :
      PhysicalGaugeDimock318ERBComponentBoundary
        activity deltaE rloc bloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        HdeltaSrc HrSrc HbSrc)
    (HdeltaSrc_le : HdeltaSrc ≤ Hdelta)
    (HrSrc_le : HrSrc ≤ Hr)
    (HbSrc_le : HbSrc ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc
      (fun X => appendixFHoleExpWeight HF kappa X.1.val)
      Hdelta Hr Hb H0 :=
  h.to_flexibleBudgetCertificate
    (fun X => appendixFHoleExpWeight_nonneg HF kappa X.1.val)
    (cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_self_sourceRate_le_and_decayFactor
      Λ
      (sourceMetric := sourceMetric)
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappa := kappa)
      card_le_sourceMetric
      target_le_source
      kappaSource_nonneg
      decayFactor_reserve
      kappa_nonneg
      t k)
    HdeltaSrc_le
    HrSrc_le
    HbSrc_le
    component_budget

/-- Eliminate a source-facing E/R/B boundary using the self-spanning Lemma-3
weight capstone with primitive small-delta and large-block scalar hypotheses. -/
theorem PhysicalGaugeDimock318ERBComponentBoundary.to_flexibleBudgetCertificate_cmp116Lemma3ScaleWeight_self_sourceRate_le_and_delta_bounds
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((X.val.card : ℝ) ≤ (sourceMetric t k X : ℝ)))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa)
    {t k : ℕ}
    {activity deltaE rloc bloc :
      {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k} →
        PhysicalGaugeLocalActivity dPhys N Nc}
    {HdeltaSrc HrSrc HbSrc Hdelta Hr Hb H0 : ℝ}
    (h :
      PhysicalGaugeDimock318ERBComponentBoundary
        activity deltaE rloc bloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        HdeltaSrc HrSrc HbSrc)
    (HdeltaSrc_le : HdeltaSrc ≤ Hdelta)
    (HrSrc_le : HrSrc ≤ Hr)
    (HbSrc_le : HbSrc ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc
      (fun X => appendixFHoleExpWeight HF kappa X.1.val)
      Hdelta Hr Hb H0 :=
  h.to_flexibleBudgetCertificate
    (fun X => appendixFHoleExpWeight_nonneg HF kappa X.1.val)
    (cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_self_sourceRate_le_and_delta_bounds
      Λ
      (sourceMetric := sourceMetric)
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappa := kappa)
      card_le_sourceMetric
      target_le_source
      kappaSource_nonneg
      delta_le_one_sixteen
      four_le_blockScale
      kappa_nonneg
      t k)
    HdeltaSrc_le
    HrSrc_le
    HbSrc_le
    component_budget

/-- Eliminate a source-facing E/R/B boundary using the spanning-set Lemma-3
weight capstone.

This is the boundary-record version of the spanning-set component-decay
transport: the record supplies the source-native E/R/B decays and
decomposition, while the spanning capstone supplies the active-subtype
`sourceWeight_le` input. -/
theorem PhysicalGaugeDimock318ERBComponentBoundary.to_flexibleBudgetCertificate_cmp116Lemma3ScaleWeight_spanning_sourceRate_le_and_decayFactor
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((spanningSet t k X).card : ℝ) ≤ (sourceMetric t k X : ℝ))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa)
    {t k : ℕ}
    {activity deltaE rloc bloc :
      {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k} →
        PhysicalGaugeLocalActivity dPhys N Nc}
    {HdeltaSrc HrSrc HbSrc Hdelta Hr Hb H0 : ℝ}
    (h :
      PhysicalGaugeDimock318ERBComponentBoundary
        activity deltaE rloc bloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        HdeltaSrc HrSrc HbSrc)
    (HdeltaSrc_le : HdeltaSrc ≤ Hdelta)
    (HrSrc_le : HrSrc ≤ Hr)
    (HbSrc_le : HbSrc ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc
      (fun X => appendixFHoleExpWeight HF kappa X.1.val)
      Hdelta Hr Hb H0 :=
  h.to_flexibleBudgetCertificate
    (fun X => appendixFHoleExpWeight_nonneg HF kappa X.1.val)
    (cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_spanning_sets_le_sourceMetric_and_sourceRate_le_and_decayFactor
      Λ
      (sourceMetric := sourceMetric)
      spanningSet
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappa := kappa)
      hskel
      hsub
      hconn
      card_le_sourceMetric
      target_le_source
      kappaSource_nonneg
      decayFactor_reserve
      kappa_nonneg
      t k)
    HdeltaSrc_le
    HrSrc_le
    HbSrc_le
    component_budget

/-- Eliminate a source-facing E/R/B boundary using the spanning-set Lemma-3
weight capstone with primitive small-delta and large-block scalar hypotheses. -/
theorem PhysicalGaugeDimock318ERBComponentBoundary.to_flexibleBudgetCertificate_cmp116Lemma3ScaleWeight_spanning_sourceRate_le_and_delta_bounds
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((spanningSet t k X).card : ℝ) ≤ (sourceMetric t k X : ℝ))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa)
    {t k : ℕ}
    {activity deltaE rloc bloc :
      {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k} →
        PhysicalGaugeLocalActivity dPhys N Nc}
    {HdeltaSrc HrSrc HbSrc Hdelta Hr Hb H0 : ℝ}
    (h :
      PhysicalGaugeDimock318ERBComponentBoundary
        activity deltaE rloc bloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        HdeltaSrc HrSrc HbSrc)
    (HdeltaSrc_le : HdeltaSrc ≤ Hdelta)
    (HrSrc_le : HrSrc ≤ Hr)
    (HbSrc_le : HbSrc ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc
      (fun X => appendixFHoleExpWeight HF kappa X.1.val)
      Hdelta Hr Hb H0 :=
  h.to_flexibleBudgetCertificate
    (fun X => appendixFHoleExpWeight_nonneg HF kappa X.1.val)
    (cmp116Lemma3ScaleWeight_domination_on_activeSubtype_of_spanning_sets_le_sourceMetric_and_sourceRate_le_and_delta_bounds
      Λ
      (sourceMetric := sourceMetric)
      spanningSet
      (blockScale := blockScale)
      (delta := delta)
      (kappaSource := kappaSource)
      (kappa := kappa)
      hskel
      hsub
      hconn
      card_le_sourceMetric
      target_le_source
      kappaSource_nonneg
      delta_le_one_sixteen
      four_le_blockScale
      kappa_nonneg
      t k)
    HdeltaSrc_le
    HrSrc_le
    HbSrc_le
    component_budget

/-- Build a flexible E/R/B certificate on an active CMP116 scale family after
transporting component decays from the native Lemma-3 scale weight to the
Appendix-F shifted hole weight.

The subtype keeps the active-family membership honest: the Lemma-3/App-F
weight bridge is only known on `X ∈ Λ t k`, so this theorem does not silently
promote it to a global weight domination.  The component estimates and the
E/R/B decomposition remain explicit inputs. -/
theorem PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_cmp116Lemma3ScaleWeight_on_activeFamily
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    {t k : ℕ}
    {activity deltaE rloc bloc :
      {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k} →
        PhysicalGaugeLocalActivity dPhys N Nc}
    {Hdelta Hr Hb H0 : ℝ}
    (weight_domination :
      ∀ X, X ∈ Λ t k →
        cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X ≤
          appendixFHoleExpWeight HF kappa X.val)
    (hHdelta : 0 ≤ Hdelta)
    (hHr : 0 ≤ Hr)
    (hHb : 0 ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hdelta)
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hr)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hb) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc
      (fun X => appendixFHoleExpWeight HF kappa X.1.val)
      Hdelta Hr Hb H0 :=
  PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_weightDomination
    (fun X => appendixFHoleExpWeight_nonneg HF kappa X.1.val)
    (fun X => weight_domination X.1 X.2)
    hHdelta
    hHr
    hHb
    component_budget
    decomposes
    deltaE_decay
    rloc_decay
    bloc_decay

/-- Spanning-set version of the active-family E/R/B weight transport.

This composes the already proved Lemma-3/App-F spanning-set capstone with the
component-decay weight transport.  It proves no component decay, no
decomposition, and no physical source theorem. -/
theorem PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_cmp116Lemma3ScaleWeight_spanning_sourceRate_le_and_decayFactor
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((spanningSet t k X).card : ℝ) ≤ (sourceMetric t k X : ℝ))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa)
    {t k : ℕ}
    {activity deltaE rloc bloc :
      {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k} →
        PhysicalGaugeLocalActivity dPhys N Nc}
    {Hdelta Hr Hb H0 : ℝ}
    (hHdelta : 0 ≤ Hdelta)
    (hHr : 0 ≤ Hr)
    (hHb : 0 ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hdelta)
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hr)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hb) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc
      (fun X => appendixFHoleExpWeight HF kappa X.1.val)
      Hdelta Hr Hb H0 :=
  PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_cmp116Lemma3ScaleWeight_on_activeFamily
    (Λ := Λ)
    (sourceMetric := sourceMetric)
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    (t := t)
    (k := k)
    (fun X hX =>
      cmp116Lemma3ScaleWeight_domination_of_spanning_sets_le_sourceMetric_and_sourceRate_le_and_decayFactor
        Λ
        (sourceMetric := sourceMetric)
        spanningSet
        (blockScale := blockScale)
        (delta := delta)
        (kappaSource := kappaSource)
        (kappa := kappa)
        hskel
        hsub
        hconn
        card_le_sourceMetric
        target_le_source
        kappaSource_nonneg
        decayFactor_reserve
        kappa_nonneg
        t k X hX)
    hHdelta
    hHr
    hHb
    component_budget
    decomposes
    deltaE_decay
    rloc_decay
    bloc_decay

/-- Self-spanning version of the active-family E/R/B weight transport.

This is the concrete convention `spanningSet t k X = X.val`: the only
remaining geometric dictionary input is `X.val.card <= sourceMetric t k X`. -/
theorem PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_cmp116Lemma3ScaleWeight_self_sourceRate_le_and_decayFactor
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((X.val.card : ℝ) ≤ (sourceMetric t k X : ℝ)))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (decayFactor_reserve :
      ∀ t k,
        1 ≤
          balabanCMP116Lemma3DecayFactor
            (blockScale t k) (delta t k))
    (kappa_nonneg : 0 ≤ kappa)
    {t k : ℕ}
    {activity deltaE rloc bloc :
      {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k} →
        PhysicalGaugeLocalActivity dPhys N Nc}
    {Hdelta Hr Hb H0 : ℝ}
    (hHdelta : 0 ≤ Hdelta)
    (hHr : 0 ≤ Hr)
    (hHb : 0 ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hdelta)
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hr)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hb) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc
      (fun X => appendixFHoleExpWeight HF kappa X.1.val)
      Hdelta Hr Hb H0 :=
  PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_cmp116Lemma3ScaleWeight_on_activeFamily
    (Λ := Λ)
    (sourceMetric := sourceMetric)
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    (t := t)
    (k := k)
    (fun X hX =>
      cmp116Lemma3ScaleWeight_domination_of_self_le_sourceMetric_and_sourceRate_le_and_decayFactor
        Λ
        (sourceMetric := sourceMetric)
        (blockScale := blockScale)
        (delta := delta)
        (kappaSource := kappaSource)
        (kappa := kappa)
        card_le_sourceMetric
        target_le_source
        kappaSource_nonneg
        decayFactor_reserve
        kappa_nonneg
        t k X hX)
    hHdelta
    hHr
    hHb
    component_budget
    decomposes
    deltaE_decay
    rloc_decay
    bloc_decay

/-- Spanning-set active-family E/R/B transport with the Lemma-3 decay reserve
generated from primitive small-delta and large-block hypotheses.

This removes only the abstract scalar reserve from the interface.  The
spanning-set dictionary, component estimates, and E/R/B decomposition remain
explicit source obligations. -/
theorem PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_cmp116Lemma3ScaleWeight_spanning_sourceRate_le_and_delta_bounds
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    (spanningSet :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (hskel :
      ∀ t k X, X ∈ Λ t k →
        skeleton HF X.val ⊆ spanningSet t k X)
    (hsub :
      ∀ t k X, X ∈ Λ t k →
        spanningSet t k X ⊆ X.val)
    (hconn :
      ∀ t k X, X ∈ Λ t k →
        cubeConnected (spanningSet t k X))
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((spanningSet t k X).card : ℝ) ≤ (sourceMetric t k X : ℝ))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa)
    {t k : ℕ}
    {activity deltaE rloc bloc :
      {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k} →
        PhysicalGaugeLocalActivity dPhys N Nc}
    {Hdelta Hr Hb H0 : ℝ}
    (hHdelta : 0 ≤ Hdelta)
    (hHr : 0 ≤ Hr)
    (hHb : 0 ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hdelta)
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hr)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hb) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc
      (fun X => appendixFHoleExpWeight HF kappa X.1.val)
      Hdelta Hr Hb H0 :=
  PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_cmp116Lemma3ScaleWeight_spanning_sourceRate_le_and_decayFactor
    (Λ := Λ)
    (sourceMetric := sourceMetric)
    spanningSet
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    hskel
    hsub
    hconn
    card_le_sourceMetric
    target_le_source
    kappaSource_nonneg
    (cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (blockScale := blockScale)
      (delta := delta)
      delta_le_one_sixteen
      four_le_blockScale)
    kappa_nonneg
    hHdelta
    hHr
    hHb
    component_budget
    decomposes
    deltaE_decay
    rloc_decay
    bloc_decay

/-- Self-spanning active-family E/R/B transport with the Lemma-3 decay reserve
generated from primitive small-delta and large-block hypotheses. -/
theorem PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_cmp116Lemma3ScaleWeight_self_sourceRate_le_and_delta_bounds
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ}
    {blockScale : ℕ → ℕ → ℕ}
    {delta kappaSource : ℕ → ℕ → ℝ}
    {kappa : ℝ}
    (card_le_sourceMetric :
      ∀ t k X, X ∈ Λ t k →
        ((X.val.card : ℝ) ≤ (sourceMetric t k X : ℝ)))
    (target_le_source :
      ∀ t k, kappa ≤ kappaSource t k)
    (kappaSource_nonneg :
      ∀ t k, 0 ≤ kappaSource t k)
    (delta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (four_le_blockScale :
      ∀ t k, 4 ≤ blockScale t k)
    (kappa_nonneg : 0 ≤ kappa)
    {t k : ℕ}
    {activity deltaE rloc bloc :
      {X : OmegaPolymerType HF (z t k) // X ∈ Λ t k} →
        PhysicalGaugeLocalActivity dPhys N Nc}
    {Hdelta Hr Hb H0 : ℝ}
    (hHdelta : 0 ≤ Hdelta)
    (hHr : 0 ≤ Hr)
    (hHb : 0 ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField dPhys N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hdelta)
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hr)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc
        (fun X =>
          cmp116Lemma3ScaleWeight
            sourceMetric blockScale delta kappaSource t k X.1)
        Hb) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc
      (fun X => appendixFHoleExpWeight HF kappa X.1.val)
      Hdelta Hr Hb H0 :=
  PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_cmp116Lemma3ScaleWeight_self_sourceRate_le_and_decayFactor
    (Λ := Λ)
    (sourceMetric := sourceMetric)
    (blockScale := blockScale)
    (delta := delta)
    (kappaSource := kappaSource)
    (kappa := kappa)
    card_le_sourceMetric
    target_le_source
    kappaSource_nonneg
    (cmp116Lemma3Scale_decayFactor_reserve_of_delta_le_one_sixteen_and_four_le_blockScale
      (blockScale := blockScale)
      (delta := delta)
      delta_le_one_sixteen
      four_le_blockScale)
    kappa_nonneg
    hHdelta
    hHr
    hHb
    component_budget
    decomposes
    deltaE_decay
    rloc_decay
    bloc_decay

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

/-- Source-neutral boundary identifying a CMP116 resummation with the physical
activity and giving the pointwise termwise norm estimate consumed by Lemma 3.

This record proves neither field.  It only names the two activity/termwise
obligations that are shared by the CMP116 Lemma-3 source packages. -/
structure CMP116Lemma3ActivityTermwiseScaleBoundary
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc) :
    Prop where

  activity_identification :
    ∀ t k Z ψ φ,
      (physicalActivity t k Z).globalEval ψ φ =
        balabanCMP116H (R t k) Z ψ φ

  termwise_estimate :
    ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
      ∀ ψ φ,
        ‖(R t k).summand
            Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
          (R t k).termWeight
            Z x.1.1 x.1.2 x.2.1 x.2.2

/-- Source-facing activity/termwise dictionary staging for CMP116 Lemma 3.

The five Prop parameters name the currently open source-to-Lean dictionary
checks: the `H(Z,Z0)`/`H(Z)` index stack, the summand identity, the printed
term-weight identification, component-factorization compatibility, and
field-uniformity of the termwise estimate.  This record proves none of those
source facts by itself and does not discharge `raw_pointwise_decay`; it only
keeps them explicit before exposing the already-supplied activity equality and
termwise norm estimate as the existing scale boundary. -/
structure CMP116ActivityTermwiseSourceDictionary
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc)
    (indexStackIdentified summandIdentified termWeightIdentified
      componentFactorizationCompatible fieldUniformity : Prop) :
    Prop where

  index_stack_identification : indexStackIdentified
  summand_identification : summandIdentified
  termWeight_identification : termWeightIdentified
  component_factorization_compatible : componentFactorizationCompatible
  field_uniformity : fieldUniformity

  activity_identification :
    ∀ t k Z ψ φ,
      (physicalActivity t k Z).globalEval ψ φ =
        balabanCMP116H (R t k) Z ψ φ

  termwise_estimate :
    ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
      ∀ ψ φ,
        ‖(R t k).summand
            Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
          (R t k).termWeight
            Z x.1.1 x.1.2 x.2.1 x.2.2

namespace CMP116ActivityTermwiseSourceDictionary

/-- Forget the source-dictionary staging fields and expose only the
activity/termwise scale boundary consumed by the Lemma-3 bridges. -/
def to_activityTermwiseScaleBoundary
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {indexStackIdentified summandIdentified termWeightIdentified
      componentFactorizationCompatible fieldUniformity : Prop}
    (h :
      CMP116ActivityTermwiseSourceDictionary
        R physicalActivity
        indexStackIdentified summandIdentified termWeightIdentified
        componentFactorizationCompatible fieldUniformity) :
    CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity where
  activity_identification := h.activity_identification
  termwise_estimate := h.termwise_estimate

/-- Project the still-open H(Z) index-stack dictionary obligation. -/
theorem to_index_stack_identification
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {indexStackIdentified summandIdentified termWeightIdentified
      componentFactorizationCompatible fieldUniformity : Prop}
    (h :
      CMP116ActivityTermwiseSourceDictionary
        R physicalActivity
        indexStackIdentified summandIdentified termWeightIdentified
        componentFactorizationCompatible fieldUniformity) :
    indexStackIdentified :=
  h.index_stack_identification

/-- Project the still-open H(Z) summand dictionary obligation. -/
theorem to_summand_identification
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {indexStackIdentified summandIdentified termWeightIdentified
      componentFactorizationCompatible fieldUniformity : Prop}
    (h :
      CMP116ActivityTermwiseSourceDictionary
        R physicalActivity
        indexStackIdentified summandIdentified termWeightIdentified
        componentFactorizationCompatible fieldUniformity) :
    summandIdentified :=
  h.summand_identification

/-- Project the still-open source term-weight dictionary obligation. -/
theorem to_termWeight_identification
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {indexStackIdentified summandIdentified termWeightIdentified
      componentFactorizationCompatible fieldUniformity : Prop}
    (h :
      CMP116ActivityTermwiseSourceDictionary
        R physicalActivity
        indexStackIdentified summandIdentified termWeightIdentified
        componentFactorizationCompatible fieldUniformity) :
    termWeightIdentified :=
  h.termWeight_identification

/-- Project the still-open component-factorization compatibility obligation. -/
theorem to_component_factorization_compatible
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {indexStackIdentified summandIdentified termWeightIdentified
      componentFactorizationCompatible fieldUniformity : Prop}
    (h :
      CMP116ActivityTermwiseSourceDictionary
        R physicalActivity
        indexStackIdentified summandIdentified termWeightIdentified
        componentFactorizationCompatible fieldUniformity) :
    componentFactorizationCompatible :=
  h.component_factorization_compatible

/-- Project the still-open field-uniformity obligation for the termwise bound. -/
theorem to_field_uniformity
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {indexStackIdentified summandIdentified termWeightIdentified
      componentFactorizationCompatible fieldUniformity : Prop}
    (h :
      CMP116ActivityTermwiseSourceDictionary
        R physicalActivity
        indexStackIdentified summandIdentified termWeightIdentified
        componentFactorizationCompatible fieldUniformity) :
    fieldUniformity :=
  h.field_uniformity

end CMP116ActivityTermwiseSourceDictionary

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

/-- Assemble a scale-family of CMP116 Gaussian-normalization records from
per-scale split source records.

This is the scale-family analogue of
`CMP116GaussianPushforwardNormalization.of_sourceRecords`: callers supply the
coordinate-map source record, physical-law source record, and normalized
pushforward source record at each `(t, k)`, and the intermediate structured
normalization records are built internally. -/
def cmp116GaussianPushforwardNormalizationScaleFamily_of_sourceRecords
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
    (sourceCoordinateMap :
      ∀ _t _k,
        CMP116FluctuationField d L lieDim →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (sourcePhysicalGaussian :
      ∀ _t _k, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (coordinateSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianCoordinateMapSource
          (D t k) (root t k) (sourceCoordinateMap t k))
    (physicalLawSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianPhysicalLawSource
          (sourcePhysicalGaussian t k) (physicalGaussian t k))
    (pushforwardSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianNormalizedPushforwardSource
          (sourceCoordinateMap t k) (sourcePhysicalGaussian t k)) :
    ∀ t k,
      PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization
        (D t k) (root t k) (physicalGaussian t k) :=
  fun t k =>
    PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization.of_sourceRecords
      (sourceCoordinateMap t k)
      (sourcePhysicalGaussian t k)
      (coordinateSource t k)
      (physicalLawSource t k)
      (pushforwardSource t k)

/-- Scale-family raw-source constructor from the structured CMP116 Gaussian
normalization record.

Compared with `rawSource_of_lemma3ActivityEstimate`, callers no longer supply
the dictionary/root Gaussian pushforward equality directly.  They supply the
source-shaped normalization record at each `(t, k)`; the remaining
root-localization, Hessian, local-activity, and Lemma-3 estimates stay explicit
inputs. -/
def rawSource_of_lemma3ActivityEstimate_gaussianNormalization
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
    (gaussian_normalization :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization
          (D t k) (root t k) (physicalGaussian t k))
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
  rawSource_of_lemma3ActivityEstimate
    (fun t k => (gaussian_normalization t k).gaussian_pushforward)
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    lemma3_activity_estimate

/-- Scale-family raw-source constructor from per-scale split CMP116 Gaussian
source records.

This is the source-record-facing variant of
`rawSource_of_lemma3ActivityEstimate_gaussianNormalization`: callers provide
the three CMP116 Eq. (2.5)--(2.6) source records at every scale, while the
intermediate Gaussian-normalization records are assembled internally. -/
def rawSource_of_lemma3ActivityEstimate_sourceRecords
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
    (sourceCoordinateMap :
      ∀ _t _k,
        CMP116FluctuationField d L lieDim →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (sourcePhysicalGaussian :
      ∀ _t _k, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (coordinateSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianCoordinateMapSource
          (D t k) (root t k) (sourceCoordinateMap t k))
    (physicalLawSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianPhysicalLawSource
          (sourcePhysicalGaussian t k) (physicalGaussian t k))
    (pushforwardSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianNormalizedPushforwardSource
          (sourceCoordinateMap t k) (sourcePhysicalGaussian t k))
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
  rawSource_of_lemma3ActivityEstimate_gaussianNormalization
    (cmp116GaussianPushforwardNormalizationScaleFamily_of_sourceRecords
      sourceCoordinateMap sourcePhysicalGaussian
      coordinateSource physicalLawSource pushforwardSource)
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    lemma3_activity_estimate

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

/-- Scale-family lift of the Eq. (2.29)-weighted P-stage adapter.

It turns normalized per-scale P residual summability into the exact
`CMP116PStageSummability` whose budget is the Eq. (2.29) fixed-`D` product. -/
theorem cmp116PStageSummabilityScaleFamily_of_pResidualSummability_weighted
    {σ ιD ιP ιY : ℕ → ℕ → Type*}
    (DIndex : ∀ t k, σ t k → Finset (ιD t k))
    (PIndex : ∀ t k, σ t k → ιD t k → Finset (ιP t k))
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 delta kappa : ℕ → ℕ → ℝ)
    (metric : ∀ t k, σ t k → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (hPResidual :
      ∀ t k,
        CMP116PResidualSummability
          (DIndex t k)
          (PIndex t k)
          (pResidualWeight t k))
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k) :
    ∀ t k,
      CMP116PStageSummability
        (DIndex t k)
        (PIndex t k)
        (cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (delta t k)
          (kappa t k)
          (metric t k)
          (pResidualWeight t k))
        (cmp116Eq229Product
          (DParts t k)
          (alpha6 t k)
          (delta t k)
          (kappa t k)
          (metric t k)) := by
  intro t k
  exact
    cmp116PStageSummability_of_pResidualSummability_weighted
      (DIndex t k)
      (PIndex t k)
      (DParts t k)
      (alpha6 t k)
      (delta t k)
      (kappa t k)
      (metric t k)
      (pResidualWeight t k)
      (hPResidual t k)
      (halpha6 t k)

/-- Build a CMP116 Lemma 3 scale family from Eq. (2.29), normalized
P-residual summability weighted by the Eq. (2.29) product, and a direct
combined post-`P` residual budget at every scale.

This removes the explicit `CMP116PStageSummability` premise on this route by
constructing it from the normalized P-residual estimate and `alpha6 >= 0`.
It proves no source estimate or source identification; Eq. (2.29), the
normalized P residual, the combined post-`P` residual estimate, activity
identification, and termwise bound remain explicit obligations. -/
theorem cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_weightedPResidualPostPResidualBound
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
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (hEq229 :
      ∀ t k,
        CMP116Eq229Summability
          (R t k).DIndex
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k))
    (hPResidual :
      ∀ t k,
        CMP116PResidualSummability
          (R t k).DIndex
          (R t k).PIndex
          (pResidualWeight t k))
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k)
    (hpostP :
      ∀ t k,
        CMP116PostPResidualBound
          (hp t k) (R t k) (sourceMetric t k)
          (cmp116Eq229WeightedPWeight
            (DParts t k)
            (alpha6 t k)
            (hp t k).delta
            (hp t k).kappa
            (eq229Metric t k)
            (pResidualWeight t k)))
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
  have hPStage :
      ∀ t k,
        CMP116PStageSummability
          (R t k).DIndex
          (R t k).PIndex
          (cmp116Eq229WeightedPWeight
            (DParts t k)
            (alpha6 t k)
            (hp t k).delta
            (hp t k).kappa
            (eq229Metric t k)
            (pResidualWeight t k))
          (fun Z D =>
            Finset.prod (DParts t k Z D)
              (cmp116Eq229Weight
                (alpha6 t k)
                (hp t k).delta
                (hp t k).kappa
                (eq229Metric t k Z))) := by
    intro t k
    simpa [cmp116Eq229Product] using
      cmp116PStageSummability_of_pResidualSummability_weighted
        (R t k).DIndex
        (R t k).PIndex
        (DParts t k)
        (alpha6 t k)
        (hp t k).delta
        (hp t k).kappa
        (eq229Metric t k)
        (pResidualWeight t k)
        (hPResidual t k)
        (halpha6 t k)
  exact
    cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      (fun t k =>
        cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k))
      hEq229
      hPStage
      hpostP
      hglobal
      hterm

/-- Pointwise scale-family majorization of the source-shaped post-`P`
amplitude/weight by the canonical CMP116 Lemma-3 base factor.

This predicate proves no source majorization.  It names the exact source-side
obligation consumed by the post-`P` residual adapter at every scale. -/
def CMP116PostPResidualSourceMajorizationScaleFamily
    {σ : ℕ → ℕ → Type*}
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ) : Prop :=
  ∀ t k Z,
    postPAmplitude t k * postPSourceWeight t k Z ≤
      (C3 t k * epsilon1 t k) *
        balabanCMP116Lemma3Weight
          (blockScale t k)
          (delta t k)
          (kappaSource t k)
          (sourceMetric t k)
          Z

/-- A scale family of source-shaped combined post-`P` estimates feeds the
canonical post-`P` residual consumer once the source amplitude/weight is
majorized pointwise and the `P` weight is nonnegative.

This is only the scale-family lift of
`cmp116PostPResidualBound_of_sourceBound`. -/
theorem cmp116PostPResidualBoundScaleFamily_of_sourceBound
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {Ψ Φ : Type*}
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          Ψ Φ)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (pWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (hsource :
      ∀ t k,
        CMP116PostPResidualSourceBound
          (R t k)
          (postPSourceWeight t k)
          (postPAmplitude t k)
          (pWeight t k))
    (hmajorization :
      CMP116PostPResidualSourceMajorizationScaleFamily
        sourceMetric
        (fun t k => (hp t k).blockScale)
        (fun t k => (hp t k).C3)
        (fun t k => (hp t k).epsilon1)
        (fun t k => (hp t k).delta)
        (fun t k => (hp t k).kappa)
        postPSourceWeight
        postPAmplitude)
    (hpWeight_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          0 ≤ pWeight t k Z D P) :
    ∀ t k,
      CMP116PostPResidualBound
        (hp t k)
        (R t k)
        (sourceMetric t k)
        (pWeight t k) := by
  intro t k
  exact
    cmp116PostPResidualBound_of_sourceBound
      (hp t k)
      (R t k)
      (sourceMetric t k)
      (postPSourceWeight t k)
      (postPAmplitude t k)
      (pWeight t k)
      (hsource t k)
      (hmajorization t k)
      (hpWeight_nonneg t k)

/-- Eq. (2.29) boundary for the weighted CMP116 post-`P` source package.

This names the Eq. (2.29) summability field and the nonnegativity of `alpha6`
needed to weight normalized P-residual sums. -/
structure CMP116Lemma3Eq229ScaleBoundary
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric : ∀ t k, σ t k → ιY t k → ℕ) :
    Prop where

  eq229_summability :
    ∀ t k,
      CMP116Eq229Summability
        (R t k).DIndex
        (DParts t k)
        (alpha6 t k)
        (hp t k).delta
        (hp t k).kappa
        (eq229Metric t k)

  alpha6_nonneg :
    ∀ t k, 0 ≤ alpha6 t k

/-- P-stage source boundary for the weighted CMP116 post-`P` source package.

This records the source-shaped P-stage estimate, its scalar smallness
restriction, and pointwise nonnegativity of the normalized P-residual weight. -/
structure CMP116Lemma3PStageSourceScaleBoundary
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ) :
    Prop where

  p_stage_source_bound :
    ∀ t k,
      CMP116PStageSourceBound
        (R t k).DIndex
        (R t k).PIndex
        (pResidualWeight t k)
        (pStageBlockScale t k)
        (pEntropyConstant t k)
        (epsilon2 t k)
        (pStageKappa t k)

  p_stage_smallness :
    ∀ t k,
      2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
          pEntropyConstant t k * epsilon2 t k *
            Real.exp (5 * pStageKappa t k) ≤ 1

  p_residual_weight_nonneg :
    ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P

/-- Scale-family constructor for the P-stage source boundary from the
pointwise/geometric P-stage split.

This is still source-neutral: it packages the pointwise P-term estimate, the
finite geometric P-family summation consequence, the scalar smallness
restriction, and nonnegativity into the existing P-stage boundary record.  It
does not construct the source `P` families or prove any CMP116 scalar hierarchy.
-/
def CMP116Lemma3PStageSourceScaleBoundary.of_pointwise_geometric
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hgeometric :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        Finset.sum ((R t k).PIndex Z D)
            (fun P => pGeometryWeight t k Z D P) ≤
          pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k =>
    cmp116PStageSourceBound_of_pointwise_geometric
      (R t k).DIndex
      (R t k).PIndex
      (pResidualWeight t k)
      (pGeometryWeight t k)
      (pStageBlockScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (hepsilon2_nonneg t k)
      (hpointwise t k)
      (hgeometric t k)

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- Scale-family constructor for the P-stage source boundary from the explicit
CMP116 Eq. (2.31) bond-subset entropy boundary.

This is the theorem-fed variant of `of_pointwise_geometric`: it derives the
finite geometric P-family summation from `CMP116Eq231PBondBoundary` at each
scale, and derives the transcendental rate condition from the source-shaped
rate formula and an algebraic small-coupling inequality.  The source
construction of the `P` families, pointwise residual majorization, remaining
scalar smallness, and constant hierarchy remain explicit inputs. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise
    {σ ιD ιP ιZ0 ιZ0' β : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
          (R t k).DIndex
          (R t k).PIndex
          (eq231LocalizationScale t k))
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                (20 * (gk t k) ^ 2))
              (B t k).gapMass (B t k).pBonds Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k =>
    cmp116PStageSourceBound_of_eq231_pointwise
      (R t k).DIndex
      (R t k).PIndex
      (pResidualWeight t k)
      (pGeometryWeight t k)
      (pStageBlockScale t k)
      (eq231LocalizationScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (gamma2 t k)
      (eq231Epsilon1 t k)
      (gk t k)
      (B t k)
      (hepsilon2_nonneg t k)
      (hpointwise t k)
      (hsourceBracket t k)
      (hgeometry t k)
      (htarget t k)

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- Scale-family constructor for the source-backed CMP116 Eq. (2.31) route
where the `P` index is the finite four-dimensional bond set itself.

Compared with `of_eq231_pointwise`, this source-facing route no longer asks
callers to supply an abstract `CMP116Eq231PBondBoundary`; it constructs that
boundary from `gapCubes`, the concrete four-direction carrier, and the one
remaining source-specific carrier-containment fact. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourceBondSets
    {σ ιD ιZ0 ιZ0' Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ)
    (gapCubes :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k))
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPcarrier :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          P ⊆
            gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)))
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k =>
    cmp116PStageSourceBound_of_eq231_sourceBondSets
      (R t k).DIndex
      (R t k).PIndex
      (pResidualWeight t k)
      (pGeometryWeight t k)
      (gapCubes t k)
      (pStageBlockScale t k)
      (eq231LocalizationScale t k)
      (hlocalizationScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (gamma2 t k)
      (eq231Epsilon1 t k)
      (gk t k)
      (hepsilon2_nonneg t k)
      (hPcarrier t k)
      (hpointwise t k)
      (hsourceBracket t k)
      (hgeometry t k)
      (htarget t k)

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- Scale-family constructor for the source-backed CMP116 Eq. (2.31) route
whose source `P` family is already presented as the filtered powerset of the
four-direction gap carrier.

Compared with `of_eq231_sourceBondSets`, this route replaces the live
source-specific carrier-containment hypothesis by the explicit statement that
`R.PIndex` is the filtered source family `cmp116Eq231SourcePIndex`.  Containment
then follows from powerset membership. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets
    {σ ιD ιZ0 ιZ0' Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ)
    (gapCubes :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k))
    (admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool)
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndex :
      ∀ t k Z D,
        (R t k).PIndex Z D =
          cmp116Eq231SourcePIndex
            (gapCubes t k) (admissible t k) Z D)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k => by
    have hPIndex_fun :
        (R t k).PIndex =
          cmp116Eq231SourcePIndex
            (gapCubes t k) (admissible t k) := by
      funext Z D
      exact hPIndex t k Z D
    have hsource :
        CMP116PStageSourceBound
          (R t k).DIndex
          (cmp116Eq231SourcePIndex
            (gapCubes t k) (admissible t k))
          (pResidualWeight t k)
          (pStageBlockScale t k)
          (pEntropyConstant t k)
          (epsilon2 t k)
          (pStageKappa t k) :=
      cmp116PStageSourceBound_of_eq231_filteredBondSets
        (R t k).DIndex
        (gapCubes t k)
        (admissible t k)
        (pResidualWeight t k)
        (pGeometryWeight t k)
        (pStageBlockScale t k)
        (eq231LocalizationScale t k)
        (hlocalizationScale t k)
        (pEntropyConstant t k)
        (epsilon2 t k)
        (pStageKappa t k)
        (gamma2 t k)
        (eq231Epsilon1 t k)
        (gk t k)
        (hepsilon2_nonneg t k)
        (fun Z D hD P hP =>
          hpointwise t k Z D hD P
            (by simpa [hPIndex t k Z D] using hP))
        (hsourceBracket t k)
        (fun Z D hD P hP =>
          hgeometry t k Z D hD P
            (by simpa [hPIndex t k Z D] using hP))
        (htarget t k)
    simpa [hPIndex_fun] using hsource

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- Scale-family constructor for the incidence-filtered Eq. (2.31) fallback.

This is the doubled-mass incidence analogue of `of_eq231_filteredBondSets`.
The source `P` family is already presented as the filtered powerset of
`cmp116Eq231IncidenceCarrier`, and the geometry estimate is required to use
`cmp116Eq231IncidenceGapMass`.  Consequently this theorem does not pretend to
be the ordinary four-direction Eq. (2.31) source route; any caller must supply
the incidence-specific source theorem and mass/weight normalization explicitly. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_incidenceFilteredBondSets
    {σ ιD ιZ0 ιZ0' Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k)
          (Finset ((Cube t k × Fin 4) × Fin 2))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k →
        Finset ((Cube t k × Fin 4) × Fin 2) → ℝ)
    (gapCubes :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k))
    (admissible :
      ∀ t k, σ t k → ιD t k →
        Finset ((Cube t k × Fin 4) × Fin 2) → Bool)
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndex :
      ∀ t k Z D,
        (R t k).PIndex Z D =
          cmp116Eq231IncidenceSourcePIndex
            (gapCubes t k) (admissible t k) Z D)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                (20 * (gk t k) ^ 2))
              (cmp116Eq231IncidenceGapMass
                (gapCubes t k) (eq231LocalizationScale t k))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k => by
    have hPIndex_fun :
        (R t k).PIndex =
          cmp116Eq231IncidenceSourcePIndex
            (gapCubes t k) (admissible t k) := by
      funext Z D
      exact hPIndex t k Z D
    have hsource :
        CMP116PStageSourceBound
          (R t k).DIndex
          (cmp116Eq231IncidenceSourcePIndex
            (gapCubes t k) (admissible t k))
          (pResidualWeight t k)
          (pStageBlockScale t k)
          (pEntropyConstant t k)
          (epsilon2 t k)
          (pStageKappa t k) :=
      cmp116PStageSourceBound_of_eq231_incidenceFilteredBondSets
        (R t k).DIndex
        (gapCubes t k)
        (admissible t k)
        (pResidualWeight t k)
        (pGeometryWeight t k)
        (pStageBlockScale t k)
        (eq231LocalizationScale t k)
        (hlocalizationScale t k)
        (pEntropyConstant t k)
        (epsilon2 t k)
        (pStageKappa t k)
        (gamma2 t k)
        (eq231Epsilon1 t k)
        (gk t k)
        (hepsilon2_nonneg t k)
        (fun Z D hD P hP =>
          hpointwise t k Z D hD P
            (by simpa [hPIndex t k Z D] using hP))
        (hsourceBracket t k)
        (fun Z D hD P hP =>
          hgeometry t k Z D hD P
            (by simpa [hPIndex t k Z D] using hP))
        (htarget t k)
    simpa [hPIndex_fun] using hsource

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- Scale-family constructor for the source-backed CMP116 Eq. (2.31) route
from the exact pointwise source-membership theorem for `R.PIndex`.

Compared with `of_eq231_filteredBondSets`, this route does not require callers
to first prove the extensional equality
`R.PIndex = cmp116Eq231SourcePIndex gapCubes admissible`.  The pointwise iff
is precisely the source theorem still missing from the citation audit. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourcePIndexMemIff
    {σ ιD ιZ0 ιZ0' Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ)
    (gapCubes :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k))
    (admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool)
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndexMem :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          P ⊆ gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible t k Z D P = true)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa where

  p_stage_source_bound := fun t k =>
    cmp116PStageSourceBound_of_eq231_sourcePIndexMemIff
      (R t k).DIndex
      (R t k).PIndex
      (gapCubes t k)
      (admissible t k)
      (pResidualWeight t k)
      (pGeometryWeight t k)
      (pStageBlockScale t k)
      (eq231LocalizationScale t k)
      (hlocalizationScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (gamma2 t k)
      (eq231Epsilon1 t k)
      (gk t k)
      (hepsilon2_nonneg t k)
      (hPIndexMem t k)
      (hpointwise t k)
      (hsourceBracket t k)
      (hgeometry t k)
      (htarget t k)

  p_stage_smallness := hsmall

  p_residual_weight_nonneg := hpResidual_nonneg

/-- Scale-family constructor for the source-backed CMP116 Eq. (2.31) route
from the one-field positive-tail ownership source record.

Compared with `of_eq231_sourceBondSets`, this route removes the raw
carrier-containment premise.  The exact source membership dictionary,
positive-tail/base ownership record, and admissibility dictionary remain
explicit. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_positiveTailOwnership
    {σ ιD ιZ0 ιZ0' Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ)
    (gapCubes :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k))
    (admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool)
    (sourceAdmissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Prop)
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hmem_iff_source :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          sourceAdmissible t k Z D P)
    (positiveTail :
      ∀ t k,
        CMP116Eq231PositiveTailOwnershipSource
          (gapCubes t k) (sourceAdmissible t k))
    (hadmissible_iff_source :
      ∀ t k Z D P,
        admissible t k Z D P = true ↔
          sourceAdmissible t k Z D P)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa :=
  CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourcePIndexMemIff
    R pResidualWeight pGeometryWeight gapCubes admissible
    pStageBlockScale eq231LocalizationScale
    pEntropyConstant epsilon2 pStageKappa
    gamma2 eq231Epsilon1 gk
    hlocalizationScale hepsilon2_nonneg
    (fun t k =>
      cmp116Eq231_sourcePIndexMemIff_of_positiveTailOwnership
        (R t k).PIndex
        (gapCubes t k)
        (admissible t k)
        (sourceAdmissible t k)
        (hmem_iff_source t k)
        (positiveTail t k)
        (hadmissible_iff_source t k))
    hpointwise hsourceBracket hgeometry htarget hsmall hpResidual_nonneg

/-- Scale-family constructor for the source-backed CMP116 Eq. (2.31) route
from the full Balaban `P`-family source package.

This is the theorem-facing version of
`of_eq231_sourcePIndexMemIff`: instead of asking callers to restate the
pointwise filtered-family iff, it extracts that iff from the named source
package `CMP116Eq231BalabanPFamilySourcePackage`.  Thus the live `hPIndex`
equality/filtering obligation is replaced by a reusable Lean proof object. -/
def CMP116Lemma3PStageSourceScaleBoundary.of_eq231_balabanPFamilySourcePackage
    {σ ιD ιZ0 ιZ0' Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ)
    (gapCubes :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k))
    (admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool)
    (sourceAdmissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Prop)
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa
      gamma2 eq231Epsilon1 gk : ℕ → ℕ → ℝ)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (sourcePackage :
      ∀ t k,
        CMP116Eq231BalabanPFamilySourcePackage
          (R t k).PIndex
          (gapCubes t k)
          (admissible t k)
          (sourceAdmissible t k))
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (eq231Epsilon1 t k) ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P) :
    CMP116Lemma3PStageSourceScaleBoundary
      R pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa :=
  CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourcePIndexMemIff
    R pResidualWeight pGeometryWeight gapCubes admissible
    pStageBlockScale eq231LocalizationScale
    pEntropyConstant epsilon2 pStageKappa
    gamma2 eq231Epsilon1 gk
    hlocalizationScale hepsilon2_nonneg
    (fun t k =>
      cmp116Eq231_balabanPFamily_sourcePIndexMemIff
        (R t k).PIndex
        (gapCubes t k)
        (admissible t k)
        (sourceAdmissible t k)
        (sourcePackage t k))
    hpointwise hsourceBracket hgeometry htarget hsmall hpResidual_nonneg

/-- The P-stage source boundary exposes normalized P-residual summability after
applying its explicit scalar smallness field.

This lets downstream finite-sum consumers use the P-stage boundary without
requiring the larger weighted post-`P` source package. -/
def CMP116Lemma3PStageSourceScaleBoundary.p_residual_summability
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    (source :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa) :
    ∀ t k,
      CMP116PResidualSummability
        (R t k).DIndex
        (R t k).PIndex
        (pResidualWeight t k) := by
  intro t k
  exact
    cmp116PResidualSummability_of_pStageSourceBound
      (R t k).DIndex
      (R t k).PIndex
      (pResidualWeight t k)
      (pStageBlockScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (source.p_stage_source_bound t k)
      (source.p_stage_smallness t k)

/-- Weighted post-`P` source boundary for the CMP116 Lemma-3 scale route.

This names the combined post-`P` source estimate for the Eq. (2.29)-weighted
P weights and the majorization by the canonical Lemma-3 base factor. -/
structure CMP116Lemma3WeightedPostPSourceScaleBoundary
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
    (postPAmplitude : ℕ → ℕ → ℝ) :
    Prop where

  postP_source_bound :
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
          (pResidualWeight t k))

  postP_majorization :
    CMP116PostPResidualSourceMajorizationScaleFamily
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      postPSourceWeight
      postPAmplitude

/-- The weighted post-`P` source boundary exposes the canonical post-`P`
residual bound once the Eq. (2.29) and P-stage boundaries supply weighted
P-weight nonnegativity.

This avoids assembling the larger weighted post-`P` source package when a
downstream proof only needs the post-`P` residual consumer. -/
def CMP116Lemma3WeightedPostPSourceScaleBoundary.postP_residual_bound
    {σ ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
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
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude) :
    ∀ t k,
      CMP116PostPResidualBound
        (hp t k)
        (R t k)
        (sourceMetric t k)
        (cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k)) := by
  have hweighted_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          0 ≤
            cmp116Eq229WeightedPWeight
              (DParts t k)
              (alpha6 t k)
              (hp t k).delta
              (hp t k).kappa
              (eq229Metric t k)
              (pResidualWeight t k)
              Z D P := by
    intro t k Z D _ P _
    exact
      cmp116Eq229WeightedPWeight_nonneg
        (DParts := DParts t k)
        (metric := eq229Metric t k)
        (pResidualWeight := pResidualWeight t k)
        (eq229.alpha6_nonneg t k)
        (pStage.p_residual_weight_nonneg t k)
        Z D P
  exact
    cmp116PostPResidualBoundScaleFamily_of_sourceBound
      hp R sourceMetric postPSourceWeight postPAmplitude
      (fun t k =>
        cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k))
      postP.postP_source_bound
      postP.postP_majorization
      hweighted_nonneg

/-- Source-boundary package for the CMP116 Lemma-3 scale route that keeps the
final `Z0/Z0'` resummation as one combined post-`P` residual estimate.

This record deliberately does not introduce a standalone `Z0'` source scalar
or a fixed-`Z0` source summability theorem.  It only packages the exact
assumptions consumed by
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound`. -/
structure CMP116Lemma3PostPScaleSourceAssumptions
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
    (pWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ) :
    Prop where

  eq229_summability :
    ∀ t k,
      CMP116Eq229Summability
        (R t k).DIndex
        (DParts t k)
        (alpha6 t k)
        (hp t k).delta
        (hp t k).kappa
        (eq229Metric t k)

  p_stage_summability :
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
              (eq229Metric t k Z)))

  postP_residual_bound :
    ∀ t k,
      CMP116PostPResidualBound
        (hp t k) (R t k) (sourceMetric t k) (pWeight t k)

  activity_identification :
    ∀ t k Z ψ φ,
      (physicalActivity t k Z).globalEval ψ φ =
        balabanCMP116H (R t k) Z ψ φ

  termwise_estimate :
    ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
      ∀ ψ φ,
        ‖(R t k).summand
            Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
          (R t k).termWeight
            Z x.1.1 x.1.2 x.2.1 x.2.2

namespace CMP116Lemma3PostPScaleSourceAssumptions

/-- The post-`P` scale-source package exposes the shared
activity-identification/termwise-estimate boundary. -/
def activityTermwiseBoundary
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
    {pWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    (source :
      CMP116Lemma3PostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pWeight) :
    CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity where
  activity_identification := source.activity_identification
  termwise_estimate := source.termwise_estimate

/-- Projection from the post-`P` scale-source package to the existing CMP116
Lemma-3 activity scale-family estimate. -/
def lemma3_activity_estimate
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
    {pWeight : ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    (source :
      CMP116Lemma3PostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pWeight) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound
    hp R sourceMetric physicalActivity DParts alpha6 eq229Metric pWeight
    source.eq229_summability
    source.p_stage_summability
    source.postP_residual_bound
    source.activity_identification
    source.termwise_estimate

end CMP116Lemma3PostPScaleSourceAssumptions

/-- Source-boundary package for the Eq. (2.29)-weighted P-residual CMP116
Lemma-3 scale route.

This is the source-shaped companion to
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_weightedPResidualPostPResidualBound`.
It keeps the P-stage source bound, its scalar smallness restriction, pointwise
P-weight nonnegativity, the combined post-`P` source estimate, and the
post-`P` majorization as separate fields.  It proves no Eq. (2.29), no source
construction of the P family, and no combined post-`P` source estimate. -/
structure CMP116Lemma3WeightedPostPScaleSourceAssumptions
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
    (pResidualWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ) :
    Prop where

  eq229_summability :
    ∀ t k,
      CMP116Eq229Summability
        (R t k).DIndex
        (DParts t k)
        (alpha6 t k)
        (hp t k).delta
        (hp t k).kappa
        (eq229Metric t k)

  p_stage_source_bound :
    ∀ t k,
      CMP116PStageSourceBound
        (R t k).DIndex
        (R t k).PIndex
        (pResidualWeight t k)
        (pStageBlockScale t k)
        (pEntropyConstant t k)
        (epsilon2 t k)
        (pStageKappa t k)

  p_stage_smallness :
    ∀ t k,
      2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
          pEntropyConstant t k * epsilon2 t k *
            Real.exp (5 * pStageKappa t k) ≤ 1

  alpha6_nonneg :
    ∀ t k, 0 ≤ alpha6 t k

  p_residual_weight_nonneg :
    ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P

  postP_source_bound :
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
          (pResidualWeight t k))

  postP_majorization :
    CMP116PostPResidualSourceMajorizationScaleFamily
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      postPSourceWeight
      postPAmplitude

  activity_identification :
    ∀ t k Z ψ φ,
      (physicalActivity t k Z).globalEval ψ φ =
        balabanCMP116H (R t k) Z ψ φ

  termwise_estimate :
    ∀ t k Z x, x ∈ cmp116HIndexFinset (R t k) Z →
      ∀ ψ φ,
        ‖(R t k).summand
            Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
          (R t k).termWeight
            Z x.1.1 x.1.2 x.2.1 x.2.2

namespace CMP116Lemma3WeightedPostPScaleSourceAssumptions

/-- The weighted post-`P` source package exposes the shared
activity-identification/termwise-estimate boundary. -/
def activityTermwiseBoundary
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
    (source :
      CMP116Lemma3WeightedPostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude) :
    CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity where
  activity_identification := source.activity_identification
  termwise_estimate := source.termwise_estimate

/-- Constructor for the weighted post-`P` source package from named
source-boundary subpackages.

This is only record assembly: Eq. (2.29), the P-stage source/smallness data,
the weighted post-`P` source/majorization data, and the activity-termwise
boundary are all supplied explicitly. -/
def of_boundaries
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
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude where
  eq229_summability := eq229.eq229_summability
  p_stage_source_bound := pStage.p_stage_source_bound
  p_stage_smallness := pStage.p_stage_smallness
  alpha6_nonneg := eq229.alpha6_nonneg
  p_residual_weight_nonneg := pStage.p_residual_weight_nonneg
  postP_source_bound := postP.postP_source_bound
  postP_majorization := postP.postP_majorization
  activity_identification := activity.activity_identification
  termwise_estimate := activity.termwise_estimate

/-- Constructor for the weighted post-`P` source package from Eq. (2.29), an
explicit Eq. (2.31) P-bond boundary, the weighted post-`P` boundary, and the
activity/termwise boundary.

This packages the same source-neutral composition as
`lemma3_activity_estimate_of_eq231_boundaries`, but keeps the resulting
`CMP116Lemma3WeightedPostPScaleSourceAssumptions` record available for
downstream projections.  It proves no source construction of the P family,
pointwise P-residual estimate, scalar hierarchy, post-`P` estimate, activity
identification, or termwise bound. -/
def of_eq231_boundaries
    {σ ιD ιP ιZ0 ιZ0' ιY β : ℕ → ℕ → Type*}
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
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
          (R t k).DIndex
          (R t k).PIndex
          (eq231LocalizationScale t k))
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (B t k).gapMass (B t k).pBonds Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise
      R pResidualWeight pGeometryWeight
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      B hepsilon2_nonneg hpointwise hsourceBracket hgeometry htarget
      hsmall hpResidual_nonneg)
    postP
    activity

/-- Constructor for the weighted post-`P` source package from Eq. (2.29), the
filtered-powerset Eq. (2.31) P-family route, the weighted post-`P` boundary,
and the activity/termwise boundary.

Compared with `of_eq231_boundaries`, this route removes the abstract
`CMP116Eq231PBondBoundary` input and the per-`P` carrier-containment premise.
It still requires the source dictionary stating that `R.PIndex` is the filtered
source family `cmp116Eq231SourcePIndex gapCubes admissible`. -/
def of_eq231_filteredBondSets
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndex :
      ∀ t k Z D,
        (R t k).PIndex Z D =
          cmp116Eq231SourcePIndex
            (gapCubes t k) (admissible t k) Z D)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets
      R pResidualWeight pGeometryWeight gapCubes admissible
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      hlocalizationScale hepsilon2_nonneg hPIndex hpointwise
      hsourceBracket hgeometry htarget hsmall hpResidual_nonneg)
    postP
    activity

/-- Constructor for the weighted post-`P` source package from Eq. (2.29), the
incidence-filtered Eq. (2.31) fallback route, the weighted post-`P` boundary,
and the activity/termwise boundary.

This is the incidence analogue of `of_eq231_filteredBondSets`.  It is not the
ordinary four-direction Eq. (2.31) source route: callers must identify
`R.PIndex` with `cmp116Eq231IncidenceSourcePIndex`, and the geometry majorant
must use the doubled fallback mass `cmp116Eq231IncidenceGapMass`. -/
def of_eq231_incidenceFilteredBondSets
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset ((Cube t k × Fin 4) × Fin 2))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k)
          (Finset ((Cube t k × Fin 4) × Fin 2))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k →
        Finset ((Cube t k × Fin 4) × Fin 2) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k →
        Finset ((Cube t k × Fin 4) × Fin 2) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndex :
      ∀ t k Z D,
        (R t k).PIndex Z D =
          cmp116Eq231IncidenceSourcePIndex
            (gapCubes t k) (admissible t k) Z D)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (cmp116Eq231IncidenceGapMass
                (gapCubes t k) (eq231LocalizationScale t k))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_incidenceFilteredBondSets
      R pResidualWeight pGeometryWeight gapCubes admissible
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      hlocalizationScale hepsilon2_nonneg hPIndex hpointwise
      hsourceBracket hgeometry htarget hsmall hpResidual_nonneg)
    postP
    activity

/-- Constructor for the weighted post-`P` source package from Eq. (2.29), the
Eq. (2.31) source-membership theorem for `R.PIndex`, the weighted post-`P`
boundary, and the activity/termwise boundary.

This is the theorem-facing counterpart of `of_eq231_filteredBondSets`: the
future source theorem is the pointwise `PIndex` membership iff, not a separate
extensional equality proof generated outside the package. -/
def of_eq231_sourcePIndexMemIff
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndexMem :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          P ⊆ gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible t k Z D P = true)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourcePIndexMemIff
      R pResidualWeight pGeometryWeight gapCubes admissible
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      hlocalizationScale hepsilon2_nonneg hPIndexMem hpointwise
      hsourceBracket hgeometry htarget hsmall hpResidual_nonneg)
    postP
    activity

/-- Constructor for the weighted post-`P` source package from Eq. (2.29), the
positive-tail/base ownership source record for Eq. (2.31), the weighted
post-`P` boundary, and the activity/termwise boundary.

This route removes the raw carrier-containment input from the source-bond-set
branch.  The source membership and admissibility dictionaries remain explicit,
and the positive-tail ownership theorem is still an input. -/
def of_eq231_positiveTailOwnership
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {sourceAdmissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Prop}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hmem_iff_source :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          sourceAdmissible t k Z D P)
    (positiveTail :
      ∀ t k,
        CMP116Eq231PositiveTailOwnershipSource
          (gapCubes t k) (sourceAdmissible t k))
    (hadmissible_iff_source :
      ∀ t k Z D P,
        admissible t k Z D P = true ↔
          sourceAdmissible t k Z D P)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_positiveTailOwnership
      R pResidualWeight pGeometryWeight gapCubes admissible sourceAdmissible
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      hlocalizationScale hepsilon2_nonneg
      hmem_iff_source positiveTail hadmissible_iff_source
      hpointwise hsourceBracket hgeometry htarget hsmall hpResidual_nonneg)
    postP
    activity

/-- The weighted post-`P` source package exposes normalized P-residual
summability only after applying the explicit source scalar smallness field. -/
def p_residual_summability
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
    (source :
      CMP116Lemma3WeightedPostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude) :
    ∀ t k,
      CMP116PResidualSummability
        (R t k).DIndex
        (R t k).PIndex
        (pResidualWeight t k) := by
  intro t k
  exact
    cmp116PResidualSummability_of_pStageSourceBound
      (R t k).DIndex
      (R t k).PIndex
      (pResidualWeight t k)
      (pStageBlockScale t k)
      (pEntropyConstant t k)
      (epsilon2 t k)
      (pStageKappa t k)
      (source.p_stage_source_bound t k)
      (source.p_stage_smallness t k)

/-- The source-shaped combined post-`P` bound in the weighted package feeds the
canonical post-`P` residual bound for the Eq. (2.29)-weighted P weights. -/
def postP_residual_bound
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
    (source :
      CMP116Lemma3WeightedPostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude) :
    ∀ t k,
      CMP116PostPResidualBound
        (hp t k)
        (R t k)
        (sourceMetric t k)
        (cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k)) := by
  have hweighted_nonneg :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          0 ≤
            cmp116Eq229WeightedPWeight
              (DParts t k)
              (alpha6 t k)
              (hp t k).delta
              (hp t k).kappa
              (eq229Metric t k)
              (pResidualWeight t k)
              Z D P := by
    intro t k Z D _ P _
    exact
      cmp116Eq229WeightedPWeight_nonneg
        (DParts := DParts t k)
        (metric := eq229Metric t k)
        (pResidualWeight := pResidualWeight t k)
        (source.alpha6_nonneg t k)
        (source.p_residual_weight_nonneg t k)
        Z D P
  exact
    cmp116PostPResidualBoundScaleFamily_of_sourceBound
      hp R sourceMetric postPSourceWeight postPAmplitude
      (fun t k =>
        cmp116Eq229WeightedPWeight
          (DParts t k)
          (alpha6 t k)
          (hp t k).delta
          (hp t k).kappa
          (eq229Metric t k)
          (pResidualWeight t k))
      source.postP_source_bound
      source.postP_majorization
      hweighted_nonneg

/-- Projection from the weighted post-`P` scale-source package to the CMP116
Lemma-3 activity scale-family estimate. -/
def lemma3_activity_estimate
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
    (source :
      CMP116Lemma3WeightedPostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude) :
    CMP116Lemma3ActivityEstimateScaleFamily
      physicalActivity
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) :=
  cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_weightedPResidualPostPResidualBound
    hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
    pResidualWeight
    source.eq229_summability
    source.p_residual_summability
    source.alpha6_nonneg
    source.postP_residual_bound
    source.activity_identification
    source.termwise_estimate

/-- Project a weighted post-`P` scale-source package to the raw-source records
consumed by the physical CMP116/Appendix-F path.

The package supplies the Lemma-3 activity estimate; the separated
Gaussian/root/Hessian/activity facts remain explicit. -/
def rawSource
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
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
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
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
    (source :
      CMP116Lemma3WeightedPostPScaleSourceAssumptions
        hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
        pResidualWeight pStageBlockScale pEntropyConstant epsilon2
        pStageKappa postPSourceWeight postPAmplitude) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_lemma3ActivityEstimate
    gaussian_pushforward
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    source.lemma3_activity_estimate

/-- Direct CMP116 Lemma-3 scale-family consumer from the named weighted
post-`P` boundary subpackages.

This only composes `of_boundaries` with `lemma3_activity_estimate`; all source,
smallness, majorization, activity-identification, and termwise-estimate
obligations remain explicit inputs. -/
def lemma3_activity_estimate_of_boundaries
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
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
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
    (of_boundaries eq229 pStage postP activity)

/-- Direct CMP116 Lemma-3 scale-family consumer from Eq. (2.29), the explicit
Eq. (2.31) P-bond entropy boundary, the weighted post-`P` boundary, and the
activity/termwise boundary.

This only composes `CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise`
with `lemma3_activity_estimate_of_boundaries`.  It removes the need for callers
to preassemble a P-stage source boundary when Eq. (2.31) bond data are already
available; all source construction, pointwise, smallness, post-`P`,
majorization, activity-identification, and termwise obligations remain explicit
inputs. -/
def lemma3_activity_estimate_of_eq231_boundaries
    {σ ιD ιP ιZ0 ιZ0' ιY β : ℕ → ℕ → Type*}
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
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → ιP t k → ℝ}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
          (R t k).DIndex
          (R t k).PIndex
          (eq231LocalizationScale t k))
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (B t k).gapMass (B t k).pBonds Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
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
  lemma3_activity_estimate_of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise
      R pResidualWeight pGeometryWeight
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      B hepsilon2_nonneg hpointwise hsourceBracket hgeometry htarget
      hsmall hpResidual_nonneg)
    postP
    activity

/-- Direct CMP116 Lemma-3 scale-family consumer from Eq. (2.29), the
filtered-powerset Eq. (2.31) P-family route, the weighted post-`P` boundary,
and the activity/termwise boundary.

This is the filtered-P counterpart of
`lemma3_activity_estimate_of_eq231_boundaries`: it removes the abstract
Eq. (2.31) bond-boundary input once `R.PIndex` is explicitly identified with
`cmp116Eq231SourcePIndex gapCubes admissible`. -/
def lemma3_activity_estimate_of_eq231_filteredBondSets
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndex :
      ∀ t k Z D,
        (R t k).PIndex Z D =
          cmp116Eq231SourcePIndex
            (gapCubes t k) (admissible t k) Z D)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
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
    (of_eq231_filteredBondSets
      eq229 hlocalizationScale hepsilon2_nonneg hPIndex hpointwise
      hsourceBracket hgeometry htarget hsmall hpResidual_nonneg
      postP activity)

/-- Direct CMP116 Lemma-3 scale-family consumer from Eq. (2.29), the
Eq. (2.31) source-membership theorem for `R.PIndex`, the weighted post-`P`
boundary, and the activity/termwise boundary.

This avoids exposing an auxiliary filtered-family equality to final
Lemma-3 consumers.  The remaining `hPIndexMem` premise is exactly the
source-to-Lean dictionary still requested from the CMP116/CMP109 source
audit. -/
def lemma3_activity_estimate_of_eq231_sourcePIndexMemIff
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndexMem :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          P ⊆ gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible t k Z D P = true)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
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
    (of_eq231_sourcePIndexMemIff
      eq229 hlocalizationScale hepsilon2_nonneg hPIndexMem hpointwise
      hsourceBracket hgeometry htarget hsmall hpResidual_nonneg
      postP activity)

/-- Constructor for the weighted post-`P` source package from Eq. (2.29), the
full Balaban Eq. (2.31) `P`-family source package, the weighted post-`P`
boundary, and the activity/termwise boundary.

This upgrades the `of_eq231_sourcePIndexMemIff` route by extracting the needed
membership iff from `CMP116Eq231BalabanPFamilySourcePackage`, so downstream
callers no longer need to manufacture either the filtered-family equality or
the raw pointwise `hPIndexMem` premise by hand. -/
def of_eq231_balabanPFamilySourcePackage
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {sourceAdmissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Prop}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (sourcePackage :
      ∀ t k,
        CMP116Eq231BalabanPFamilySourcePackage
          (R t k).PIndex
          (gapCubes t k)
          (admissible t k)
          (sourceAdmissible t k))
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    CMP116Lemma3WeightedPostPScaleSourceAssumptions
      hp R sourceMetric physicalActivity DParts alpha6 eq229Metric
      pResidualWeight pStageBlockScale pEntropyConstant epsilon2
      pStageKappa postPSourceWeight postPAmplitude :=
  of_boundaries
    eq229
    (CMP116Lemma3PStageSourceScaleBoundary.of_eq231_balabanPFamilySourcePackage
      R pResidualWeight pGeometryWeight gapCubes admissible sourceAdmissible
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa
      gamma2 (fun t k => (hp t k).epsilon1) gk
      hlocalizationScale hepsilon2_nonneg sourcePackage
      hpointwise hsourceBracket hgeometry htarget hsmall hpResidual_nonneg)
    postP
    activity

/-- Direct CMP116 Lemma-3 scale-family consumer from Eq. (2.29), the full
Balaban Eq. (2.31) `P`-family source package, the weighted post-`P` boundary,
and the activity/termwise boundary.

This is the final consumer form of the source-package bridge: it exposes a
checked Lemma-3 scale-family estimate from the source package itself, without
an intermediate `hPIndex` equality or hand-written membership iff. -/
def lemma3_activity_estimate_of_eq231_balabanPFamilySourcePackage
    {σ ιD ιZ0 ιZ0' ιY Cube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (Cube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (Cube t k)]
    {dPhys N Nc : ℕ} [NeZero N]
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k) (Finset (Cube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {sourceMetric : ∀ t k, σ t k → ℕ}
    {physicalActivity :
      ∀ t k, σ t k → PhysicalGaugeLocalActivity dPhys N Nc}
    {DParts : ∀ t k, σ t k → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric : ∀ t k, σ t k → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → ℝ}
    {gapCubes : ∀ t k, σ t k → ιD t k → Finset (Cube t k)}
    {admissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Bool}
    {sourceAdmissible :
      ∀ t k, σ t k → ιD t k → Finset (Cube t k × Fin 4) → Prop}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight : ∀ t k, σ t k → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (sourcePackage :
      ∀ t k,
        CMP116Eq231BalabanPFamilySourcePackage
          (R t k).PIndex
          (gapCubes t k)
          (admissible t k)
          (sourceAdmissible t k))
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
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
    (of_eq231_balabanPFamilySourcePackage
      eq229 hlocalizationScale hepsilon2_nonneg sourcePackage hpointwise
      hsourceBracket hgeometry htarget hsmall hpResidual_nonneg
      postP activity)

end CMP116Lemma3WeightedPostPScaleSourceAssumptions

/-- Build raw-source records directly from the named weighted post-`P` boundary
subpackages and the separated Gaussian/root/Hessian/activity source facts.

This is a thin composition of
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries`
with `rawSource_of_lemma3ActivityEstimate`; it proves none of the analytic or
physical source obligations supplied as inputs. -/
def rawSource_of_weightedPostPBoundaries
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
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
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
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
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_lemma3ActivityEstimate
    gaussian_pushforward
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    (CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries
      eq229 pStage postP activity)

/-- Gaussian-normalization variant of
`rawSource_of_weightedPostPBoundaries`.

This removes the raw scale-family `gaussian_pushforward` equality from this
route and replaces it by one structured CMP116 Gaussian-normalization record
per `(t, k)`.  It still assumes the root-localization, Hessian,
local-activity, Eq. (2.29), P-stage, post-`P`, and activity/termwise
boundaries. -/
def rawSource_of_weightedPostPBoundaries_gaussianNormalization
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
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
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (gaussian_normalization :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization
          (D t k) (root t k) (physicalGaussian t k))
    (root_localization :
      ∀ t k, rootLocalization t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_lemma3ActivityEstimate_gaussianNormalization
    gaussian_normalization
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    (CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries
      eq229 pStage postP activity)

/-- Source-record variant of
`rawSource_of_weightedPostPBoundaries_gaussianNormalization`.

The Gaussian input is the per-scale triple of CMP116 Eq. (2.5)--(2.6)
source records; all Eq. (2.29), P-stage, post-`P`, activity/termwise,
root-localization, Hessian, and local-activity obligations remain explicit. -/
def rawSource_of_weightedPostPBoundaries_sourceRecords
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιP ιZ0 ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
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
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (sourceCoordinateMap :
      ∀ _t _k,
        CMP116FluctuationField d L lieDim →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (sourcePhysicalGaussian :
      ∀ _t _k, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (coordinateSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianCoordinateMapSource
          (D t k) (root t k) (sourceCoordinateMap t k))
    (physicalLawSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianPhysicalLawSource
          (sourcePhysicalGaussian t k) (physicalGaussian t k))
    (pushforwardSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianNormalizedPushforwardSource
          (sourceCoordinateMap t k) (sourcePhysicalGaussian t k))
    (root_localization :
      ∀ t k, rootLocalization t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_weightedPostPBoundaries_gaussianNormalization
    (cmp116GaussianPushforwardNormalizationScaleFamily_of_sourceRecords
      sourceCoordinateMap sourcePhysicalGaussian
      coordinateSource physicalLawSource pushforwardSource)
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    eq229 pStage postP activity

/-- Build raw-source records from Eq. (2.29), explicit Eq. (2.31) P-bond data,
the weighted post-`P` boundary, the activity/termwise boundary, and the
separated Gaussian/root/Hessian/activity source facts.

This is the Eq. (2.31)-specialized version of
`rawSource_of_weightedPostPBoundaries`.  It avoids requiring callers to
preassemble a `CMP116Lemma3PStageSourceScaleBoundary`; all Eq. (2.31), scalar,
post-`P`, activity, termwise, and physical source obligations are still
supplied explicitly. -/
def rawSource_of_eq231_weightedPostPBoundaries
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιP ιZ0 ιZ0' ιY β : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
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
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
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
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
          (R t k).DIndex
          (R t k).PIndex
          (eq231LocalizationScale t k))
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (B t k).gapMass (B t k).pBonds Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_lemma3ActivityEstimate
    gaussian_pushforward
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    (CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_boundaries
      eq229 B hepsilon2_nonneg hpointwise hsourceBracket
      hgeometry htarget hsmall
      hpResidual_nonneg postP activity)

/-- Gaussian-normalization variant of
`rawSource_of_eq231_weightedPostPBoundaries`.

This is the Eq. (2.31)-specialized raw-source route with the Gaussian
pushforward field supplied through
`CMP116GaussianPushforwardNormalization`, while all Eq. (2.29), Eq. (2.31),
post-`P`, activity/termwise, root-localization, Hessian, and local-activity
obligations remain explicit. -/
def rawSource_of_eq231_weightedPostPBoundaries_gaussianNormalization
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιP ιZ0 ιZ0' ιY β : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
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
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (gaussian_normalization :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization
          (D t k) (root t k) (physicalGaussian t k))
    (root_localization :
      ∀ t k, rootLocalization t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
          (R t k).DIndex
          (R t k).PIndex
          (eq231LocalizationScale t k))
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (B t k).gapMass (B t k).pBonds Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_lemma3ActivityEstimate_gaussianNormalization
    gaussian_normalization
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    (CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_boundaries
      eq229 B hepsilon2_nonneg hpointwise hsourceBracket
      hgeometry htarget hsmall
      hpResidual_nonneg postP activity)

/-- Source-record variant of
`rawSource_of_eq231_weightedPostPBoundaries_gaussianNormalization`.

The Eq. (2.31) and post-`P` source boundaries are unchanged; only the Gaussian
normalization input is pushed down to the three per-scale CMP116 Gaussian
source records. -/
def rawSource_of_eq231_weightedPostPBoundaries_sourceRecords
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιP ιZ0 ιZ0' ιY β : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (ιP t k)]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
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
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → ιP t k → ℝ}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (sourceCoordinateMap :
      ∀ _t _k,
        CMP116FluctuationField d L lieDim →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (sourcePhysicalGaussian :
      ∀ _t _k, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (coordinateSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianCoordinateMapSource
          (D t k) (root t k) (sourceCoordinateMap t k))
    (physicalLawSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianPhysicalLawSource
          (sourcePhysicalGaussian t k) (physicalGaussian t k))
    (pushforwardSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianNormalizedPushforwardSource
          (sourceCoordinateMap t k) (sourcePhysicalGaussian t k))
    (root_localization :
      ∀ t k, rootLocalization t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (B :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
          (R t k).DIndex
          (R t k).PIndex
          (eq231LocalizationScale t k))
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (B t k).gapMass (B t k).pBonds Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_eq231_weightedPostPBoundaries_gaussianNormalization
    (cmp116GaussianPushforwardNormalizationScaleFamily_of_sourceRecords
      sourceCoordinateMap sourcePhysicalGaussian
      coordinateSource physicalLawSource pushforwardSource)
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    eq229 B hepsilon2_nonneg hpointwise hsourceBracket
    hgeometry htarget hsmall hpResidual_nonneg postP activity

/-- Build raw-source records directly from Eq. (2.29), the Eq. (2.31)
source-membership theorem for `R.PIndex`, the weighted post-`P` boundary, the
activity/termwise boundary, and the separated Gaussian/root/Hessian/activity
source facts.

This is the theorem-facing counterpart of
`rawSource_of_eq231_weightedPostPBoundaries`: callers provide the exact
pointwise source-membership iff for the filtered `P` family instead of an
already packaged `CMP116Eq231PBondBoundary`. -/
def rawSource_of_eq231_sourcePIndexMemIff
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιZ0 ιZ0' ιY BondCube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (BondCube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (BondCube t k)]
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
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (Finset (BondCube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k →
          Finset (BondCube t k × Fin 4) → ℝ}
    {gapCubes :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (BondCube t k)}
    {admissible :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k →
          Finset (BondCube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
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
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndexMem :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          P ⊆ gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible t k Z D P = true)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_lemma3ActivityEstimate
    gaussian_pushforward
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    (CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_sourcePIndexMemIff
      eq229 hlocalizationScale hepsilon2_nonneg hPIndexMem hpointwise
      hsourceBracket hgeometry htarget hsmall
      hpResidual_nonneg postP activity)

/-- Gaussian-normalization variant of
`rawSource_of_eq231_sourcePIndexMemIff`.

This is the theorem-facing Eq. (2.31) source-membership route with the Gaussian
pushforward field supplied through
`CMP116GaussianPushforwardNormalization`, while all Eq. (2.29), exact
`R.PIndex` membership, post-`P`, activity/termwise, root-localization,
Hessian, and local-activity obligations remain explicit. -/
def rawSource_of_eq231_sourcePIndexMemIff_gaussianNormalization
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιZ0 ιZ0' ιY BondCube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (BondCube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (BondCube t k)]
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
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (Finset (BondCube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k →
          Finset (BondCube t k × Fin 4) → ℝ}
    {gapCubes :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (BondCube t k)}
    {admissible :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k →
          Finset (BondCube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (gaussian_normalization :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization
          (D t k) (root t k) (physicalGaussian t k))
    (root_localization :
      ∀ t k, rootLocalization t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndexMem :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          P ⊆ gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible t k Z D P = true)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_eq231_sourcePIndexMemIff
    (fun t k => (gaussian_normalization t k).gaussian_pushforward)
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    eq229
    hlocalizationScale
    hepsilon2_nonneg
    hPIndexMem
    hpointwise
    hsourceBracket
    hgeometry
    htarget
    hsmall
    hpResidual_nonneg
    postP
    activity

/-- Source-record variant of
`rawSource_of_eq231_sourcePIndexMemIff_gaussianNormalization`.

This keeps the exact Eq. (2.31) source-membership route as the P-family input
and lowers only the Gaussian pushforward input to the three split CMP116
Gaussian source records at each scale. -/
def rawSource_of_eq231_sourcePIndexMemIff_sourceRecords
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {ιD ιZ0 ιZ0' ιY BondCube : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιD t k)]
    [∀ t k, DecidableEq (Finset (BondCube t k × Fin 4))]
    [∀ t k, DecidableEq (ιZ0 t k)]
    [∀ t k, DecidableEq (ιZ0' t k)]
    [∀ t k, DecidableEq (BondCube t k)]
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
    {hp : ∀ _ _, CMP116Lemma3Parameters}
    {R :
      ∀ t k,
        CMP116HResummation
          (OmegaPolymerType HF (z t k))
          (ιD t k) (Finset (BondCube t k × Fin 4))
          (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc)}
    {DParts :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k → Finset (ιY t k)}
    {alpha6 : ℕ → ℕ → ℝ}
    {eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ}
    {pResidualWeight pGeometryWeight :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k →
          Finset (BondCube t k × Fin 4) → ℝ}
    {gapCubes :
      ∀ t k, OmegaPolymerType HF (z t k) → ιD t k →
        Finset (BondCube t k)}
    {admissible :
      ∀ t k,
        OmegaPolymerType HF (z t k) → ιD t k →
          Finset (BondCube t k × Fin 4) → Bool}
    {pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ}
    {pEntropyConstant epsilon2 pStageKappa gamma2 gk : ℕ → ℕ → ℝ}
    {postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ}
    {postPAmplitude : ℕ → ℕ → ℝ}
    {rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop}
    (sourceCoordinateMap :
      ∀ _t _k,
        CMP116FluctuationField d L lieDim →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (sourcePhysicalGaussian :
      ∀ _t _k, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (coordinateSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianCoordinateMapSource
          (D t k) (root t k) (sourceCoordinateMap t k))
    (physicalLawSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianPhysicalLawSource
          (sourcePhysicalGaussian t k) (physicalGaussian t k))
    (pushforwardSource :
      ∀ t k,
        PhysicalGaugeCMP116Dictionary.CMP116GaussianNormalizedPushforwardSource
          (sourceCoordinateMap t k) (sourcePhysicalGaussian t k))
    (root_localization :
      ∀ t k, rootLocalization t k)
    (wilson_hessian_identification :
      ∀ t k, wilsonHessianIdentification t k)
    (local_physical_activity_construction :
      ∀ t k, localActivityConstruction t k)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary
        hp R DParts alpha6 eq229Metric)
    (hlocalizationScale :
      ∀ t k, 0 < eq231LocalizationScale t k)
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hPIndexMem :
      ∀ t k Z D P,
        P ∈ (R t k).PIndex Z D ↔
          P ⊆ gapCubes t k Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible t k Z D P = true)
    (hpointwise :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              pGeometryWeight t k Z D P)
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgeometry :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          pGeometryWeight t k Z D P ≤
            cmp116Eq231PWeight
              (gamma2 t k * (hp t k).epsilon1 ^ 2 /
                (20 * (gk t k) ^ 2))
              (fun Z D =>
                ((gapCubes t k Z D).card : ℝ) /
                  ((eq231LocalizationScale t k : ℝ) ^ 4))
              (fun _ _ P => P) Z D P)
    (htarget :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hsmall :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary
        hp R sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (activity :
      CMP116Lemma3ActivityTermwiseScaleBoundary R physicalActivity) :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k)
        (root t k)
        (physicalGaussian t k)
        (physicalActivity t k)
        (cmp116Lemma3ScaleWeight
          sourceMetric
          (fun t k => (hp t k).blockScale)
          (fun t k => (hp t k).delta)
          (fun t k => (hp t k).kappa)
          t k)
        (cmp116Lemma3ScaleAmplitude
          (fun t k => (hp t k).C3)
          (fun t k => (hp t k).epsilon1)
          t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k) :=
  rawSource_of_eq231_sourcePIndexMemIff_gaussianNormalization
    (cmp116GaussianPushforwardNormalizationScaleFamily_of_sourceRecords
      sourceCoordinateMap sourcePhysicalGaussian
      coordinateSource physicalLawSource pushforwardSource)
    root_localization
    wilson_hessian_identification
    local_physical_activity_construction
    eq229 hlocalizationScale hepsilon2_nonneg hPIndexMem hpointwise
    hsourceBracket hgeometry htarget hsmall hpResidual_nonneg postP activity

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

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalContourActivityBoundary
import YangMills.RG.BalabanCMP116Lemma3RawSourceAdapter
import YangMills.RG.AppendixFHsharpCardTilt
import YangMills.RG.AppendixFHsharpRawToKP

/-!
# Physical Lemma-3 activities in Appendix-F cube coordinates

The literal contour campaign constructs activities on physical positive bonds,
whereas Appendix F consumes activities on CMP cubes.  The certified CMP116
dictionary supplies the source map from physical bonds to cubes and the exact
pullback of one Lie coordinate fibre.  Reindexing a `LocalActivity` along that
map loses neither its value nor its Lemma-3 estimate.

The terminal theorem converts a Lemma-3 scale estimate into the exact raw
modified-metric inequality used by Appendix F.  It assumes only the genuine
source-metric domination and scalar rate margin; no raw activity bound is an
input.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

namespace PhysicalGaugeCMP116Dictionary

/-- Reindex one physical gauge activity to the cube-coordinate fields used by
the CMP116/Appendix-F integration layer. -/
def reindexPhysicalActivity
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (F : PhysicalGaugeLocalActivity dPhys N Nc) :
    LocalActivity (Cube d L)
      (fun _ => Fin lieDim → ℝ) (fun _ => Fin lieDim → ℝ) ℂ :=
  F.reindex D.siteMap.bondToCube
    (fun b x => D.pullFluctuationAtBond b x)
    (fun b x => D.pullFluctuationAtBond b x)

/-- Global evaluation of the reindexed activity is physical evaluation on the
dictionary-pulled fields. -/
@[simp] theorem globalEval_reindexPhysicalActivity
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (F : PhysicalGaugeLocalActivity dPhys N Nc)
    (psi phi : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    (D.reindexPhysicalActivity F).globalEval psi phi =
      F.globalEval
        (fun b => D.pullFluctuationAtBond b
          (psi (D.siteMap.bondToCube b)))
        (fun b => D.pullFluctuationAtBond b
          (phi (D.siteMap.bondToCube b))) := by
  rfl

end PhysicalGaugeCMP116Dictionary

/-- Reindex a scale family of physical activities to CMP116 cube fields. -/
def cmp116Lemma3CubeActivityScaleFamily
    {ι : ℕ → ℕ → Type*}
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, ι t k → PhysicalGaugeLocalActivity dPhys N Nc) :
    ∀ t k, ι t k →
      LocalActivity (Cube d L)
        (fun _ => Fin lieDim → ℝ) (fun _ => Fin lieDim → ℝ) ℂ :=
  fun t k X => (D t k).reindexPhysicalActivity (physicalActivity t k X)

/-- A Lemma-3 source estimate becomes the exact Appendix-F raw metric decay
after the source metric dominates the shifted modified metric and the target
rate fits below the Lemma-3 decay rate. -/
theorem cmp116Lemma3CubeRawMetricDecay
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource targetRate : ℕ → ℕ → ℝ)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        targetRate t k ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (targetRate_nonneg : ∀ t k, 0 ≤ targetRate t k)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k) :
    ∀ t k psi phi X, X ∈ Λ t k →
      ‖(cmp116Lemma3CubeActivityScaleFamily D physicalActivity t k X
          |>.globalEval psi phi)‖ ≤
        (C3 t k * epsilon1 t k) *
          appendixFHoleExpWeight HF (targetRate t k) X.val := by
  intro t k psi phi X hX
  let pulledPsi : PhysicalGaugeField dPhys N Nc :=
    fun b => (D t k).pullFluctuationAtBond b
      (psi ((D t k).siteMap.bondToCube b))
  let pulledPhi : PhysicalGaugeField dPhys N Nc :=
    fun b => (D t k).pullFluctuationAtBond b
      (phi ((D t k).siteMap.bondToCube b))
  have hmetric :
      balabanCMP116Lemma3Weight
          (blockScale t k) (delta t k) (kappaSource t k)
          (sourceMetric t k) X ≤
        appendixFHoleExpWeight HF (targetRate t k) X.val :=
    balabanCMP116Lemma3Weight_domination_of_sourceMetric_domination_and_rate_margin
      (Λ t k)
      (sourceMetric_domination := sourceMetric_domination t k)
      (rate_margin := rate_margin t k)
      (kappa_nonneg := targetRate_nonneg t k)
      X hX
  calc
    ‖(cmp116Lemma3CubeActivityScaleFamily D physicalActivity t k X
        |>.globalEval psi phi)‖ =
        ‖(physicalActivity t k X).globalEval pulledPsi pulledPhi‖ := by
      rfl
    _ ≤
        (C3 t k * epsilon1 t k) *
          balabanCMP116Lemma3Weight
            (blockScale t k) (delta t k) (kappaSource t k)
            (sourceMetric t k) X :=
      estimate t k X pulledPsi pulledPhi
    _ ≤
        (C3 t k * epsilon1 t k) *
          appendixFHoleExpWeight HF (targetRate t k) X.val :=
      mul_le_mul_of_nonneg_left hmetric (amplitude_nonneg t k)

/-- Convention-robust raw bridge for source metrics that vanish on singleton
polymers.

The geometric input compares the unshifted modified metric with the unshifted
source metric.  The one-unit normalization used by Appendix F is paid by the
explicit factor `exp (targetRate t k)` in the amplitude. -/
theorem cmp116Lemma3CubeRawMetricDecay_of_unshiftedSourceMetric
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource targetRate : ℕ → ℕ → ℝ)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (discreteModifiedMetric HF X.val : ℝ) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        targetRate t k ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (targetRate_nonneg : ∀ t k, 0 ≤ targetRate t k)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k) :
    ∀ t k psi phi X, X ∈ Λ t k →
      ‖(cmp116Lemma3CubeActivityScaleFamily D physicalActivity t k X
          |>.globalEval psi phi)‖ ≤
        ((C3 t k * epsilon1 t k) * Real.exp (targetRate t k)) *
          appendixFHoleExpWeight HF (targetRate t k) X.val := by
  intro t k psi phi X hX
  let pulledPsi : PhysicalGaugeField dPhys N Nc :=
    fun b => (D t k).pullFluctuationAtBond b
      (psi ((D t k).siteMap.bondToCube b))
  let pulledPhi : PhysicalGaugeField dPhys N Nc :=
    fun b => (D t k).pullFluctuationAtBond b
      (phi ((D t k).siteMap.bondToCube b))
  have hmetric :
      balabanCMP116Lemma3Weight
          (blockScale t k) (delta t k) (kappaSource t k)
          (sourceMetric t k) X ≤
        Real.exp (targetRate t k) *
          appendixFHoleExpWeight HF (targetRate t k) X.val :=
    balabanCMP116Lemma3Weight_le_exp_mul_appendixFHoleExpWeight_of_unshiftedSourceMetric
      (Λ t k)
      (sourceMetric_domination := sourceMetric_domination t k)
      (rate_margin := rate_margin t k)
      (kappa_nonneg := targetRate_nonneg t k)
      X hX
  calc
    ‖(cmp116Lemma3CubeActivityScaleFamily D physicalActivity t k X
        |>.globalEval psi phi)‖ =
        ‖(physicalActivity t k X).globalEval pulledPsi pulledPhi‖ := by
      rfl
    _ ≤
        (C3 t k * epsilon1 t k) *
          balabanCMP116Lemma3Weight
            (blockScale t k) (delta t k) (kappaSource t k)
            (sourceMetric t k) X :=
      estimate t k X pulledPsi pulledPhi
    _ ≤
        (C3 t k * epsilon1 t k) *
          (Real.exp (targetRate t k) *
            appendixFHoleExpWeight HF (targetRate t k) X.val) :=
      mul_le_mul_of_nonneg_left hmetric (amplitude_nonneg t k)
    _ =
        ((C3 t k * epsilon1 t k) * Real.exp (targetRate t k)) *
          appendixFHoleExpWeight HF (targetRate t k) X.val := by
      ring

/-- Raw Appendix-F decay when the physical source metric controls the shifted
modified metric with a fixed multiplicative loss.

The loss is paid once in the amplitude as
`exp (metricScale * targetRate)`; it is not hidden in the metric or repeated
per polymer cube. -/
theorem cmp116Lemma3CubeRawMetricDecay_of_scaledSourceMetric
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource metricScale targetRate :
      ℕ → ℕ → ℝ)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          metricScale t k * ((sourceMetric t k X : ℝ) + 1))
    (rate_margin :
      ∀ t k,
        metricScale t k * targetRate t k ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (targetRate_nonneg : ∀ t k, 0 ≤ targetRate t k)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k) :
    ∀ t k psi phi X, X ∈ Λ t k →
      ‖(cmp116Lemma3CubeActivityScaleFamily D physicalActivity t k X
          |>.globalEval psi phi)‖ ≤
        ((C3 t k * epsilon1 t k) *
            Real.exp (metricScale t k * targetRate t k)) *
          appendixFHoleExpWeight HF (targetRate t k) X.val := by
  intro t k psi phi X hX
  let pulledPsi : PhysicalGaugeField dPhys N Nc :=
    fun b => (D t k).pullFluctuationAtBond b
      (psi ((D t k).siteMap.bondToCube b))
  let pulledPhi : PhysicalGaugeField dPhys N Nc :=
    fun b => (D t k).pullFluctuationAtBond b
      (phi ((D t k).siteMap.bondToCube b))
  have hmetric :
      balabanCMP116Lemma3Weight
          (blockScale t k) (delta t k) (kappaSource t k)
          (sourceMetric t k) X ≤
        Real.exp (metricScale t k * targetRate t k) *
          appendixFHoleExpWeight HF (targetRate t k) X.val :=
    balabanCMP116Lemma3Weight_le_scaledExp_mul_appendixFHoleExpWeight
      (Λ t k)
      (sourceMetric_domination := sourceMetric_domination t k)
      (rate_margin := rate_margin t k)
      (kappa_nonneg := targetRate_nonneg t k)
      X hX
  calc
    ‖(cmp116Lemma3CubeActivityScaleFamily D physicalActivity t k X
        |>.globalEval psi phi)‖ =
        ‖(physicalActivity t k X).globalEval pulledPsi pulledPhi‖ := by
      rfl
    _ ≤
        (C3 t k * epsilon1 t k) *
          balabanCMP116Lemma3Weight
            (blockScale t k) (delta t k) (kappaSource t k)
            (sourceMetric t k) X :=
      estimate t k X pulledPsi pulledPhi
    _ ≤
        (C3 t k * epsilon1 t k) *
          (Real.exp (metricScale t k * targetRate t k) *
            appendixFHoleExpWeight HF (targetRate t k) X.val) :=
      mul_le_mul_of_nonneg_left hmetric (amplitude_nonneg t k)
    _ =
        ((C3 t k * epsilon1 t k) *
            Real.exp (metricScale t k * targetRate t k)) *
          appendixFHoleExpWeight HF (targetRate t k) X.val := by
      ring

/-- Specialization to the exact theta-shifted B3 rate required by the terminal
raw-to-KP theorem. -/
theorem cmp116Lemma3CubeRawMetricDecay_boundedHoles
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (B : ℕ) (kappa0 : ℝ)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        4 * kappa0 + 3 + boundedHoleCardinalityTilt d B ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (kappa0_nonneg : 0 ≤ kappa0)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k) :
    ∀ t k psi phi X, X ∈ Λ t k →
      ‖(cmp116Lemma3CubeActivityScaleFamily D physicalActivity t k X
          |>.globalEval psi phi)‖ ≤
        (C3 t k * epsilon1 t k) *
          appendixFHoleExpWeight HF
            (4 * kappa0 + 3 + boundedHoleCardinalityTilt d B) X.val := by
  apply cmp116Lemma3CubeRawMetricDecay
    Λ D physicalActivity sourceMetric blockScale C3 epsilon1 delta
      kappaSource
      (fun _ _ => 4 * kappa0 + 3 + boundedHoleCardinalityTilt d B)
      estimate sourceMetric_domination rate_margin
  · intro t k
    unfold boundedHoleCardinalityTilt
    positivity
  · exact amplitude_nonneg

/-- Bounded-hole specialization of the convention-robust unshifted source
metric bridge. -/
theorem cmp116Lemma3CubeRawMetricDecay_boundedHoles_of_unshiftedSourceMetric
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (B : ℕ) (kappa0 : ℝ)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (discreteModifiedMetric HF X.val : ℝ) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        4 * kappa0 + 3 + boundedHoleCardinalityTilt d B ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (kappa0_nonneg : 0 ≤ kappa0)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k) :
    ∀ t k psi phi X, X ∈ Λ t k →
      ‖(cmp116Lemma3CubeActivityScaleFamily D physicalActivity t k X
          |>.globalEval psi phi)‖ ≤
        ((C3 t k * epsilon1 t k) *
            Real.exp
              (4 * kappa0 + 3 +
                boundedHoleCardinalityTilt d B)) *
          appendixFHoleExpWeight HF
            (4 * kappa0 + 3 + boundedHoleCardinalityTilt d B) X.val := by
  apply cmp116Lemma3CubeRawMetricDecay_of_unshiftedSourceMetric
    Λ D physicalActivity sourceMetric blockScale C3 epsilon1 delta
      kappaSource
      (fun _ _ => 4 * kappa0 + 3 + boundedHoleCardinalityTilt d B)
      estimate sourceMetric_domination rate_margin
  · intro t k
    unfold boundedHoleCardinalityTilt
    positivity
  · exact amplitude_nonneg

/-- Package the dictionary-reindexed physical activities as the localized
CMP116 family consumed by Appendix F.  Only the genuine support and
measurability facts remain as inputs. -/
def cmp116Lemma3LocalizedCubeActivityFamily
    {ι : Type*}
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity : ι → PhysicalGaugeLocalActivity dPhys N Nc)
    (Omega : Finset (Cube d L))
    (activeSupport : ι → Finset (Cube d L))
    (activity_stronglyMeasurable :
      ∀ i, ∀ psi : ∀ _ : Cube d L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube d L, Fin lieDim → ℝ =>
            (D.reindexPhysicalActivity (physicalActivity i)).globalEval psi X))
    (spectatorSupport_subset :
      ∀ i,
        (D.reindexPhysicalActivity
          (physicalActivity i)).spectatorSupport ⊆ activeSupport i)
    (fluctuationSupport_subset :
      ∀ i,
        (D.reindexPhysicalActivity
          (physicalActivity i)).fluctuationSupport ⊆
            Omega ∩ activeSupport i) :
    BalabanCMP116LocalizedActivityFamily
      (Cube d L) lieDim (fun _ => Fin lieDim → ℝ) ι where
  Omega := Omega
  activeSupport := activeSupport
  activity := fun i => D.reindexPhysicalActivity (physicalActivity i)
  activity_stronglyMeasurable := activity_stronglyMeasurable
  spectatorSupport_subset := spectatorSupport_subset
  fluctuationSupport_subset := fluctuationSupport_subset

/-- The localized family built from physical activities satisfies the exact
`hraw` proposition of the bounded-hole Appendix-F closure. -/
theorem cmp116Lemma3LocalizedCubeActivityFamily_rawMetricDecay_boundedHoles
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube d L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube d L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube d L, Fin lieDim → ℝ =>
            ((D t k).reindexPhysicalActivity
              (physicalActivity t k i)).globalEval psi X))
    (spectatorSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).spectatorSupport ⊆
            activeSupport t k i)
    (fluctuationSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).fluctuationSupport ⊆
            Omega t k ∩ activeSupport t k i)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        4 * kappa0 + 3 + boundedHoleCardinalityTilt d B ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (kappa0_nonneg : 0 ≤ kappa0)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k) :
    let F : ∀ t k,
        BalabanCMP116LocalizedActivityFamily
          (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
            (OmegaPolymerType HF (z t k)) :=
      fun t k =>
        cmp116Lemma3LocalizedCubeActivityFamily
          (D t k) (physicalActivity t k) (Omega t k)
          (activeSupport t k)
          (activity_stronglyMeasurable t k)
          (spectatorSupport_subset t k)
          (fluctuationSupport_subset t k)
    ∀ t k psi phi X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval psi phi‖ ≤
        (C3 t k * epsilon1 t k) *
          appendixFHoleExpWeight HF
            (4 * kappa0 + 3 + boundedHoleCardinalityTilt d B) X.val := by
  dsimp
  exact
    cmp116Lemma3CubeRawMetricDecay_boundedHoles
      Λ D physicalActivity sourceMetric blockScale C3 epsilon1 delta
      kappaSource B kappa0 estimate sourceMetric_domination rate_margin
      kappa0_nonneg amplitude_nonneg

/-- Localized `hraw` producer for an unshifted source tree metric.  The
Appendix-F unit shift is reflected only in the explicit effective amplitude. -/
theorem cmp116Lemma3LocalizedCubeActivityFamily_rawMetricDecay_boundedHoles_of_unshiftedSourceMetric
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube d L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube d L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube d L, Fin lieDim → ℝ =>
            ((D t k).reindexPhysicalActivity
              (physicalActivity t k i)).globalEval psi X))
    (spectatorSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).spectatorSupport ⊆
            activeSupport t k i)
    (fluctuationSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).fluctuationSupport ⊆
            Omega t k ∩ activeSupport t k i)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (discreteModifiedMetric HF X.val : ℝ) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        4 * kappa0 + 3 + boundedHoleCardinalityTilt d B ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (kappa0_nonneg : 0 ≤ kappa0)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k) :
    let F : ∀ t k,
        BalabanCMP116LocalizedActivityFamily
          (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
            (OmegaPolymerType HF (z t k)) :=
      fun t k =>
        cmp116Lemma3LocalizedCubeActivityFamily
          (D t k) (physicalActivity t k) (Omega t k)
          (activeSupport t k)
          (activity_stronglyMeasurable t k)
          (spectatorSupport_subset t k)
          (fluctuationSupport_subset t k)
    ∀ t k psi phi X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval psi phi‖ ≤
        ((C3 t k * epsilon1 t k) *
            Real.exp
              (4 * kappa0 + 3 +
                boundedHoleCardinalityTilt d B)) *
          appendixFHoleExpWeight HF
            (4 * kappa0 + 3 + boundedHoleCardinalityTilt d B) X.val := by
  dsimp
  exact
    cmp116Lemma3CubeRawMetricDecay_boundedHoles_of_unshiftedSourceMetric
      Λ D physicalActivity sourceMetric blockScale C3 epsilon1 delta
      kappaSource B kappa0 estimate sourceMetric_domination rate_margin
      kappa0_nonneg amplitude_nonneg

/-- The scalar remainder obtained by summing the real part of the canonical
Appendix-F `H#` activity rooted at `r`.  This is the literal finite-volume
single-scale remainder produced by the localized physical activities. -/
def cmp116Lemma3LocalizedCubeHsharpRemainder
    {d L lieDim : ℕ} [NeZero L]
    {HF : HoleFamily d L}
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
          (OmegaPolymerType HF (z t k)))
    (ν : ℕ → ℕ → Measure (Fin lieDim → ℝ))
    (t k : ℕ) : ℝ :=
  ∑' P : { P : OmegaPolymerType HF zCarrier //
      r ∈ skeleton HF P.val },
    Complex.re
      (balabanCMP116AppendixFHsharpOfIntegratedKsharp
        HF (z t k) (Λ t k) (F t k) (ν t k) P.val.val)

/-- Terminal physical `hRpoly`-shaped scalar decay.  The raw metric estimate is
derived internally from Lemma 3, and the scalar remainder is definitionally
the rooted canonical Appendix-F `H#` series, so no external `hraw` or remainder
identity is assumed. -/
theorem cmp116Lemma3LocalizedCubeActivityFamily_singleScaleUVDecay_boundedHoles
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube d L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube d L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube d L, Fin lieDim → ℝ =>
            ((D t k).reindexPhysicalActivity
              (physicalActivity t k i)).globalEval psi X))
    (spectatorSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).spectatorSupport ⊆
            activeSupport t k i)
    (fluctuationSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).fluctuationSupport ⊆
            Omega t k ∩ activeSupport t k i)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        4 * kappa0 + 3 + boundedHoleCardinalityTilt d B ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (ν : ℕ → ℕ → Measure (Fin lieDim → ℝ))
    (g : ℕ → ℝ)
    (C Hbar c0 : ℝ)
    (hkappa0 : 0 < kappa0)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hC : 0 ≤ C)
    (hHbar : 0 ≤ Hbar)
    (hg : ∀ k, 0 ≤ g k)
    (hamplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k)
    (hamplitude_one : ∀ t k, C3 t k * epsilon1 t k ≤ 1)
    (hhalf : ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 * (C3 t k * epsilon1 t k) *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2)
    (hprofile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          (C3 t k * epsilon1 t k) *
            appendixFHoleRootSumConstant d kappa0 ≤
        C * Hbar * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (hdisj :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 *
      (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1) :
    let F : ∀ t k,
        BalabanCMP116LocalizedActivityFamily
          (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
            (OmegaPolymerType HF (z t k)) :=
      fun t k =>
        cmp116Lemma3LocalizedCubeActivityFamily
          (D t k) (physicalActivity t k) (Omega t k)
          (activeSupport t k)
          (activity_stronglyMeasurable t k)
          (spectatorSupport_subset t k)
          (fluctuationSupport_subset t k)
    SingleScaleUVDecay
      (cmp116Lemma3LocalizedCubeHsharpRemainder
        zCarrier r z Λ F ν)
      g
      ((C * Hbar) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)))⁻¹)
      c0 kappa0 := by
  let F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
          (OmegaPolymerType HF (z t k)) :=
    fun t k =>
      cmp116Lemma3LocalizedCubeActivityFamily
        (D t k) (physicalActivity t k) (Omega t k)
        (activeSupport t k)
        (activity_stronglyMeasurable t k)
        (spectatorSupport_subset t k)
        (fluctuationSupport_subset t k)
  have hraw :
      ∀ t k psi phi X, X ∈ Λ t k →
        ‖((F t k).activity X).globalEval psi phi‖ ≤
          (C3 t k * epsilon1 t k) *
            appendixFHoleExpWeight HF
              (4 * kappa0 + 3 + boundedHoleCardinalityTilt d B) X.val := by
    simpa [F] using
      (cmp116Lemma3LocalizedCubeActivityFamily_rawMetricDecay_boundedHoles
        Λ D physicalActivity sourceMetric blockScale C3 epsilon1 delta
        kappaSource B kappa0 Omega activeSupport
        activity_stronglyMeasurable spectatorSupport_subset
        fluctuationSupport_subset estimate sourceMetric_domination rate_margin
        hkappa0.le hamplitude_nonneg)
  have hrate :
      4 * kappa0 + 3 ≤
        4 * kappa0 + 3 + boundedHoleCardinalityTilt d B := by
    apply le_add_of_nonneg_right
    unfold boundedHoleCardinalityTilt
    positivity
  exact
    singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_sourceMeasurable
      (C := C) (Hbar := Hbar) (c₀ := c0)
      (κ := 4 * kappa0 + 3 + boundedHoleCardinalityTilt d B)
      (κ₀ := kappa0)
      HF zCarrier r z Λ F ν
      (cmp116Lemma3LocalizedCubeHsharpRemainder zCarrier r z Λ F ν)
      g (fun t k => C3 t k * epsilon1 t k)
      hC hHbar hg hrate hkappa0
      (fun _ _ => rfl) hν hamplitude_nonneg hamplitude_one hraw
      hdisj hnoedges hholes_ne hCq hhalf hprofile

/-- Terminal Lemma-3-to-KP composition.  The raw Appendix-F estimate is
generated internally from the physical activity estimate and the exact
dictionary reindexing. -/
theorem cmp116Lemma3LocalizedCubeActivityFamily_KPCriterion_boundedHoles
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube d L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube d L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube d L, Fin lieDim → ℝ =>
            ((D t k).reindexPhysicalActivity
              (physicalActivity t k i)).globalEval psi X))
    (spectatorSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).spectatorSupport ⊆
            activeSupport t k i)
    (fluctuationSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).fluctuationSupport ⊆
            Omega t k ∩ activeSupport t k i)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        4 * kappa0 + 3 + boundedHoleCardinalityTilt d B ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (ν : ℕ → ℕ → Measure (Fin lieDim → ℝ))
    (g : ℕ → ℝ)
    (t0 kScale : ℕ)
    (C Hscale c0 s A : ℝ)
    (hkappa0 : 0 < kappa0)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hamplitude_one : ∀ t k, C3 t k * epsilon1 t k ≤ 1)
    (hhalf : ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 * (C3 t k * epsilon1 t k) *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2)
    (hprofile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          (C3 t k * epsilon1 t k) *
            appendixFHoleRootSumConstant d kappa0 ≤
        C * Hscale * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k)
    (hdisj :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hB : ∀ H0 ∈ HF.holes, H0.card ≤ B)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 *
      (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1)
    (hAmp0 :
      0 ≤ C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) * g kScale ^ kappa0)
    (hA0 : 0 ≤ A)
    (hA : Real.exp s *
        (C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
          g kScale ^ kappa0) ≤ A)
    (hsmall : A *
      (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    let F : ∀ t k,
        BalabanCMP116LocalizedActivityFamily
          (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
            (OmegaPolymerType HF (z t k)) :=
      fun t k =>
        cmp116Lemma3LocalizedCubeActivityFamily
          (D t k) (physicalActivity t k) (Omega t k)
          (activeSupport t k)
          (activity_stronglyMeasurable t k)
          (spectatorSupport_subset t k)
          (fluctuationSupport_subset t k)
    let zK : Finset (Cube d L) → ℂ :=
      balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t0 kScale
    let zH : Finset (Cube d L) → ℂ := appendixFHoleHsharp HF zK
    KP.KPCriterion
      ((omegaHolePolymerSystem HF zH).scaleActivity (Real.exp s))
      (fun Y => (Y.val.card : ℝ)) := by
  let F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
          (OmegaPolymerType HF (z t k)) :=
    fun t k =>
      cmp116Lemma3LocalizedCubeActivityFamily
        (D t k) (physicalActivity t k) (Omega t k)
        (activeSupport t k)
        (activity_stronglyMeasurable t k)
        (spectatorSupport_subset t k)
        (fluctuationSupport_subset t k)
  have hraw :
      ∀ t k psi phi X, X ∈ Λ t k →
        ‖((F t k).activity X).globalEval psi phi‖ ≤
          (C3 t k * epsilon1 t k) *
            appendixFHoleExpWeight HF
              (4 * kappa0 + 3 + boundedHoleCardinalityTilt d B) X.val := by
    simpa [F] using
      (cmp116Lemma3LocalizedCubeActivityFamily_rawMetricDecay_boundedHoles
        Λ D physicalActivity sourceMetric blockScale C3 epsilon1 delta
        kappaSource B kappa0 Omega activeSupport
        activity_stronglyMeasurable spectatorSupport_subset
        fluctuationSupport_subset estimate sourceMetric_domination rate_margin
        hkappa0.le amplitude_nonneg)
  exact
    omegaHolePolymerSystem_KPCriterion_of_rawMetricDecay_canonicalRoot_boundedHoles
      HF z Λ F ν g (fun t k => C3 t k * epsilon1 t k)
      B t0 kScale C Hscale c0 kappa0 s A hkappa0 hν
      amplitude_nonneg hamplitude_one hhalf hprofile hraw
      hdisj hnoedges hholes_ne hB hCq hAmp0 hA0 hA hsmall

/-- Terminal Lemma-3-to-KP composition for an unshifted source tree metric.

The effective raw amplitude includes exactly the `exp targetRate` price of the
Appendix-F `d_M + 1` convention.  All smallness and profile hypotheses are
stated against that effective amplitude, so the shift is never hidden in a
false metric domination. -/
theorem cmp116Lemma3LocalizedCubeActivityFamily_KPCriterion_boundedHoles_of_unshiftedSourceMetric
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube d L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube d L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube d L, Fin lieDim → ℝ =>
            ((D t k).reindexPhysicalActivity
              (physicalActivity t k i)).globalEval psi X))
    (spectatorSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).spectatorSupport ⊆
            activeSupport t k i)
    (fluctuationSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).fluctuationSupport ⊆
            Omega t k ∩ activeSupport t k i)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (discreteModifiedMetric HF X.val : ℝ) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        4 * kappa0 + 3 + boundedHoleCardinalityTilt d B ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (ν : ℕ → ℕ → Measure (Fin lieDim → ℝ))
    (g : ℕ → ℝ)
    (t0 kScale : ℕ)
    (C Hscale c0 s A : ℝ)
    (hkappa0 : 0 < kappa0)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hamplitude_one : ∀ t k,
      (C3 t k * epsilon1 t k) *
          Real.exp
            (4 * kappa0 + 3 + boundedHoleCardinalityTilt d B) ≤
        1)
    (hhalf : ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 *
            ((C3 t k * epsilon1 t k) *
              Real.exp
                (4 * kappa0 + 3 +
                  boundedHoleCardinalityTilt d B)) *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2)
    (hprofile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          ((C3 t k * epsilon1 t k) *
            Real.exp
              (4 * kappa0 + 3 +
                boundedHoleCardinalityTilt d B)) *
            appendixFHoleRootSumConstant d kappa0 ≤
        C * Hscale * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k)
    (hdisj :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hB : ∀ H0 ∈ HF.holes, H0.card ≤ B)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 *
      (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1)
    (hAmp0 :
      0 ≤ C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
        g kScale ^ kappa0)
    (hA0 : 0 ≤ A)
    (hA : Real.exp s *
        (C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
          g kScale ^ kappa0) ≤ A)
    (hsmall : A *
      (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    let F : ∀ t k,
        BalabanCMP116LocalizedActivityFamily
          (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
            (OmegaPolymerType HF (z t k)) :=
      fun t k =>
        cmp116Lemma3LocalizedCubeActivityFamily
          (D t k) (physicalActivity t k) (Omega t k)
          (activeSupport t k)
          (activity_stronglyMeasurable t k)
          (spectatorSupport_subset t k)
          (fluctuationSupport_subset t k)
    let zK : Finset (Cube d L) → ℂ :=
      balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t0 kScale
    let zH : Finset (Cube d L) → ℂ := appendixFHoleHsharp HF zK
    KP.KPCriterion
      ((omegaHolePolymerSystem HF zH).scaleActivity (Real.exp s))
      (fun Y => (Y.val.card : ℝ)) := by
  let targetRate : ℝ :=
    4 * kappa0 + 3 + boundedHoleCardinalityTilt d B
  let effectiveAmplitude : ℕ → ℕ → ℝ :=
    fun t k =>
      (C3 t k * epsilon1 t k) * Real.exp targetRate
  let F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
          (OmegaPolymerType HF (z t k)) :=
    fun t k =>
      cmp116Lemma3LocalizedCubeActivityFamily
        (D t k) (physicalActivity t k) (Omega t k)
        (activeSupport t k)
        (activity_stronglyMeasurable t k)
        (spectatorSupport_subset t k)
        (fluctuationSupport_subset t k)
  have heffective_nonneg :
      ∀ t k, 0 ≤ effectiveAmplitude t k := by
    intro t k
    exact mul_nonneg (amplitude_nonneg t k) (Real.exp_nonneg _)
  have hraw :
      ∀ t k psi phi X, X ∈ Λ t k →
        ‖((F t k).activity X).globalEval psi phi‖ ≤
          effectiveAmplitude t k *
            appendixFHoleExpWeight HF targetRate X.val := by
    simpa [F, effectiveAmplitude, targetRate] using
      (cmp116Lemma3LocalizedCubeActivityFamily_rawMetricDecay_boundedHoles_of_unshiftedSourceMetric
        Λ D physicalActivity sourceMetric blockScale C3 epsilon1 delta
        kappaSource B kappa0 Omega activeSupport
        activity_stronglyMeasurable spectatorSupport_subset
        fluctuationSupport_subset estimate sourceMetric_domination rate_margin
        hkappa0.le amplitude_nonneg)
  exact
    omegaHolePolymerSystem_KPCriterion_of_rawMetricDecay_canonicalRoot_boundedHoles
      HF z Λ F ν g effectiveAmplitude
      B t0 kScale C Hscale c0 kappa0 s A hkappa0 hν
      heffective_nonneg
      (by simpa [effectiveAmplitude, targetRate] using hamplitude_one)
      (by simpa [effectiveAmplitude, targetRate] using hhalf)
      (by simpa [effectiveAmplitude, targetRate] using hprofile)
      hraw hdisj hnoedges hholes_ne hB hCq hAmp0 hA0 hA hsmall

/-- Terminal Lemma-3-to-KP composition for a source metric with a fixed
multiplicative geometry loss.

All Appendix-F smallness hypotheses see the effective amplitude
`C3 * epsilon1 * exp (metricScale * targetRate)`.  Thus the metric conversion
is explicit and cannot conceal a volume-dependent or singleton-invalid
comparison. -/
theorem cmp116Lemma3LocalizedCubeActivityFamily_KPCriterion_boundedHoles_of_scaledSourceMetric
    {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource metricScale : ℕ → ℕ → ℝ)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube d L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube d L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube d L, Fin lieDim → ℝ =>
            ((D t k).reindexPhysicalActivity
              (physicalActivity t k i)).globalEval psi X))
    (spectatorSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).spectatorSupport ⊆
            activeSupport t k i)
    (fluctuationSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).fluctuationSupport ⊆
            Omega t k ∩ activeSupport t k i)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity sourceMetric blockScale
        C3 epsilon1 delta kappaSource)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          metricScale t k * ((sourceMetric t k X : ℝ) + 1))
    (rate_margin :
      ∀ t k,
        metricScale t k *
            (4 * kappa0 + 3 + boundedHoleCardinalityTilt d B) ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (ν : ℕ → ℕ → Measure (Fin lieDim → ℝ))
    (g : ℕ → ℝ)
    (t0 kScale : ℕ)
    (C Hscale c0 s A : ℝ)
    (hkappa0 : 0 < kappa0)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hamplitude_one : ∀ t k,
      (C3 t k * epsilon1 t k) *
          Real.exp
            (metricScale t k *
              (4 * kappa0 + 3 +
                boundedHoleCardinalityTilt d B)) ≤
        1)
    (hhalf : ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 *
            ((C3 t k * epsilon1 t k) *
              Real.exp
                (metricScale t k *
                  (4 * kappa0 + 3 +
                    boundedHoleCardinalityTilt d B))) *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2)
    (hprofile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          ((C3 t k * epsilon1 t k) *
            Real.exp
              (metricScale t k *
                (4 * kappa0 + 3 +
                  boundedHoleCardinalityTilt d B))) *
            appendixFHoleRootSumConstant d kappa0 ≤
        C * Hscale * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k)
    (hdisj :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hB : ∀ H0 ∈ HF.holes, H0.card ≤ B)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 *
      (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1)
    (hAmp0 :
      0 ≤ C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
        g kScale ^ kappa0)
    (hA0 : 0 ≤ A)
    (hA : Real.exp s *
        (C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
          g kScale ^ kappa0) ≤ A)
    (hsmall : A *
      (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    let F : ∀ t k,
        BalabanCMP116LocalizedActivityFamily
          (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
            (OmegaPolymerType HF (z t k)) :=
      fun t k =>
        cmp116Lemma3LocalizedCubeActivityFamily
          (D t k) (physicalActivity t k) (Omega t k)
          (activeSupport t k)
          (activity_stronglyMeasurable t k)
          (spectatorSupport_subset t k)
          (fluctuationSupport_subset t k)
    let zK : Finset (Cube d L) → ℂ :=
      balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t0 kScale
    let zH : Finset (Cube d L) → ℂ := appendixFHoleHsharp HF zK
    KP.KPCriterion
      ((omegaHolePolymerSystem HF zH).scaleActivity (Real.exp s))
      (fun Y => (Y.val.card : ℝ)) := by
  let targetRate : ℝ :=
    4 * kappa0 + 3 + boundedHoleCardinalityTilt d B
  let effectiveAmplitude : ℕ → ℕ → ℝ :=
    fun t k =>
      (C3 t k * epsilon1 t k) *
        Real.exp (metricScale t k * targetRate)
  let F : ∀ t k,
      BalabanCMP116LocalizedActivityFamily
        (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
          (OmegaPolymerType HF (z t k)) :=
    fun t k =>
      cmp116Lemma3LocalizedCubeActivityFamily
        (D t k) (physicalActivity t k) (Omega t k)
        (activeSupport t k)
        (activity_stronglyMeasurable t k)
        (spectatorSupport_subset t k)
        (fluctuationSupport_subset t k)
  have heffective_nonneg :
      ∀ t k, 0 ≤ effectiveAmplitude t k := by
    intro t k
    exact mul_nonneg (amplitude_nonneg t k) (Real.exp_nonneg _)
  have htarget_nonneg : 0 ≤ targetRate := by
    dsimp [targetRate, boundedHoleCardinalityTilt]
    positivity
  have hraw :
      ∀ t k psi phi X, X ∈ Λ t k →
        ‖((F t k).activity X).globalEval psi phi‖ ≤
          effectiveAmplitude t k *
            appendixFHoleExpWeight HF targetRate X.val := by
    simpa [F, effectiveAmplitude, targetRate] using
      (cmp116Lemma3CubeRawMetricDecay_of_scaledSourceMetric
        Λ D physicalActivity sourceMetric blockScale C3 epsilon1 delta
        kappaSource metricScale (fun _ _ => targetRate)
        estimate sourceMetric_domination
        (by simpa [targetRate] using rate_margin)
        (fun _ _ => htarget_nonneg) amplitude_nonneg)
  exact
    omegaHolePolymerSystem_KPCriterion_of_rawMetricDecay_canonicalRoot_boundedHoles
      HF z Λ F ν g effectiveAmplitude
      B t0 kScale C Hscale c0 kappa0 s A hkappa0 hν
      heffective_nonneg
      (by simpa [effectiveAmplitude, targetRate] using hamplitude_one)
      (by simpa [effectiveAmplitude, targetRate] using hhalf)
      (by simpa [effectiveAmplitude, targetRate] using hprofile)
      hraw hdisj hnoedges hholes_ne hB hCq hAmp0 hA0 hA hsmall

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalContourActivityBoundary
import YangMills.RG.BalabanCMP116Lemma3RawSourceAdapter
import YangMills.RG.AppendixFHsharpCardTilt

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

end

end YangMills.RG

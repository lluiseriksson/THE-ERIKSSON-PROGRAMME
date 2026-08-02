/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226CenteredConditionedPhysicalContourActivityBoundary
import YangMills.RG.BalabanCMP116Lemma3CubeRawBridge

/-!
# Centered conditioned physical equation-(2.26) terms produce Appendix-F `hraw`

PRE-VALIDATION: this endpoint now consumes the proof-carrying localized-region
index; its updated `.olean` has not yet been materialized and the interface
change has not yet been verified by the Lean compiler.

This module consumes the corrected physical term source through the existing
equation-(2.29), `P`, and post-`P` source stages.  The output is the literal
raw metric decay required by Appendix F.  The caller supplies those genuine
resummation stages and the usual support/measurability/scalar conditions, but
does not supply an activity identification, a termwise estimate, an
equation-(2.26) bound, or `hraw`.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

private abbrev SourceBond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

/-- Appendix-F raw metric decay for the source-faithful conditioned physical
contour family. -/
theorem cmp116Eq226CenteredConditionedPhysicalContour_rawMetricDecay_of_boundaries
    {nDelta nY M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] [NeZero L] [NeZero lieDim]
    {HF : HoleFamily 4 L}
    {z : ℕ → ℕ → Finset (Cube 4 L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    {ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιZ0' t k)]
    (Dict : ∀ t k,
      PhysicalGaugeCMP116Dictionary 4 (M * (2 * Q)) Nc 4 L lieDim)
    (ambient distinguished :
      ∀ t k, Finset (SourceBond M Q))
    (outerCarrier :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (FinBox 4 (2 * Q)))
    (DIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (Finset (FinBox 4 (2 * Q)))))
    (PIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (FinBox 4 (2 * Q))) →
          Finset (Finset (SourceBond M Q)))
    (Z0Index :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (FinBox 4 (2 * Q))) →
          Finset (SourceBond M Q) →
            Finset (CMP116SourcePhysicalLocalizedRegion (Dict t k)))
    (Z0PrimeIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (FinBox 4 (2 * Q))) →
          Finset (SourceBond M Q) →
            CMP116SourcePhysicalLocalizedRegion (Dict t k) →
              Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226CenteredConditionedPhysicalTermSourceFamily
        (nDelta := nDelta) (nY := nY) (ιZ0' := ιZ0' t k)
        (Dict t k) (ambient t k) (distinguished t k)
          (outerCarrier t k))
    (hp : ∀ t k, CMP116Lemma3Parameters)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (DParts :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (FinBox 4 (2 * Q))) → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (FinBox 4 (2 * Q))) →
          Finset (SourceBond M Q) → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary hp
        (cmp116Eq226CenteredConditionedPhysicalContourResummationScaleFamily
          Dict ambient distinguished outerCarrier
          DIndex PIndex Z0Index Z0PrimeIndex S)
        DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        (cmp116Eq226CenteredConditionedPhysicalContourResummationScaleFamily
          Dict ambient distinguished outerCarrier
          DIndex PIndex Z0Index Z0PrimeIndex S)
        pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary hp
        (cmp116Eq226CenteredConditionedPhysicalContourResummationScaleFamily
          Dict ambient distinguished outerCarrier
          DIndex PIndex Z0Index Z0PrimeIndex S)
        sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ t k, Finset (Cube 4 L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube 4 L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube 4 L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube 4 L, Fin lieDim → ℝ =>
            ((Dict t k).reindexPhysicalActivity
              (cmp116Eq226CenteredConditionedPhysicalContourActivityScaleFamily
                Dict ambient distinguished outerCarrier
                DIndex PIndex Z0Index Z0PrimeIndex S t k i)).globalEval
                  psi X))
    (spectatorSupport_subset :
      ∀ t k i,
        ((Dict t k).reindexPhysicalActivity
          (cmp116Eq226CenteredConditionedPhysicalContourActivityScaleFamily
            Dict ambient distinguished outerCarrier
            DIndex PIndex Z0Index Z0PrimeIndex S t k i)).spectatorSupport ⊆
              activeSupport t k i)
    (fluctuationSupport_subset :
      ∀ t k i,
        ((Dict t k).reindexPhysicalActivity
          (cmp116Eq226CenteredConditionedPhysicalContourActivityScaleFamily
            Dict ambient distinguished outerCarrier
            DIndex PIndex Z0Index Z0PrimeIndex S t k i)).fluctuationSupport ⊆
              Omega t k ∩ activeSupport t k i)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        4 * kappa0 + 3 + boundedHoleCardinalityTilt 4 B ≤
          balabanCMP116Lemma3DecayRate
            (hp t k).blockScale (hp t k).delta (hp t k).kappa)
    (kappa0_nonneg : 0 ≤ kappa0)
    (amplitude_nonneg :
      ∀ t k, 0 ≤ (hp t k).C3 * (hp t k).epsilon1) :
    let physicalActivity :=
      cmp116Eq226CenteredConditionedPhysicalContourActivityScaleFamily
        Dict ambient distinguished outerCarrier
        DIndex PIndex Z0Index Z0PrimeIndex S
    let F : ∀ t k,
        BalabanCMP116LocalizedActivityFamily
          (Cube 4 L) lieDim (fun _ => Fin lieDim → ℝ)
            (OmegaPolymerType HF (z t k)) :=
      fun t k =>
        cmp116Lemma3LocalizedCubeActivityFamily
          (Dict t k) (physicalActivity t k) (Omega t k)
          (activeSupport t k)
          (activity_stronglyMeasurable t k)
          (spectatorSupport_subset t k)
          (fluctuationSupport_subset t k)
    ∀ t k psi phi X, X ∈ Λ t k →
      ‖((F t k).activity X).globalEval psi phi‖ ≤
        ((hp t k).C3 * (hp t k).epsilon1) *
          appendixFHoleExpWeight HF
            (4 * kappa0 + 3 + boundedHoleCardinalityTilt 4 B) X.val := by
  dsimp only
  let physicalActivity :=
    cmp116Eq226CenteredConditionedPhysicalContourActivityScaleFamily
      Dict ambient distinguished outerCarrier
      DIndex PIndex Z0Index Z0PrimeIndex S
  have estimate :
      CMP116Lemma3ActivityEstimateScaleFamily physicalActivity sourceMetric
        (fun t k => (hp t k).blockScale)
        (fun t k => (hp t k).C3)
        (fun t k => (hp t k).epsilon1)
        (fun t k => (hp t k).delta)
        (fun t k => (hp t k).kappa) :=
    cmp116Eq226CenteredConditionedPhysicalContour_lemma3ActivityEstimate_of_boundaries
      Dict ambient distinguished outerCarrier
      DIndex PIndex Z0Index Z0PrimeIndex S hp sourceMetric DParts alpha6
      eq229Metric pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa postPSourceWeight postPAmplitude
      eq229 pStage postP
  simpa [physicalActivity] using
    (cmp116Lemma3LocalizedCubeActivityFamily_rawMetricDecay_boundedHoles
      Λ Dict physicalActivity sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      B kappa0 Omega activeSupport activity_stronglyMeasurable
      spectatorSupport_subset fluctuationSupport_subset estimate
      sourceMetric_domination rate_margin kappa0_nonneg amplitude_nonneg)

end

end YangMills.RG


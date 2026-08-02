/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226CenteredConditionedPhysicalContourToRaw
import YangMills.RG.AppendixFHsharpRawToKP

/-!
# Conditioned physical CMP116 contour terms through `hraw` to KP

PRE-VALIDATION: this endpoint now consumes the proof-carrying localized-region
index; its updated `.olean` has not yet been materialized and the interface
change has not yet been verified by the Lean compiler.

This is the terminal composition of the corrected source route.  The
equation-(2.26) estimate and raw metric decay are generated internally from
the physical conditioned term records.  The remaining hypotheses are the
genuine equation-(2.29), `P`, post-`P`, support, hole-geometry, probability,
and scalar-smallness inputs of Lemma 3 and Appendix F.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

private abbrev SourceBond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

/-- End-to-end bounded-hole KP criterion for the centered conditioned
physical contour source.  No termwise bound, `hraw`, residual `H#` estimate,
or KP conclusion is supplied. -/
theorem cmp116Eq226CenteredConditionedPhysicalContour_KPCriterion_of_boundaries
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
    (ν : ℕ → ℕ → Measure (Fin lieDim → ℝ))
    (g : ℕ → ℝ)
    (t0 kScale : ℕ)
    (C Hscale c0 s A : ℝ)
    (kappa0_pos : 0 < kappa0)
    (ν_probability : ∀ t k, IsProbabilityMeasure (ν t k))
    (amplitude_nonneg :
      ∀ t k, 0 ≤ (hp t k).C3 * (hp t k).epsilon1)
    (amplitude_le_one :
      ∀ t k, (hp t k).C3 * (hp t k).epsilon1 ≤ 1)
    (half_budget : ∀ t k,
      appendixFSecondUrsellLeafConstant 4 kappa0 *
          (2 * ((hp t k).C3 * (hp t k).epsilon1) *
            appendixFHoleRootSumConstant 4 kappa0) ≤ 1 / 2)
    (profile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant 4 kappa0 *
          ((hp t k).C3 * (hp t k).epsilon1) *
            appendixFHoleRootSumConstant 4 kappa0 ≤
        C * Hscale * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (holes_disjoint :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (no_hole_edges : noEdgesBetweenHoles (cubeAdj 4 L) HF.holes)
    (holes_nonempty : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hole_card_bound : ∀ H0 ∈ HF.holes, H0.card ≤ B)
    (geometric_small :
      ((3 ^ 4 : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ 4 + 1)) < 1)
    (target_amplitude_nonneg :
      0 ≤ C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
        g kScale ^ kappa0)
    (A_nonneg : 0 ≤ A)
    (scaled_amplitude :
      Real.exp s *
        (C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
          g kScale ^ kappa0) ≤ A)
    (KP_small :
      A * (1 - ((3 ^ 4 : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ 4 + 1)))⁻¹ ≤ 1) :
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
    let zK : Finset (Cube 4 L) → ℂ :=
      balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t0 kScale
    let zH : Finset (Cube 4 L) → ℂ := appendixFHoleHsharp HF zK
    KP.KPCriterion
      ((omegaHolePolymerSystem HF zH).scaleActivity (Real.exp s))
      (fun Y => (Y.val.card : ℝ)) := by
  dsimp only
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
  have raw_decay :
      ∀ t k psi phi X, X ∈ Λ t k →
        ‖((F t k).activity X).globalEval psi phi‖ ≤
          ((hp t k).C3 * (hp t k).epsilon1) *
            appendixFHoleExpWeight HF
              (4 * kappa0 + 3 + boundedHoleCardinalityTilt 4 B) X.val := by
    simpa [F, physicalActivity] using
      (cmp116Eq226CenteredConditionedPhysicalContour_rawMetricDecay_of_boundaries
        Λ Dict ambient distinguished outerCarrier
        DIndex PIndex Z0Index Z0PrimeIndex S hp sourceMetric DParts alpha6
        eq229Metric pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa postPSourceWeight postPAmplitude
        eq229 pStage postP B kappa0 Omega activeSupport
        activity_stronglyMeasurable spectatorSupport_subset
        fluctuationSupport_subset sourceMetric_domination rate_margin
        kappa0_pos.le amplitude_nonneg)
  simpa [F, physicalActivity] using
    (omegaHolePolymerSystem_KPCriterion_of_rawMetricDecay_canonicalRoot_boundedHoles
      HF z Λ F ν g
      (fun t k => (hp t k).C3 * (hp t k).epsilon1)
      B t0 kScale C Hscale c0 kappa0 s A
      kappa0_pos ν_probability amplitude_nonneg amplitude_le_one
      half_budget profile raw_decay holes_disjoint no_hole_edges
      holes_nonempty hole_card_bound geometric_small
      target_amplitude_nonneg A_nonneg scaled_amplitude KP_small)

end

end YangMills.RG


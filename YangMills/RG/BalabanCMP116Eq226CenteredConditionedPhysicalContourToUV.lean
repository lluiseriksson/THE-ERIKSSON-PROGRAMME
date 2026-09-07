/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226CenteredConditionedPhysicalContourToKP

/-!
# Centered conditioned contour terms produce single-scale UV decay

The centered source contour is the source-faithful route used to separate the
interpolation center from its Cauchy displacement.  This module closes the
previously missing terminal bridge from that route to `SingleScaleUVDecay`.

No raw activity estimate or scalar remainder estimate is supplied: the
equation-(2.26) activity estimate is generated from the centered conditioned
term records and the equation-(2.29), `P`, and post-`P` boundaries, then the
canonical Appendix-F theorem produces the scalar decay.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

private abbrev CenteredUVSourceBond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

/-- The centered conditioned physical contour route reaches the same
`SingleScaleUVDecay` endpoint as the non-centered literal-contour route. -/
theorem
    cmp116Eq226CenteredConditionedPhysicalContour_singleScaleUVDecay_boundedHoles_of_boundaries
    {nDelta nY M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))] [NeZero L] [NeZero lieDim]
    {HF : HoleFamily 4 L}
    {z : ℕ → ℕ → Finset (Cube 4 L) → ℂ}
    {ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ t k, DecidableEq (ιZ0' t k)]
    (zCarrier : Finset (Cube 4 L) → ℂ)
    (r : Cube 4 L)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Dict : ∀ t k,
      PhysicalGaugeCMP116Dictionary 4 (M * (2 * Q)) Nc 4 L lieDim)
    (ambient distinguished :
      ∀ t k, Finset (CenteredUVSourceBond M Q))
    (outerCarrier :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (FinBox 4 (2 * Q)))
    (DIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (Finset (FinBox 4 (2 * Q)))))
    (PIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (FinBox 4 (2 * Q))) →
          Finset (Finset (CenteredUVSourceBond M Q)))
    (Z0Index :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (FinBox 4 (2 * Q))) →
          Finset (CenteredUVSourceBond M Q) →
            Finset (CMP116SourcePhysicalLocalizedRegion (Dict t k)))
    (Z0PrimeIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (FinBox 4 (2 * Q))) →
          Finset (CenteredUVSourceBond M Q) →
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
          Finset (CenteredUVSourceBond M Q) → ℝ)
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
    (C Hbar c0 : ℝ)
    (kappa0_pos : 0 < kappa0)
    (ν_probability : ∀ t k, IsProbabilityMeasure (ν t k))
    (C_nonneg : 0 ≤ C)
    (Hbar_nonneg : 0 ≤ Hbar)
    (g_nonneg : ∀ k, 0 ≤ g k)
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
        C * Hbar * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (holes_disjoint :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (no_hole_edges : noEdgesBetweenHoles (cubeAdj 4 L) HF.holes)
    (holes_nonempty : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (geometric_small :
      ((3 ^ 4 : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ 4 + 1)) < 1) :
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
    SingleScaleUVDecay
      (cmp116Lemma3LocalizedCubeHsharpRemainder
        zCarrier r z Λ F ν)
      g
      ((C * Hbar) *
        (1 - ((3 ^ 4 : ℕ) : ℝ) ^ 2 *
          (Real.exp (-kappa0) * 2 ^ (3 ^ 4 + 1)))⁻¹)
      c0 kappa0 := by
  dsimp only
  let physicalActivity :=
    cmp116Eq226CenteredConditionedPhysicalContourActivityScaleFamily
      Dict ambient distinguished outerCarrier
      DIndex PIndex Z0Index Z0PrimeIndex S
  let estimate :
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
    (cmp116Lemma3LocalizedCubeActivityFamily_singleScaleUVDecay_boundedHoles
      zCarrier r Λ Dict physicalActivity sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      B kappa0 Omega activeSupport activity_stronglyMeasurable
      spectatorSupport_subset fluctuationSupport_subset estimate
      sourceMetric_domination rate_margin ν g C Hbar c0 kappa0_pos
      ν_probability C_nonneg Hbar_nonneg g_nonneg amplitude_nonneg
      amplitude_le_one half_budget profile holes_disjoint no_hole_edges
      holes_nonempty geometric_small)

end

end YangMills.RG

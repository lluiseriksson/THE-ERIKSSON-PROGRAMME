/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma3CubeRawBridge

/-!
# Literal CMP116 contour terms through Lemma 3 and Appendix F

This module composes the source-faithful complex-contour term records with the
three remaining Lemma-3 summation boundaries and the Appendix-F canonical-root
closure.  Neither a termwise estimate, a Lemma-3 activity estimate, a raw
polymer bound, nor the KP conclusion is supplied by the caller.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- End-to-end composition from literal equation-(2.26) contour records,
through the source-shaped equation-(2.29), `P`, and post-`P` boundaries, to the
bounded-hole Appendix-F KP criterion. -/
theorem cmp116Eq226PhysicalContour_KPCriterion_boundedHoles_of_boundaries
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {E : Type*} [Norm E]
    {ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιZ0' _t _k)]
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Dict : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℕ → ℕ → ℝ)
    (q : ℕ → ℕ → ℕ)
    (C2 kappa1 delta kappa gamma gk : ℕ → ℕ → ℝ)
    (alpha outerBound outerRate sourceRate : ℕ → ℕ → ℝ)
    (DIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (Cube d L)))
    (PIndex :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L) →
        Finset (Finset (Cube d L)))
    (Z0Index :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube d L) → Finset (Cube d L) →
          Finset (Finset (FinBox d N')))
    (Z0PrimeIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube d L) → Finset (Cube d L) →
          Finset (FinBox d N') → Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
        (Nc := Nc) (L := L) (lieDim := lieDim) (E := E)
        (ιZ0' := ιZ0' t k)
        (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
        (gamma t k) (gk t k) (alpha t k) (outerBound t k)
        (outerRate t k) (sourceRate t k)
        (OmegaPolymerType HF (z t k)))
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (DParts :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube d L) → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube d L) → Finset (Cube d L) → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary hp
        (cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        (cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary hp
        (cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube d L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube d L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube d L, Fin lieDim → ℝ =>
            ((Dict t k).reindexPhysicalActivity
              ((cmp116Eq226PhysicalContourActivityScaleFamily Dict
                E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
                alpha outerBound outerRate sourceRate
                DIndex PIndex Z0Index Z0PrimeIndex S) t k i)).globalEval
                  psi X))
    (spectatorSupport_subset :
      ∀ t k i,
        ((Dict t k).reindexPhysicalActivity
          ((cmp116Eq226PhysicalContourActivityScaleFamily Dict
            E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
            alpha outerBound outerRate sourceRate
            DIndex PIndex Z0Index Z0PrimeIndex S) t k i)).spectatorSupport ⊆
              activeSupport t k i)
    (fluctuationSupport_subset :
      ∀ t k i,
        ((Dict t k).reindexPhysicalActivity
          ((cmp116Eq226PhysicalContourActivityScaleFamily Dict
            E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
            alpha outerBound outerRate sourceRate
            DIndex PIndex Z0Index Z0PrimeIndex S) t k i)).fluctuationSupport ⊆
              Omega t k ∩ activeSupport t k i)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        4 * kappa0 + 3 + boundedHoleCardinalityTilt d B ≤
          balabanCMP116Lemma3DecayRate
            ((hp t k).blockScale) ((hp t k).delta) ((hp t k).kappa))
    (ν : ℕ → ℕ → Measure (Fin lieDim → ℝ))
    (g : ℕ → ℝ)
    (t0 kScale : ℕ)
    (C Hscale c0 s A : ℝ)
    (hkappa0 : 0 < kappa0)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hamplitude_one :
      ∀ t k, (hp t k).C3 * (hp t k).epsilon1 ≤ 1)
    (hhalf : ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 * ((hp t k).C3 * (hp t k).epsilon1) *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2)
    (hprofile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          ((hp t k).C3 * (hp t k).epsilon1) *
            appendixFHoleRootSumConstant d kappa0 ≤
        C * Hscale * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (amplitude_nonneg :
      ∀ t k, 0 ≤ (hp t k).C3 * (hp t k).epsilon1)
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
    let physicalActivity :=
      cmp116Eq226PhysicalContourActivityScaleFamily Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
        DIndex PIndex Z0Index Z0PrimeIndex S
    let F : ∀ t k,
        BalabanCMP116LocalizedActivityFamily
          (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
            (OmegaPolymerType HF (z t k)) :=
      fun t k =>
        cmp116Lemma3LocalizedCubeActivityFamily
          (Dict t k) (physicalActivity t k) (Omega t k)
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
  let physicalActivity :=
    cmp116Eq226PhysicalContourActivityScaleFamily Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S
  let estimate :
      CMP116Lemma3ActivityEstimateScaleFamily physicalActivity sourceMetric
        (fun t k => (hp t k).blockScale)
        (fun t k => (hp t k).C3)
        (fun t k => (hp t k).epsilon1)
        (fun t k => (hp t k).delta)
        (fun t k => (hp t k).kappa) :=
    cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_boundaries Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S hp sourceMetric DParts alpha6
      eq229Metric pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa postPSourceWeight postPAmplitude
      eq229 pStage postP
  simpa [physicalActivity] using
    (cmp116Lemma3LocalizedCubeActivityFamily_KPCriterion_boundedHoles
      Λ Dict physicalActivity sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      B kappa0 Omega activeSupport activity_stronglyMeasurable
      spectatorSupport_subset fluctuationSupport_subset estimate
      sourceMetric_domination rate_margin ν g t0 kScale C Hscale c0 s A
      hkappa0 hν hamplitude_one hhalf hprofile amplitude_nonneg
      hdisj hnoedges hholes_ne hB hCq hAmp0 hA0 hA hsmall)

/-- The literal-contour counterpart of the terminal `hRpoly` decay theorem.
The activity estimate is assembled from the equation-(2.29), `P`, and post-`P`
source boundaries; the remainder is the canonical rooted `H#` series. -/
theorem cmp116Eq226PhysicalContour_singleScaleUVDecay_boundedHoles_of_boundaries
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {HF : HoleFamily d L}
    {z : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {E : Type*} [Norm E]
    {ιZ0' ιY : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιZ0' _t _k)]
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Dict : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (E0 epsilon1 C1 alpha4 : ℕ → ℕ → ℝ)
    (q : ℕ → ℕ → ℕ)
    (C2 kappa1 delta kappa gamma gk : ℕ → ℕ → ℝ)
    (alpha outerBound outerRate sourceRate : ℕ → ℕ → ℝ)
    (DIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (Cube d L)))
    (PIndex :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L) →
        Finset (Finset (Cube d L)))
    (Z0Index :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube d L) → Finset (Cube d L) →
          Finset (Finset (FinBox d N')))
    (Z0PrimeIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube d L) → Finset (Cube d L) →
          Finset (FinBox d N') → Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := d) (M := M) (N' := N')
        (Nc := Nc) (L := L) (lieDim := lieDim) (E := E)
        (ιZ0' := ιZ0' t k)
        (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
        (gamma t k) (gk t k) (alpha t k) (outerBound t k)
        (outerRate t k) (sourceRate t k)
        (OmegaPolymerType HF (z t k)))
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ)
    (DParts :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube d L) → Finset (ιY t k))
    (alpha6 : ℕ → ℕ → ℝ)
    (eq229Metric :
      ∀ t k, OmegaPolymerType HF (z t k) → ιY t k → ℕ)
    (pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube d L) → Finset (Cube d L) → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
    (eq229 :
      CMP116Lemma3Eq229ScaleBoundary hp
        (cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        DParts alpha6 eq229Metric)
    (pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        (cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary hp
        (cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        sourceMetric DParts alpha6 eq229Metric pResidualWeight
        postPSourceWeight postPAmplitude)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube d L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube d L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube d L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube d L, Fin lieDim → ℝ =>
            ((Dict t k).reindexPhysicalActivity
              ((cmp116Eq226PhysicalContourActivityScaleFamily Dict
                E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
                alpha outerBound outerRate sourceRate
                DIndex PIndex Z0Index Z0PrimeIndex S) t k i)).globalEval
                  psi X))
    (spectatorSupport_subset :
      ∀ t k i,
        ((Dict t k).reindexPhysicalActivity
          ((cmp116Eq226PhysicalContourActivityScaleFamily Dict
            E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
            alpha outerBound outerRate sourceRate
            DIndex PIndex Z0Index Z0PrimeIndex S) t k i)).spectatorSupport ⊆
              activeSupport t k i)
    (fluctuationSupport_subset :
      ∀ t k i,
        ((Dict t k).reindexPhysicalActivity
          ((cmp116Eq226PhysicalContourActivityScaleFamily Dict
            E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
            alpha outerBound outerRate sourceRate
            DIndex PIndex Z0Index Z0PrimeIndex S) t k i)).fluctuationSupport ⊆
              Omega t k ∩ activeSupport t k i)
    (sourceMetric_domination :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (sourceMetric t k X : ℝ))
    (rate_margin :
      ∀ t k,
        4 * kappa0 + 3 + boundedHoleCardinalityTilt d B ≤
          balabanCMP116Lemma3DecayRate
            ((hp t k).blockScale) ((hp t k).delta) ((hp t k).kappa))
    (ν : ℕ → ℕ → Measure (Fin lieDim → ℝ))
    (g : ℕ → ℝ)
    (C Hbar c0 : ℝ)
    (hkappa0 : 0 < kappa0)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hC : 0 ≤ C)
    (hHbar : 0 ≤ Hbar)
    (hg : ∀ k, 0 ≤ g k)
    (hamplitude_nonneg :
      ∀ t k, 0 ≤ (hp t k).C3 * (hp t k).epsilon1)
    (hamplitude_one :
      ∀ t k, (hp t k).C3 * (hp t k).epsilon1 ≤ 1)
    (hhalf : ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 * ((hp t k).C3 * (hp t k).epsilon1) *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2)
    (hprofile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          ((hp t k).C3 * (hp t k).epsilon1) *
            appendixFHoleRootSumConstant d kappa0 ≤
        C * Hbar * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (hdisj :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 *
      (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1) :
    let physicalActivity :=
      cmp116Eq226PhysicalContourActivityScaleFamily Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
        DIndex PIndex Z0Index Z0PrimeIndex S
    let F : ∀ t k,
        BalabanCMP116LocalizedActivityFamily
          (Cube d L) lieDim (fun _ => Fin lieDim → ℝ)
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
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)))⁻¹)
      c0 kappa0 := by
  let physicalActivity :=
    cmp116Eq226PhysicalContourActivityScaleFamily Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S
  let estimate :
      CMP116Lemma3ActivityEstimateScaleFamily physicalActivity sourceMetric
        (fun t k => (hp t k).blockScale)
        (fun t k => (hp t k).C3)
        (fun t k => (hp t k).epsilon1)
        (fun t k => (hp t k).delta)
        (fun t k => (hp t k).kappa) :=
    cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_boundaries Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
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
      sourceMetric_domination rate_margin ν g C Hbar c0 hkappa0 hν
      hC hHbar hg hamplitude_nonneg hamplitude_one hhalf hprofile
      hdisj hnoedges hholes_ne hCq)

end

end YangMills.RG

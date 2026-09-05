/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalContourActivityBoundary
import YangMills.RG.BalabanCMP116Eq229CubeTreeMetricScaleBoundary
import YangMills.RG.BalabanCMP116Lemma3CubeSourceTreeToKP
import YangMills.RG.BalabanCMP116Lemma3CubeRawBridge

/-!
# Physical equation-(2.26) contour estimate with constructed equation (2.29)

This module removes the abstract equation-(2.29) boundary from the literal
four-dimensional contour pipeline.  The physical `D` indices inject into the
exact-union fiber of connected source domains, and the source tree metric
supplies the shifted equation-(2.30) estimate internally.
-/

namespace YangMills.RG

open MeasureTheory

/-- Literal equation-(2.26) contour activity estimate with equation (2.29)
constructed from an injective exact-union domain-family dictionary. -/
def cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_cubeSourceTreeBoundaries
    {nDelta nY M N' Nc L lieDim : ℕ}
    [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E : Type*} [Norm E]
    {σ ιZ0' : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιZ0' _t _k)]
    (Dict : ∀ _t _k,
      PhysicalGaugeCMP116Dictionary 4 (M * N') Nc 4 L lieDim)
    (E0 epsilon1 C1 alpha4 : ℕ → ℕ → ℝ)
    (q : ℕ → ℕ → ℕ)
    (C2 kappa1 delta kappa gamma gk : ℕ → ℕ → ℝ)
    (alpha outerBound outerRate sourceRate : ℕ → ℕ → ℝ)
    (DIndex :
      ∀ t k, σ t k → Finset (Finset (Cube 4 L)))
    (PIndex :
      ∀ t k, σ t k → Finset (Cube 4 L) →
        Finset (Finset (Cube 4 L)))
    (Z0Index :
      ∀ t k, σ t k → Finset (Cube 4 L) → Finset (Cube 4 L) →
        Finset (Finset (FinBox 4 N')))
    (Z0PrimeIndex :
      ∀ t k, σ t k → Finset (Cube 4 L) → Finset (Cube 4 L) →
        Finset (FinBox 4 N') → Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := 4) (M := M) (N' := N')
        (Nc := Nc) (L := L) (lieDim := lieDim) (E := E)
        (ιZ0' := ιZ0' t k)
        (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
        (gamma t k) (gk t k) (alpha t k) (outerBound t k)
        (outerRate t k) (sourceRate t k) (σ t k))
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (DParts :
      ∀ t k, σ t k → Finset (Cube 4 L) →
        Finset (Finset (Cube 4 L)))
    (domainFamily :
      ∀ _t _k, Finset (Finset (Cube 4 L)))
    (unionOf :
      ∀ t k, σ t k → Finset (Cube 4 L))
    (hunion_nonempty :
      ∀ t k Z, (unionOf t k Z).Nonempty)
    (hdomains :
      ∀ t k Y, Y ∈ domainFamily t k →
        Y.Nonempty ∧ walkConnected (cmp116CubeFaceAdj L) Y)
    (hparts_mem :
      ∀ t k Z D, D ∈ DIndex t k Z →
        DParts t k Z D ∈
          cmp116Eq229ExactUnionDIndex
            (domainFamily t k) (unionOf t k Z))
    (hparts_inj :
      ∀ t k Z D₁, D₁ ∈ DIndex t k Z →
        ∀ D₂, D₂ ∈ DIndex t k Z →
          DParts t k Z D₁ = DParts t k Z D₂ →
            D₁ = D₂)
    (alpha6 : ℕ → ℕ → ℝ)
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k)
    (hdeltaKappa :
      ∀ t k, 0 ≤ (hp t k).delta * (hp t k).kappa)
    (hCq :
      ∀ t k,
        64 *
          Real.exp
            (-(((hp t k).delta * (hp t k).kappa) / 48)) < 1)
    (huniform :
      ∀ t k,
        (alpha6 t k *
            Real.exp
              (3 * ((hp t k).delta * (hp t k).kappa))) *
            24 *
            (1 -
              64 *
                Real.exp
                  (-(((hp t k).delta * (hp t k).kappa) / 48)))⁻¹ ≤
          ((hp t k).delta * (hp t k).kappa) / 2)
    (pResidualWeight :
      ∀ t k, σ t k → Finset (Cube 4 L) → Finset (Cube 4 L) → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
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
        sourceMetric DParts alpha6
        (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y)
        pResidualWeight postPSourceWeight postPAmplitude) :
    CMP116Lemma3ActivityEstimateScaleFamily
      (cmp116Eq226PhysicalContourActivityScaleFamily Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
        DIndex PIndex Z0Index Z0PrimeIndex S)
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) := by
  let R :=
    cmp116Eq226PhysicalContourResummationScaleFamily Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S
  have eq229 :
      CMP116Lemma3Eq229ScaleBoundary hp R DParts alpha6
        (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y) :=
    CMP116Lemma3Eq229ScaleBoundary.of_cubeSourceTreeMetric_exactUnionInjection
      hp R DParts domainFamily unionOf hunion_nonempty hdomains
      hparts_mem hparts_inj
      alpha6 halpha6 hdeltaKappa hCq huniform
  exact
    cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_boundaries Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S hp sourceMetric DParts alpha6
      (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y)
      pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa postPSourceWeight postPAmplitude
      eq229 pStage postP

/-- Exact Appendix-F `hraw` for the literal four-dimensional contour
activity, with the source tree metric and equation (2.29) constructed
internally.

The interface contains neither an `eq229` boundary nor a raw polymer-decay
hypothesis. -/
theorem cmp116Eq226PhysicalContour_rawMetricDecay_of_cubeSourceTreeBoundaries
    {nDelta nY M N' Nc L lieDim : ℕ}
    [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {HF : HoleFamily 4 L}
    {z : ℕ → ℕ → Finset (Cube 4 L) → ℂ}
    {E : Type*} [Norm E]
    {ιZ0' : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιZ0' _t _k)]
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Dict : ∀ _t _k,
      PhysicalGaugeCMP116Dictionary 4 (M * N') Nc 4 L lieDim)
    (E0 epsilon1 C1 alpha4 : ℕ → ℕ → ℝ)
    (q : ℕ → ℕ → ℕ)
    (C2 kappa1 delta kappa gamma gk : ℕ → ℕ → ℝ)
    (alpha outerBound outerRate sourceRate : ℕ → ℕ → ℝ)
    (DIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (Cube 4 L)))
    (PIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Finset (Cube 4 L)))
    (Z0Index :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Cube 4 L) →
          Finset (Finset (FinBox 4 N')))
    (Z0PrimeIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Cube 4 L) →
          Finset (FinBox 4 N') → Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := 4) (M := M) (N' := N')
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
        Finset (Cube 4 L) → Finset (Finset (Cube 4 L)))
    (domainFamily :
      ∀ _t _k, Finset (Finset (Cube 4 L)))
    (unionOf :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube 4 L))
    (hunion_nonempty :
      ∀ t k Z, (unionOf t k Z).Nonempty)
    (hdomains :
      ∀ t k Y, Y ∈ domainFamily t k →
        Y.Nonempty ∧ walkConnected (cmp116CubeFaceAdj L) Y)
    (hparts_mem :
      ∀ t k Z D, D ∈ DIndex t k Z →
        DParts t k Z D ∈
          cmp116Eq229ExactUnionDIndex
            (domainFamily t k) (unionOf t k Z))
    (hparts_inj :
      ∀ t k Z D₁, D₁ ∈ DIndex t k Z →
        ∀ D₂, D₂ ∈ DIndex t k Z →
          DParts t k Z D₁ = DParts t k Z D₂ →
            D₁ = D₂)
    (alpha6 : ℕ → ℕ → ℝ)
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k)
    (hdeltaKappa :
      ∀ t k, 0 ≤ (hp t k).delta * (hp t k).kappa)
    (hEq229Cq :
      ∀ t k,
        64 *
          Real.exp
            (-(((hp t k).delta * (hp t k).kappa) / 48)) < 1)
    (hEq229Uniform :
      ∀ t k,
        (alpha6 t k *
            Real.exp
              (3 * ((hp t k).delta * (hp t k).kappa))) *
            24 *
            (1 -
              64 *
                Real.exp
                  (-(((hp t k).delta * (hp t k).kappa) / 48)))⁻¹ ≤
          ((hp t k).delta * (hp t k).kappa) / 2)
    (pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Cube 4 L) → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
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
        sourceMetric DParts alpha6
        (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y)
        pResidualWeight postPSourceWeight postPAmplitude)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube 4 L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube 4 L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube 4 L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube 4 L, Fin lieDim → ℝ =>
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
        4 * kappa0 + 3 + boundedHoleCardinalityTilt 4 B ≤
          balabanCMP116Lemma3DecayRate
            ((hp t k).blockScale) ((hp t k).delta) ((hp t k).kappa))
    (kappa0_nonneg : 0 ≤ kappa0)
    (amplitude_nonneg :
      ∀ t k, 0 ≤ (hp t k).C3 * (hp t k).epsilon1) :
    let physicalActivity :=
      cmp116Eq226PhysicalContourActivityScaleFamily Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
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
    cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_cubeSourceTreeBoundaries
      Dict E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S hp sourceMetric DParts
      domainFamily unionOf hunion_nonempty hdomains
      hparts_mem hparts_inj
      alpha6 halpha6 hdeltaKappa hEq229Cq hEq229Uniform
      pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa postPSourceWeight postPAmplitude pStage postP
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

/-- Terminal bounded-hole KP criterion for the literal equation-(2.26)
contour activity, with the source-tree equation-(2.29) producer.

The caller retains the genuine `P` and post-`P` source boundaries and the
Appendix-F scalar/geometric hypotheses.  No equation-(2.29) boundary, raw
decay estimate, residual estimate, or rooted-remainder identity is supplied. -/
theorem cmp116Eq226PhysicalContour_KPCriterion_of_cubeSourceTreeBoundaries
    {nDelta nY M N' Nc L lieDim : ℕ}
    [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {HF : HoleFamily 4 L}
    {z : ℕ → ℕ → Finset (Cube 4 L) → ℂ}
    {E : Type*} [Norm E]
    {ιZ0' : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιZ0' _t _k)]
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Dict : ∀ _t _k,
      PhysicalGaugeCMP116Dictionary 4 (M * N') Nc 4 L lieDim)
    (E0 epsilon1 C1 alpha4 : ℕ → ℕ → ℝ)
    (q : ℕ → ℕ → ℕ)
    (C2 kappa1 delta kappa gamma gk : ℕ → ℕ → ℝ)
    (alpha outerBound outerRate sourceRate : ℕ → ℕ → ℝ)
    (DIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (Cube 4 L)))
    (PIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Finset (Cube 4 L)))
    (Z0Index :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Cube 4 L) →
          Finset (Finset (FinBox 4 N')))
    (Z0PrimeIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Cube 4 L) →
          Finset (FinBox 4 N') → Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := 4) (M := M) (N' := N')
        (Nc := Nc) (L := L) (lieDim := lieDim) (E := E)
        (ιZ0' := ιZ0' t k)
        (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
        (gamma t k) (gk t k) (alpha t k) (outerBound t k)
        (outerRate t k) (sourceRate t k)
        (OmegaPolymerType HF (z t k)))
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (DParts :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Finset (Cube 4 L)))
    (domainFamily :
      ∀ _t _k, Finset (Finset (Cube 4 L)))
    (unionOf :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube 4 L))
    (hunion_nonempty :
      ∀ t k Z, (unionOf t k Z).Nonempty)
    (hunion_connected :
      ∀ t k Z,
        walkConnected (cmp116CubeFaceAdj L) (unionOf t k Z))
    (hcarrier :
      ∀ t k Z, Z ∈ Λ t k → Z.val ⊆ unionOf t k Z)
    (hdomains :
      ∀ t k Y, Y ∈ domainFamily t k →
        Y.Nonempty ∧ walkConnected (cmp116CubeFaceAdj L) Y)
    (hparts_mem :
      ∀ t k Z D, D ∈ DIndex t k Z →
        DParts t k Z D ∈
          cmp116Eq229ExactUnionDIndex
            (domainFamily t k) (unionOf t k Z))
    (hparts_inj :
      ∀ t k Z D₁, D₁ ∈ DIndex t k Z →
        ∀ D₂, D₂ ∈ DIndex t k Z →
          DParts t k Z D₁ = DParts t k Z D₂ →
            D₁ = D₂)
    (alpha6 : ℕ → ℕ → ℝ)
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k)
    (hdeltaKappa :
      ∀ t k, 0 ≤ (hp t k).delta * (hp t k).kappa)
    (hEq229Cq :
      ∀ t k,
        64 *
          Real.exp
            (-(((hp t k).delta * (hp t k).kappa) / 48)) < 1)
    (hEq229Uniform :
      ∀ t k,
        (alpha6 t k *
            Real.exp
              (3 * ((hp t k).delta * (hp t k).kappa))) *
            24 *
            (1 -
              64 *
                Real.exp
                  (-(((hp t k).delta * (hp t k).kappa) / 48)))⁻¹ ≤
          ((hp t k).delta * (hp t k).kappa) / 2)
    (pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Cube 4 L) → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
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
        (fun t k Z => cmp116CubeSourceTreeMetric (unionOf t k Z))
        DParts alpha6
        (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y)
        pResidualWeight postPSourceWeight postPAmplitude)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube 4 L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube 4 L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube 4 L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube 4 L, Fin lieDim → ℝ =>
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
    (rate_margin :
      ∀ t k,
        24 * (4 * kappa0 + 3 + boundedHoleCardinalityTilt 4 B) ≤
          balabanCMP116Lemma3DecayRate
            ((hp t k).blockScale) ((hp t k).delta) ((hp t k).kappa))
    (ν : ℕ → ℕ → Measure (Fin lieDim → ℝ))
    (g : ℕ → ℝ)
    (t0 kScale : ℕ)
    (C Hscale c0 s A : ℝ)
    (hkappa0 : 0 < kappa0)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hamplitude_one :
      ∀ t k,
        ((hp t k).C3 * (hp t k).epsilon1) *
            Real.exp
              (24 *
                (4 * kappa0 + 3 +
                  boundedHoleCardinalityTilt 4 B)) ≤
          1)
    (hhalf : ∀ t k,
      appendixFSecondUrsellLeafConstant 4 kappa0 *
          (2 *
            (((hp t k).C3 * (hp t k).epsilon1) *
              Real.exp
                (24 *
                  (4 * kappa0 + 3 +
                    boundedHoleCardinalityTilt 4 B))) *
            appendixFHoleRootSumConstant 4 kappa0) ≤ 1 / 2)
    (hprofile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant 4 kappa0 *
          (((hp t k).C3 * (hp t k).epsilon1) *
            Real.exp
              (24 *
                (4 * kappa0 + 3 +
                  boundedHoleCardinalityTilt 4 B))) *
            appendixFHoleRootSumConstant 4 kappa0 ≤
        C * Hscale * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (amplitude_nonneg :
      ∀ t k, 0 ≤ (hp t k).C3 * (hp t k).epsilon1)
    (hdisj :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (hnoedges : noEdgesBetweenHoles (cubeAdj 4 L) HF.holes)
    (hholes_ne : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hB : ∀ H0 ∈ HF.holes, H0.card ≤ B)
    (hCq : ((3 ^ 4 : ℕ) : ℝ) ^ 2 *
      (Real.exp (-kappa0) * 2 ^ (3 ^ 4 + 1)) < 1)
    (hAmp0 :
      0 ≤ C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
        g kScale ^ kappa0)
    (hA0 : 0 ≤ A)
    (hA : Real.exp s *
        (C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
          g kScale ^ kappa0) ≤ A)
    (hsmall : A *
      (1 - ((3 ^ 4 : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ 4 + 1)))⁻¹ ≤ 1) :
    let physicalActivity :=
      cmp116Eq226PhysicalContourActivityScaleFamily Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
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
  let physicalActivity :=
    cmp116Eq226PhysicalContourActivityScaleFamily Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S
  let sourceMetric :
      ∀ t k, OmegaPolymerType HF (z t k) → ℕ :=
    fun t k Z => cmp116CubeSourceTreeMetric (unionOf t k Z)
  let estimate :
      CMP116Lemma3ActivityEstimateScaleFamily physicalActivity sourceMetric
        (fun t k => (hp t k).blockScale)
        (fun t k => (hp t k).C3)
        (fun t k => (hp t k).epsilon1)
        (fun t k => (hp t k).delta)
        (fun t k => (hp t k).kappa) :=
    cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_cubeSourceTreeBoundaries
      Dict E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S hp sourceMetric DParts
      domainFamily unionOf hunion_nonempty hdomains
      hparts_mem hparts_inj
      alpha6 halpha6 hdeltaKappa hEq229Cq hEq229Uniform
      pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa postPSourceWeight postPAmplitude pStage postP
  simpa [physicalActivity] using
    (cmp116Lemma3LocalizedCubeActivityFamily_KPCriterion_boundedHoles_of_cubeSourceTreeMetric
      Λ Dict physicalActivity unionOf hcarrier hunion_nonempty hunion_connected
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      B kappa0 Omega activeSupport activity_stronglyMeasurable
      spectatorSupport_subset fluctuationSupport_subset estimate
      rate_margin ν g t0 kScale C Hscale c0 s A
      hkappa0 hν hamplitude_one hhalf hprofile amplitude_nonneg
      hdisj hnoedges hholes_ne hB hCq hAmp0 hA0 hA hsmall)

/-- Terminal physical `hRpoly` scalar decay for the literal equation-(2.26)
contour activity with the source-tree equation-(2.29) producer.

Both the raw activity decay and the rooted canonical `H#` remainder are
constructed internally. -/
theorem cmp116Eq226PhysicalContour_singleScaleUVDecay_of_cubeSourceTreeBoundaries
    {nDelta nY M N' Nc L lieDim : ℕ}
    [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {HF : HoleFamily 4 L}
    {z : ℕ → ℕ → Finset (Cube 4 L) → ℂ}
    (zCarrier : Finset (Cube 4 L) → ℂ)
    (r : Cube 4 L)
    {E : Type*} [Norm E]
    {ιZ0' : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιZ0' _t _k)]
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Dict : ∀ _t _k,
      PhysicalGaugeCMP116Dictionary 4 (M * N') Nc 4 L lieDim)
    (E0 epsilon1 C1 alpha4 : ℕ → ℕ → ℝ)
    (q : ℕ → ℕ → ℕ)
    (C2 kappa1 delta kappa gamma gk : ℕ → ℕ → ℝ)
    (alpha outerBound outerRate sourceRate : ℕ → ℕ → ℝ)
    (DIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Finset (Cube 4 L)))
    (PIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Finset (Cube 4 L)))
    (Z0Index :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Cube 4 L) →
          Finset (Finset (FinBox 4 N')))
    (Z0PrimeIndex :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Cube 4 L) →
          Finset (FinBox 4 N') → Finset (ιZ0' t k))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := 4) (M := M) (N' := N')
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
        Finset (Cube 4 L) → Finset (Finset (Cube 4 L)))
    (domainFamily :
      ∀ _t _k, Finset (Finset (Cube 4 L)))
    (unionOf :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube 4 L))
    (hunion_nonempty :
      ∀ t k Z, (unionOf t k Z).Nonempty)
    (hdomains :
      ∀ t k Y, Y ∈ domainFamily t k →
        Y.Nonempty ∧ walkConnected (cmp116CubeFaceAdj L) Y)
    (hparts_mem :
      ∀ t k Z D, D ∈ DIndex t k Z →
        DParts t k Z D ∈
          cmp116Eq229ExactUnionDIndex
            (domainFamily t k) (unionOf t k Z))
    (hparts_inj :
      ∀ t k Z D₁, D₁ ∈ DIndex t k Z →
        ∀ D₂, D₂ ∈ DIndex t k Z →
          DParts t k Z D₁ = DParts t k Z D₂ →
            D₁ = D₂)
    (alpha6 : ℕ → ℕ → ℝ)
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k)
    (hdeltaKappa :
      ∀ t k, 0 ≤ (hp t k).delta * (hp t k).kappa)
    (hEq229Cq :
      ∀ t k,
        64 *
          Real.exp
            (-(((hp t k).delta * (hp t k).kappa) / 48)) < 1)
    (hEq229Uniform :
      ∀ t k,
        (alpha6 t k *
            Real.exp
              (3 * ((hp t k).delta * (hp t k).kappa))) *
            24 *
            (1 -
              64 *
                Real.exp
                  (-(((hp t k).delta * (hp t k).kappa) / 48)))⁻¹ ≤
          ((hp t k).delta * (hp t k).kappa) / 2)
    (pResidualWeight :
      ∀ t k, OmegaPolymerType HF (z t k) →
        Finset (Cube 4 L) → Finset (Cube 4 L) → ℝ)
    (pStageBlockScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℕ → ℕ → ℝ)
    (postPSourceWeight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ)
    (postPAmplitude : ℕ → ℕ → ℝ)
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
        sourceMetric DParts alpha6
        (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y)
        pResidualWeight postPSourceWeight postPAmplitude)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube 4 L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube 4 L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube 4 L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube 4 L, Fin lieDim → ℝ =>
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
        4 * kappa0 + 3 + boundedHoleCardinalityTilt 4 B ≤
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
      appendixFSecondUrsellLeafConstant 4 kappa0 *
          (2 * ((hp t k).C3 * (hp t k).epsilon1) *
            appendixFHoleRootSumConstant 4 kappa0) ≤ 1 / 2)
    (hprofile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant 4 kappa0 *
          ((hp t k).C3 * (hp t k).epsilon1) *
            appendixFHoleRootSumConstant 4 kappa0 ≤
        C * Hbar * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (hdisj :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (hnoedges : noEdgesBetweenHoles (cubeAdj 4 L) HF.holes)
    (hholes_ne : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hCq : ((3 ^ 4 : ℕ) : ℝ) ^ 2 *
      (Real.exp (-kappa0) * 2 ^ (3 ^ 4 + 1)) < 1) :
    let physicalActivity :=
      cmp116Eq226PhysicalContourActivityScaleFamily Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
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
    cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_cubeSourceTreeBoundaries
      Dict E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S hp sourceMetric DParts
      domainFamily unionOf hunion_nonempty hdomains
      hparts_mem hparts_inj
      alpha6 halpha6 hdeltaKappa hEq229Cq hEq229Uniform
      pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa postPSourceWeight postPAmplitude pStage postP
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

end YangMills.RG

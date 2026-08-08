/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226VariableArityContourActivityBoundary
import YangMills.RG.BalabanCMP116Eq229CubeTreeMetricScaleBoundary

/-!
# Variable-arity contour terms with the physical source-tree metric

This module composes the term-dependent Cauchy arities of the literal
equation-(2.26) contour source with the source-tree construction of equation
(2.29).  Neither `nDelta` nor `nY` is fixed globally: both remain internal to
each contour term.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Literal variable-arity equation-(2.26) contour activity estimate with
equation (2.29) constructed from an injective exact-union domain-family
dictionary. -/
def cmp116Eq226VariableArityContour_lemma3ActivityEstimate_of_cubeSourceTreeBoundaries
    {M N' Nc L lieDim : ℕ}
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
      CMP116Eq226VariableArityContourTermSourceFamily
        (d := 4) (M := M) (N' := N') (Nc := Nc) (L := L)
        (lieDim := lieDim) (E := E) (ιZ0' := ιZ0' t k)
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
        (cmp116Eq226VariableArityContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa)
    (postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary hp
        (cmp116Eq226VariableArityContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S)
        sourceMetric DParts alpha6
        (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y)
        pResidualWeight postPSourceWeight postPAmplitude) :
    CMP116Lemma3ActivityEstimateScaleFamily
      (cmp116Eq226VariableArityContourActivityScaleFamily Dict
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
    cmp116Eq226VariableArityContourResummationScaleFamily Dict
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
    CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries
      eq229 pStage postP
      (cmp116Eq226VariableArityContour_activityTermwiseScaleBoundary Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
        DIndex PIndex Z0Index Z0PrimeIndex S)

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalContourSourceTreeBoundary
import YangMills.RG.BalabanCMP116Eq237
import YangMills.RG.BalabanCMP116Eq231PBondFactorBridge

/-!
# Literal CMP116 contour estimate through equations (2.29), (2.31), and (2.37)

This module constructs both remaining finite-resummation boundaries used by
the source-tree contour route.  The `P` stage is generated from the explicit
equation-(2.31) bond boundary, and the post-`P` stage is generated from the
fixed-`Z0'` equation-(2.37) estimate and its final source summation.

The pointwise equation-(2.31) residual estimate is stated directly against the
literal equation-(2.26) `P` factor.  Endpoint coverage supplies the gap/cardinal
comparison, so no abstract geometric weight or comparison theorem remains in
the terminal interface.  The fixed-`Z0'` equation-(2.37) estimate, final source
sum, and scalar majorization remain visible genuine analytic inputs.
-/

namespace YangMills.RG

/-- Literal equation-(2.26) contour activity estimate with the source-tree
equation-(2.29), equation-(2.31), and equation-(2.37) producers composed
internally. -/
def cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_cubeSourceTree_eq231_eq237
    {nDelta nY M N' Nc L lieDim : ℕ}
    [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E : Type*} [Norm E]
    {σ ιZ0' ιC β : ℕ → ℕ → Type*}
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
      ∀ t k, σ t k → Finset (Cube 4 L) → Finset (Cube 4 L) → ℝ)
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa gamma2 : ℕ → ℕ → ℝ)
    (eq231Boundary :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
          (DIndex t k) (PIndex t k) (eq231LocalizationScale t k))
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hpointwise :
      ∀ t k Z D, D ∈ DIndex t k Z →
        ∀ P, P ∈ PIndex t k Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              cmp116Eq226PBondFactor
                (gamma2 t k) (hp t k).epsilon1 (gk t k)
                ((eq231Boundary t k).pBonds Z D P))
    (hsourceBracket :
      ∀ t k,
        4 * ((eq231LocalizationScale t k : ℝ) ^ 4) *
            Real.exp
              (-(gamma2 t k * (hp t k).epsilon1 ^ 2 /
                  (10 * (gk t k) ^ 2))) ≤
          gamma2 t k * (hp t k).epsilon1 ^ 2 /
            (20 * (gk t k) ^ 2))
    (hgapCard :
      ∀ t k Z D, D ∈ DIndex t k Z →
        ∀ P, P ∈ PIndex t k Z D →
          (eq231Boundary t k).gapMass Z D ≤
            2 * (((eq231Boundary t k).pBonds Z D P).card : ℝ))
    (hEq231Target :
      ∀ t k,
        1 ≤ pEntropyConstant t k * Real.exp (5 * pStageKappa t k))
    (hEq231Small :
      ∀ t k,
        2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
            pEntropyConstant t k * epsilon2 t k *
              Real.exp (5 * pStageKappa t k) ≤ 1)
    (hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P)
    (localizationScale : ℕ → ℕ → ℕ)
    (C237 Calpha5 alpha5 : ℕ → ℕ → ℝ)
    (sourceCard : ∀ t k, σ t k → ℕ)
    (gapCard : ∀ t k, σ t k → ιZ0' t k → ℕ)
    (components :
      ∀ t k, σ t k → ιZ0' t k → Finset (ιC t k))
    (componentMetric :
      ∀ t k, σ t k → ιZ0' t k → ιC t k → ℕ)
    (sourceZ0PrimeIndex :
      ∀ t k, σ t k → Finset (ιZ0' t k))
    (postPSourceWeight : ∀ t k, σ t k → ℝ)
    (hC237_nonneg : ∀ t k, 0 ≤ C237 t k)
    (hindex :
      let R :=
        cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          cmp116Eq237Z0PrimeIndex (R t k) Z D P ⊆
            sourceZ0PrimeIndex t k Z)
    (heq237_fixed :
      let R :=
        cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0',
            Z0' ∈ cmp116Eq237Z0PrimeIndex (R t k) Z D P →
              Finset.sum
                  (cmp116Eq237Z0Fiber (R t k) Z D P Z0')
                  (fun Z0 => (R t k).termWeight Z D P Z0 Z0') ≤
                cmp116Eq229WeightedPWeight
                  (DParts t k)
                  (alpha6 t k)
                  (hp t k).delta
                  (hp t k).kappa
                  (fun _Z Y => cmp116CubeSourceTreeMetric Y)
                  (pResidualWeight t k)
                  Z D P *
                  cmp116Eq237FixedZ0PrimeWeight
                    (hp t k)
                    (localizationScale t k)
                    (C237 t k) (Calpha5 t k) (alpha5 t k)
                    (sourceCard t k) (gapCard t k)
                    (components t k) (componentMetric t k) Z Z0')
    (hpost_eq237 :
      ∀ t k Z,
        Finset.sum (sourceZ0PrimeIndex t k Z) (fun Z0' =>
            cmp116Eq237FixedZ0PrimeWeight
              (hp t k)
              (localizationScale t k)
              (C237 t k) (Calpha5 t k) (alpha5 t k)
              (sourceCard t k) (gapCard t k)
              (components t k) (componentMetric t k) Z Z0') ≤
          cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k) (hp t k).epsilon2 *
            postPSourceWeight t k Z)
    (hmajorization :
      CMP116Eq237MajorizationBoundary
        hp sourceMetric postPSourceWeight
        (fun t k =>
          cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k) (hp t k).epsilon2)) :
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
  let eq229 :
      CMP116Lemma3Eq229ScaleBoundary hp R DParts alpha6
        (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y) :=
    CMP116Lemma3Eq229ScaleBoundary.of_cubeSourceTreeMetric_exactUnionInjection
      hp R DParts domainFamily unionOf hunion_nonempty hdomains
      hparts_mem hparts_inj
      alpha6 halpha6 hdeltaKappa hEq229Cq hEq229Uniform
  let pStage :
      CMP116Lemma3PStageSourceScaleBoundary
        R pResidualWeight pStageBlockScale pEntropyConstant
        epsilon2 pStageKappa :=
    CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise
      R pResidualWeight
      (fun t k Z D P =>
        cmp116Eq226PBondFactor
          (gamma2 t k) (hp t k).epsilon1 (gk t k)
          ((eq231Boundary t k).pBonds Z D P))
      pStageBlockScale eq231LocalizationScale
      pEntropyConstant epsilon2 pStageKappa gamma2
      (fun t k => (hp t k).epsilon1) gk
      eq231Boundary hepsilon2_nonneg hpointwise hsourceBracket
      (fun t k Z D hD P hP => by
        have hrate_nonneg :
            0 ≤
              cmp116Eq226PSourceRate
                (gamma2 t k) (hp t k).epsilon1 (gk t k) :=
          cmp116Eq226PSourceRate_nonneg_of_sourceBracket
            (eq231LocalizationScale t k)
            (gamma2 t k) (hp t k).epsilon1 (gk t k)
            (hsourceBracket t k)
        simpa [cmp116Eq226PSourceRate] using
          cmp116Eq226PBondFactor_le_eq231PWeight_of_gapMass_le_two_mul_card
            (gamma2 t k) (hp t k).epsilon1 (gk t k)
            (eq231Boundary t k).gapMass
            (eq231Boundary t k).pBonds Z D P
            hrate_nonneg (hgapCard t k Z D hD P hP))
      hEq231Target hEq231Small hpResidual_nonneg
  let postP :
      CMP116Lemma3WeightedPostPSourceScaleBoundary hp R sourceMetric
        DParts alpha6
        (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y)
        pResidualWeight postPSourceWeight
        (fun t k =>
          cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k) (hp t k).epsilon2) :=
    CMP116Lemma3WeightedPostPSourceScaleBoundary.of_eq237
      hp R sourceMetric DParts alpha6
      (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y)
      pResidualWeight localizationScale C237 Calpha5 alpha5
      sourceCard gapCard components componentMetric sourceZ0PrimeIndex
      postPSourceWeight hC237_nonneg halpha6 hpResidual_nonneg
      hindex heq237_fixed hpost_eq237 hmajorization
  exact
    cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_cubeSourceTreeBoundaries
      Dict E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S hp sourceMetric DParts
      domainFamily unionOf hunion_nonempty hdomains
      hparts_mem hparts_inj
      alpha6 halpha6 hdeltaKappa hEq229Cq hEq229Uniform
      pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa postPSourceWeight
      (fun t k =>
        cmp116Eq237Amplitude
          (hp t k).blockScale (C237 t k) (hp t k).epsilon2)
      pStage postP

end YangMills.RG

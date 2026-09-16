/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalContourSourceTreeBoundary
import YangMills.RG.BalabanCMP116Eq237
import YangMills.RG.BalabanCMP116Eq231PBondFactorBridge
import YangMills.RG.BalabanCMP116Eq228ShiftedCardRoute
import YangMills.RG.BalabanCMP116Eq237FiberEntropyBoundary
import YangMills.RG.BalabanCMP116Eq226DomainDictionary
import YangMills.RG.BalabanCMP116Eq226ScalarDictionaries
import YangMills.RG.BalabanCMP116Eq237ComponentFiberEncoding
import YangMills.RG.BalabanCMP116Eq237ComponentFamilySum
import YangMills.RG.BalabanCMP116Eq237RootedComponentSum
import YangMills.RG.BalabanCMP116Eq237GapComponentCovering
import YangMills.RG.BalabanCMP116Eq237SplitRateHierarchy
import YangMills.RG.BalabanCMP116Eq237SourceFinalSum
import YangMills.RG.BalabanCMP116Eq234PhysicalGapEncoding

/-!
# Literal CMP116 contour estimate through equations (2.29), (2.31), and (2.37)

This module constructs both remaining finite-resummation boundaries used by
the source-tree contour route.  The `P` stage is generated from the explicit
equation-(2.31) bond boundary, and the post-`P` stage is generated from the
fixed-`Z0'` equation-(2.37) estimate and its final source summation.

The pointwise equation-(2.31) residual estimate is stated directly against the
literal equation-(2.26) `P` factor.  Endpoint coverage supplies the gap/cardinal
comparison, so no abstract geometric weight or comparison theorem remains in
the terminal interface.  The fixed-`Z0'` equation-(2.37) estimate is then
summed internally through component families and rooted cube animals.  The
remaining inputs are source dictionaries for those components, their
gap--metric covering, and the explicit scalar rate budget; no post-summation
majorant is supplied by the caller.
-/

namespace YangMills.RG

/-- Literal post-domain residual used by the physical contour scale family.
The shifted cardinal metric is the convention-robust lower metric generated
from the physical source-tree comparison. -/
noncomputable def cmp116Eq228PhysicalPResidualWeight
    {M L : ℕ} {ιP : Type*}
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (unionOf : Finset (Cube 4 L))
    (gamma2 gapEpsilon1 gk : ℝ)
    (pBonds : Finset ιP) : ℝ :=
  cmp116Eq228PResidualWeight
    E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 delta kappa
    (cmp116Eq229ShiftedCardMetric unionOf : ℝ)
    gamma2 gapEpsilon1 gk pBonds

/-- Literal equation-(2.26) contour activity estimate with the source-tree
equation-(2.29), equation-(2.31), and equation-(2.37) producers composed
internally. -/
def cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_cubeSourceTree_eq231_eq237
    {nDelta nY M N' Nc L lieDim : ℕ}
    [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {E : Type*} [Norm E]
    {σ ιC ιGap ιChoice β : ℕ → ℕ → Type*}
    [∀ _t _k, DecidableEq (ιGap _t _k)]
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
        Finset (FinBox 4 N') → Finset (Finset (ιGap t k)))
    (S : ∀ t k,
      CMP116Eq226PhysicalContourTermSourceFamily
        (nDelta := nDelta) (nY := nY) (d := 4) (M := M) (N' := N')
        (Nc := Nc) (L := L) (lieDim := lieDim) (E := E)
        (ιZ0' := Finset (ιGap t k))
        (Dict t k) (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (q t k) (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
        (gamma t k) (gk t k) (alpha t k) (outerBound t k)
        (outerRate t k) (sourceRate t k) (σ t k))
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (DParts :
      ∀ t k, σ t k → Finset (Cube 4 L) →
        Finset (Finset (Cube 4 L)))
    (domainFamily :
      ∀ _t _k, Finset (Finset (Cube 4 L)))
    (unionOf :
      ∀ t k, σ t k → Finset (Cube 4 L))
    (hunion_nonempty :
      ∀ t k Z, (unionOf t k Z).Nonempty)
    (hunion_connected :
      ∀ t k Z,
        walkConnected (cmp116CubeFaceAdj L) (unionOf t k Z))
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
    (halpha6 : ∀ t k, 0 < alpha6 t k)
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
    (pStageBlockScale eq231LocalizationScale : ℕ → ℕ → ℕ)
    (pEntropyConstant epsilon2 pStageKappa gamma2 : ℕ → ℕ → ℝ)
    (eq231Boundary :
      ∀ t k,
        CMP116Eq231PBondBoundary
          (β := β t k)
          (DIndex t k) (PIndex t k) (eq231LocalizationScale t k))
    (hepsilon2_nonneg : ∀ t k, 0 ≤ epsilon2 t k)
    (hE0_nonneg : ∀ t k, 0 ≤ E0 t k)
    (hepsilon1_nonneg : ∀ t k, 0 ≤ epsilon1 t k)
    (hC1_nonneg : ∀ t k, 0 ≤ C1 t k)
    (halpha4_pos : ∀ t k, 0 < alpha4 t k)
    (hdelta_nonneg : ∀ t k, 0 ≤ delta t k)
    (hkappa_nonneg : ∀ t k, 0 ≤ kappa t k)
    (hdelta_le_one_sixteen :
      ∀ t k, delta t k ≤ (1 : ℝ) / 16)
    (hdelta_source : ∀ t k, delta t k = (hp t k).delta)
    (hkappa_source : ∀ t k, kappa t k = (hp t k).kappa)
    (hepsilon2_source :
      ∀ t k,
        epsilon2 t k =
          cmp116Eq228SourceCoefficient
            (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
            (alpha6 t k) M (q t k) (C2 t k) (kappa1 t k))
    (hhp_epsilon2_source :
      ∀ t k, (hp t k).epsilon2 = epsilon2 t k)
    (hEq228Small :
      ∀ t k,
        cmp116Eq228SourceCoefficient
              (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
              (alpha6 t k) M (q t k) (C2 t k) (kappa1 t k) *
            Real.exp (5 * kappa t k) ≤
          1)
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
    (localizationScale : ℕ → ℕ → ℕ)
    (hlocalizationScale_ne :
      ∀ t k, localizationScale t k ≠ 0)
    (C237 Calpha5 alpha5 : ℕ → ℕ → ℝ)
    (sourceCard : ∀ t k, σ t k → ℕ)
    (gapCarrier : ∀ t k, σ t k → Finset (ιGap t k))
    (components :
      ∀ t k, σ t k → Finset (ιGap t k) → Finset (ιC t k))
    (componentMetric :
      ∀ t k, σ t k → Finset (ιGap t k) → ιC t k → ℕ)
    (sourceZ0PrimeIndex :
      ∀ t k, σ t k → Finset (Finset (ιGap t k)))
    (hsourceZ0Prime_sub :
      ∀ t k Z Z0',
        Z0' ∈ sourceZ0PrimeIndex t k Z →
          Z0' ⊆ gapCarrier t k Z)
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
    (hgamma2_source : ∀ t k, gamma2 t k = gamma t k)
    (hepsilon1_source :
      ∀ t k, (hp t k).epsilon1 = epsilon1 t k)
    (hkappa1_source :
      ∀ t k, (hp t k).kappa1 = kappa1 t k)
    (hvolumeTarget_nonneg :
      ∀ t k, 0 ≤ Calpha5 t k * alpha5 t k)
    (hscalar_eq226_fixed :
      let R :=
        cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0',
            Z0' ∈ cmp116Eq237Z0PrimeIndex (R t k) Z D P →
              ∀ Z0,
                Z0 ∈ cmp116Eq237Z0Fiber (R t k) Z D P Z0' →
                  let s := S t k Z D P Z0 Z0'
                  (∃ domainCubes : Fin nY → Finset (Cube 4 L),
                    Function.Injective domainCubes ∧
                    (∀ i,
                      s.domainMetric i =
                        cmp116CubeSourceTreeMetric (domainCubes i)) ∧
                    DParts t k Z D =
                      cmp116Eq226SourceDomainParts domainCubes) ∧
                  ((eq231Boundary t k).pBonds Z D P).card = P.card ∧
                  localizationScale t k * 1 = s.gapScale * M ∧
                  cmp116Eq234PhysicalGapCard
                      (localizationScale t k)
                      (gapCarrier t k Z) Z0' =
                    s.gapCard ∧
                  s.volumeRate * alpha t k ≤
                    Calpha5 t k * alpha5 t k ∧
                  Z0.card ≤ sourceCard t k Z)
    (hcomponentEncoding :
      let R :=
        cmp116Eq226PhysicalContourResummationScaleFamily Dict
          E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
          alpha outerBound outerRate sourceRate
          DIndex PIndex Z0Index Z0PrimeIndex S
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        ∀ P, P ∈ (R t k).PIndex Z D →
          ∀ Z0',
            Z0' ∈ cmp116Eq237Z0PrimeIndex (R t k) Z D P →
              CMP116Eq237ComponentFiberEncoding
                (ιChoice := ιChoice t k)
                (cmp116Eq237Z0Fiber (R t k) Z D P Z0')
                (components t k Z Z0')
                (fun Zi =>
                  cmp116Eq237Amplitude
                      (hp t k).blockScale (C237 t k)
                      (hp t k).epsilon2 *
                    Real.exp
                      (-(((1 - 7 * (hp t k).delta) / 2) *
                        ((hp t k).blockScale : ℝ) *
                        (hp t k).kappa *
                        (componentMetric t k Z Z0' Zi : ℝ)))))
    (hcomponentFamilyEncoding :
      ∀ t k Z,
        CMP116Eq237ComponentFamilyEncoding
          (sourceZ0PrimeIndex t k Z)
          (components t k Z)
          (fun Z0' Zi =>
            cmp116Eq237Amplitude
                (hp t k).blockScale (C237 t k)
                (hp t k).epsilon2 *
              Real.exp
                (-(cmp116Eq237ComponentEntropyRate (hp t k) *
                  (componentMetric t k Z Z0' Zi : ℝ)))))
    (hcomponentFamilies_nonempty :
      ∀ t k Z Z0',
        Z0' ∈ sourceZ0PrimeIndex t k Z →
          (components t k Z Z0').Nonempty)
    (componentAtomMetric :
      ∀ t k, σ t k → ιC t k → ℕ)
    (componentCarrier :
      ∀ t k, σ t k → Finset (Cube 4 L))
    (sourceCardScale gapCarrierScale : ℕ → ℕ → ℝ)
    (hsourceCardScale_nonneg :
      ∀ t k, 0 ≤ sourceCardScale t k)
    (hgapCarrierScale_nonneg :
      ∀ t k, 0 ≤ gapCarrierScale t k)
    (hsourceCard_volume :
      ∀ t k Z,
        (sourceCard t k Z : ℝ) ≤
          sourceCardScale t k * ((unionOf t k Z).card : ℝ))
    (hcomponentCarrier_sub :
      ∀ t k Z,
        componentCarrier t k Z ⊆ unionOf t k Z)
    (hgapCarrier_volume :
      ∀ t k Z,
        ((gapCarrier t k Z).card : ℝ) ≤
          gapCarrierScale t k * ((unionOf t k Z).card : ℝ))
    (gapCost : ℕ → ℕ → ℝ)
    (hgapComponentCovering :
      ∀ t k,
        CMP116Eq237GapComponentCovering
          (fun Z => cmp116CubeSourceTreeMetric (unionOf t k Z))
          (sourceZ0PrimeIndex t k)
          (fun Z Z0' =>
            cmp116Eq234PhysicalGapCard
              (localizationScale t k)
              (gapCarrier t k Z) Z0')
          (components t k)
          (componentMetric t k)
          (localizationScale t k)
          (gapCost t k))
    (hrootedComponentDictionary :
      ∀ t k Z,
        let E := hcomponentFamilyEncoding t k Z
        CMP116Eq237RootedCubeComponentDictionary
          E.componentUniverse E.atomWeight
          (componentAtomMetric t k Z)
          (componentCarrier t k Z)
          (cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k)
            (hp t k).epsilon2)
          (cmp116Eq237ComponentEntropyRate (hp t k)))
    (hblockScale_four :
      ∀ t k, 4 ≤ (hp t k).blockScale)
    (hgapPays :
      ∀ t k,
        cmp116Eq237ComponentTransportRate (hp t k) *
            gapCost t k ≤
          ((hp t k).kappa1 - 1) / 2)
    (hpostRateBudget :
      ∀ t k,
        Real.exp (-(((hp t k).kappa1 - 1) / 2)) *
              (24 * gapCarrierScale t k) +
            Calpha5 t k * alpha5 t k *
              (24 * sourceCardScale t k) +
            cmp116Eq237RootedComponentLinearRate
              24
              (cmp116Eq237ComponentEntropyRate (hp t k)) +
            cmp116Eq237Amplitude
                (hp t k).blockScale (C237 t k)
                (hp t k).epsilon2 *
              cmp116Eq237RootedComponentLinearRate
                24
                (cmp116Eq237ComponentEntropyRate (hp t k)) ≤
          cmp116Eq237ComponentEntropyRate (hp t k))
    (hC3_source_shifted :
      ∀ t k,
        (hp t k).C3 =
          cmp116Lemma3C3OfShiftedSourceConstants
            (hp t k).blockScale
            (C237 t k) (E0 t k) (C1 t k)
            (alpha4 t k) (alpha6 t k) (M : ℝ)
            (C2 t k) (kappa1 t k)
            (Real.exp (-(((hp t k).kappa1 - 1) / 2)) *
                    (24 * gapCarrierScale t k) +
                Calpha5 t k * alpha5 t k *
                    (24 * sourceCardScale t k) +
                cmp116Eq237RootedComponentLinearRate
                  24
                  (cmp116Eq237ComponentEntropyRate (hp t k)) +
                cmp116Eq237Amplitude
                    (hp t k).blockScale (C237 t k)
                    (hp t k).epsilon2 *
                  cmp116Eq237RootedComponentLinearRate
                    24
                    (cmp116Eq237ComponentEntropyRate (hp t k)))
            (q t k)) :
    CMP116Lemma3ActivityEstimateScaleFamily
      (cmp116Eq226PhysicalContourActivityScaleFamily Dict
        E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
        alpha outerBound outerRate sourceRate
        DIndex PIndex Z0Index Z0PrimeIndex S)
      (fun t k Z =>
        cmp116CubeSourceTreeMetric (unionOf t k Z))
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa) := by
  have hfourDelta : ∀ t k, 4 * delta t k ≤ 1 :=
    fun t k =>
      cmp116Eq237_four_delta_le_one_of_delta_le_one_sixteen
        (hdelta_le_one_sixteen t k)
  have hfifteenDelta : ∀ t k, 15 * delta t k ≤ 2 :=
    fun t k =>
      cmp116Eq237_fifteen_delta_le_two_of_delta_le_one_sixteen
        (hdelta_le_one_sixteen t k)
  have hblockScale_two : ∀ t k, 2 ≤ (hp t k).blockScale :=
    fun t k => by
      have hfour := hblockScale_four t k
      omega
  let sourceMetric : ∀ t k, σ t k → ℕ :=
    fun t k Z => cmp116CubeSourceTreeMetric (unionOf t k Z)
  let postLinearRate : ℕ → ℕ → ℝ :=
    fun t k =>
      Real.exp (-(((hp t k).kappa1 - 1) / 2)) *
          (24 * gapCarrierScale t k) +
        Calpha5 t k * alpha5 t k *
          (24 * sourceCardScale t k) +
        cmp116Eq237RootedComponentLinearRate
          24
          (cmp116Eq237ComponentEntropyRate (hp t k)) +
        cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k)
            (hp t k).epsilon2 *
          cmp116Eq237RootedComponentLinearRate
            24
            (cmp116Eq237ComponentEntropyRate (hp t k))
  have hsourceCard_linear :
      ∀ t k Z,
        (sourceCard t k Z : ℝ) ≤
          (24 * sourceCardScale t k) *
            ((sourceMetric t k Z : ℝ) + 1) := by
    intro t k Z
    simpa [sourceMetric] using
      cmp116Cube_scaledCard_le_sourceTreeMetric_add_one
        (unionOf t k Z)
        (hunion_nonempty t k Z)
        (hunion_connected t k Z)
        (sourceCard t k Z)
        (sourceCardScale t k)
        (hsourceCardScale_nonneg t k)
        (hsourceCard_volume t k Z)
  have hgapCarrier_linear :
      ∀ t k Z,
        ((gapCarrier t k Z).card : ℝ) ≤
          (24 * gapCarrierScale t k) *
            ((sourceMetric t k Z : ℝ) + 1) := by
    intro t k Z
    simpa [sourceMetric] using
      cmp116Cube_scaledCard_le_sourceTreeMetric_add_one
        (unionOf t k Z)
        (hunion_nonempty t k Z)
        (hunion_connected t k Z)
        (gapCarrier t k Z).card
        (gapCarrierScale t k)
        (hgapCarrierScale_nonneg t k)
        (hgapCarrier_volume t k Z)
  have hcomponentCarrier_linear :
      ∀ t k Z,
        ((componentCarrier t k Z).card : ℝ) ≤
          24 * ((sourceMetric t k Z : ℝ) + 1) := by
    intro t k Z
    simpa [sourceMetric] using
      cmp116Cube_subset_card_le_twentyFour_mul_sourceTreeMetric_add_one
        (unionOf t k Z)
        (componentCarrier t k Z)
        (hunion_nonempty t k Z)
        (hunion_connected t k Z)
        (hcomponentCarrier_sub t k Z)
  let R :=
    cmp116Eq226PhysicalContourResummationScaleFamily Dict
      E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S
  let gapCard :
      ∀ t k, σ t k → Finset (ιGap t k) → ℕ :=
    fun t k Z Z0' =>
      cmp116Eq234PhysicalGapCard
        (localizationScale t k) (gapCarrier t k Z) Z0'
  let postPSourceWeight : ∀ t k, σ t k → ℝ :=
    fun t k Z =>
      Real.exp
          (-(cmp116Eq237ComponentTransportRate (hp t k) *
            (sourceMetric t k Z : ℝ))) *
        cmp116Eq237SourcePostComponentBudget
          (cmp116Eq226GaussianVolumeFactor
            (Calpha5 t k) (alpha5 t k) (sourceCard t k Z))
          (cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k)
            (hp t k).epsilon2)
          (hp t k).kappa1
          (gapCarrier t k Z).card
          (componentCarrier t k Z).card
          (cmp116Eq237ComponentEntropyRate (hp t k))
  let pResidualWeight :
      ∀ t k, σ t k → Finset (Cube 4 L) →
        Finset (Cube 4 L) → ℝ :=
    fun t k Z D P =>
      cmp116Eq228PhysicalPResidualWeight
        (M := M)
        (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (alpha6 t k) (q t k) (C2 t k) (kappa1 t k)
        (delta t k) (kappa t k) (unionOf t k Z)
        (gamma2 t k) (hp t k).epsilon1 (gk t k)
        ((eq231Boundary t k).pBonds Z D P)
  have hpResidual_nonneg :
      ∀ t k Z D P, 0 ≤ pResidualWeight t k Z D P := by
    intro t k Z D P
    have hcoeff :
        0 ≤
          cmp116Eq228SourceCoefficient
            (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
            (alpha6 t k) M (q t k) (C2 t k) (kappa1 t k) :=
      cmp116Eq228SourceCoefficient_nonneg
        (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (alpha6 t k) M (q t k) (C2 t k) (kappa1 t k)
        (hE0_nonneg t k) (hepsilon1_nonneg t k)
        (hC1_nonneg t k) (halpha4_pos t k) (halpha6 t k)
    simpa [pResidualWeight, cmp116Eq228PhysicalPResidualWeight] using
      cmp116Eq228PResidualWeight_nonneg
        (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (alpha6 t k) M (q t k) (C2 t k) (kappa1 t k)
        (delta t k) (kappa t k)
        (cmp116Eq229ShiftedCardMetric (unionOf t k Z) : ℝ)
        (gamma2 t k) (hp t k).epsilon1 (gk t k)
        ((eq231Boundary t k).pBonds Z D P) hcoeff
  have hpointwise :
      ∀ t k Z D, D ∈ DIndex t k Z →
        ∀ P, P ∈ PIndex t k Z D →
          pResidualWeight t k Z D P ≤
            (2 * (((pStageBlockScale t k : ℝ) + 2) ^ 4) *
                epsilon2 t k) *
              cmp116Eq226PBondFactor
                (gamma2 t k) (hp t k).epsilon1 (gk t k)
                ((eq231Boundary t k).pBonds Z D P) := by
    intro t k Z D _hD P _hP
    have hcoeff :
        0 ≤
          cmp116Eq228SourceCoefficient
            (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
            (alpha6 t k) M (q t k) (C2 t k) (kappa1 t k) :=
      cmp116Eq228SourceCoefficient_nonneg
        (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (alpha6 t k) M (q t k) (C2 t k) (kappa1 t k)
        (hE0_nonneg t k) (hepsilon1_nonneg t k)
        (hC1_nonneg t k) (halpha4_pos t k) (halpha6 t k)
    simpa [pResidualWeight, cmp116Eq228PhysicalPResidualWeight] using
      cmp116Eq228PResidualWeight_le_eq231Pointwise
        (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (alpha6 t k) M (q t k) (pStageBlockScale t k)
        (C2 t k) (kappa1 t k) (delta t k) (kappa t k)
        (cmp116Eq229ShiftedCardMetric (unionOf t k Z) : ℝ)
        (gamma2 t k) (hp t k).epsilon1 (gk t k) (epsilon2 t k)
        ((eq231Boundary t k).pBonds Z D P)
        hcoeff (hkappa_nonneg t k) (hfourDelta t k)
        (by positivity) (hepsilon2_source t k)
  have heq237_fixed :
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
                    (components t k) (componentMetric t k) Z Z0' := by
    intro t k Z D hD P hP Z0' hZ0'
    have hDIndex : D ∈ DIndex t k Z := by
      exact hD
    have hextract :=
      cmp116Eq226DomainProduct_mul_PBondFactor_le_eq229Product_mul_eq228PResidual_cubeSourceTree
        (domainFamily t k) (unionOf t k Z) (hunion_nonempty t k Z)
        (hdomains t k) (DParts t k Z D)
        (hparts_mem t k Z D hDIndex)
        (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
        (alpha6 t k) M (q t k) (C2 t k) (kappa1 t k)
        (delta t k) (kappa t k)
        (gamma2 t k) (hp t k).epsilon1 (gk t k)
        ((eq231Boundary t k).pBonds Z D P)
        (hE0_nonneg t k) (hepsilon1_nonneg t k)
        (hC1_nonneg t k) (halpha4_pos t k) (halpha6 t k)
        (hdelta_nonneg t k) (hkappa_nonneg t k)
        (hfourDelta t k) (hEq228Small t k)
    have hfixed_nonneg :
        0 ≤
          cmp116Eq237FixedZ0PrimeWeight
            (hp t k)
            (localizationScale t k)
            (C237 t k) (Calpha5 t k) (alpha5 t k)
            (sourceCard t k) (gapCard t k)
            (components t k) (componentMetric t k) Z Z0' :=
      cmp116Eq237FixedZ0PrimeWeight_nonneg
        (hp t k) (localizationScale t k)
        (C237 t k) (Calpha5 t k) (alpha5 t k)
        (sourceCard t k) (gapCard t k)
        (components t k) (componentMetric t k)
        (hC237_nonneg t k) Z Z0'
    calc
      Finset.sum
            (cmp116Eq237Z0Fiber (R t k) Z D P Z0')
            (fun Z0 => (R t k).termWeight Z D P Z0 Z0') ≤
          (cmp116Eq226DomainProduct
                (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
                M (q t k) (C2 t k) (kappa1 t k)
                (delta t k) (kappa t k)
                cmp116CubeSourceTreeMetric (DParts t k Z D) *
              cmp116Eq226PBondFactor
                (gamma2 t k) (hp t k).epsilon1 (gk t k)
                ((eq231Boundary t k).pBonds Z D P)) *
            cmp116Eq237FixedZ0PrimeWeight
              (hp t k)
              (localizationScale t k)
              (C237 t k) (Calpha5 t k) (alpha5 t k)
              (sourceCard t k) (gapCard t k)
              (components t k) (componentMetric t k) Z Z0' := by
        have hdomain_nonneg :
            0 ≤
              cmp116Eq226DomainProduct
                (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
                M (q t k) (C2 t k) (kappa1 t k)
                (delta t k) (kappa t k)
                cmp116CubeSourceTreeMetric (DParts t k Z D) := by
          unfold cmp116Eq226DomainProduct
          exact
            Finset.prod_nonneg fun Y _hY =>
              cmp116Eq226DomainFactor_nonneg
                (hE0_nonneg t k) (hepsilon1_nonneg t k)
                (hC1_nonneg t k) (halpha4_pos t k).le
        have hbase_nonneg :
            0 ≤
              (cmp116Eq226DomainProduct
                    (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
                    M (q t k) (C2 t k) (kappa1 t k)
                    (delta t k) (kappa t k)
                    cmp116CubeSourceTreeMetric (DParts t k Z D) *
                  cmp116Eq226PBondFactor
                    (gamma2 t k) (hp t k).epsilon1 (gk t k)
                    ((eq231Boundary t k).pBonds Z D P)) *
                cmp116Eq226GapFactor
                  (hp t k).kappa1 (localizationScale t k) 1
                  (gapCard t k Z Z0') *
                cmp116Eq226GaussianVolumeFactor
                  (Calpha5 t k) (alpha5 t k) (sourceCard t k Z) := by
          exact
            mul_nonneg
              (mul_nonneg
                (mul_nonneg hdomain_nonneg (Real.exp_nonneg _))
                (Real.exp_nonneg _))
              (Real.exp_nonneg _)
        exact
          cmp116Eq237_rawFixed_of_sourcePointwiseLedger_and_fiberEntropy
            (hp t k) (localizationScale t k)
            (C237 t k) (Calpha5 t k) (alpha5 t k)
            (sourceCard t k) (gapCard t k)
            (components t k) (componentMetric t k)
            Z Z0'
            (cmp116Eq237Z0Fiber (R t k) Z D P Z0')
            (fun Z0 => (R t k).termWeight Z D P Z0 Z0')
            (cmp116Eq226DomainProduct
                  (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
                  M (q t k) (C2 t k) (kappa1 t k)
                  (delta t k) (kappa t k)
                  cmp116CubeSourceTreeMetric (DParts t k Z D) *
                cmp116Eq226PBondFactor
                  (gamma2 t k) (hp t k).epsilon1 (gk t k)
                  ((eq231Boundary t k).pBonds Z D P))
            hbase_nonneg
            (by
              intro Z0 hZ0
              let s := S t k Z D P Z0 Z0'
              have hf :
                  (∃ domainCubes : Fin nY → Finset (Cube 4 L),
                    Function.Injective domainCubes ∧
                    (∀ i,
                      s.domainMetric i =
                        cmp116CubeSourceTreeMetric (domainCubes i)) ∧
                    DParts t k Z D =
                      cmp116Eq226SourceDomainParts domainCubes) ∧
                  ((eq231Boundary t k).pBonds Z D P).card = P.card ∧
                  localizationScale t k * 1 = s.gapScale * M ∧
                  gapCard t k Z Z0' = s.gapCard ∧
                  s.volumeRate * alpha t k ≤
                    Calpha5 t k * alpha5 t k ∧
                  Z0.card ≤ sourceCard t k Z := by
                simpa [R, s] using
                  hscalar_eq226_fixed
                    t k Z D hD P hP Z0' hZ0' Z0 hZ0
              rcases hf with
                ⟨hdomainDictionary, hPcard, hgapScale, hgapCardDictionary,
                  hvolumeCoefficient, hsourceCard⟩
              obtain ⟨domainCubes, hdomainCubes_inj,
                  hdomainMetric, hdomainParts⟩ := hdomainDictionary
              have hdomain :
                  cmp116Eq226DomainProduct
                      (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
                      M (q t k) (C2 t k) (kappa1 t k)
                      (delta t k) (kappa t k)
                      s.domainMetric Finset.univ =
                    cmp116Eq226DomainProduct
                      (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
                      M (q t k) (C2 t k) (kappa1 t k)
                      (delta t k) (kappa t k)
                      cmp116CubeSourceTreeMetric (DParts t k Z D) :=
                cmp116Eq226DomainProduct_eq_of_sourceDomainDictionary
                  (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
                  M (q t k) (C2 t k) (kappa1 t k)
                  (delta t k) (kappa t k)
                  domainCubes s.domainMetric
                  cmp116CubeSourceTreeMetric (DParts t k Z D)
                  hdomainCubes_inj hdomainMetric hdomainParts
              have hPpenalty :=
                cmp116Eq226PBondPenalty_eq_of_sourceDictionary
                  (gamma t k) (epsilon1 t k) (gk t k) P
                  (gamma2 t k) (hp t k).epsilon1 (gk t k)
                  ((eq231Boundary t k).pBonds Z D P)
                  (hgamma2_source t k) (hepsilon1_source t k) rfl hPcard
              have hgappenalty :=
                cmp116Eq226GapPenalty_eq_of_sourceDictionary
                  (kappa1 t k) s.gapScale M s.gapCard
                  (hp t k).kappa1 (localizationScale t k) 1
                  (gapCard t k Z Z0')
                  (hkappa1_source t k) hgapScale hgapCardDictionary
              have hgaussianExponent :=
                cmp116Eq226GaussianExponent_le_of_sourceDictionary
                  (s.volumeRate * alpha t k)
                  (Calpha5 t k * alpha5 t k)
                  Z0.card (sourceCard t k Z)
                  hvolumeCoefficient hsourceCard
                  (hvolumeTarget_nonneg t k)
              have hledger :=
                cmp116Eq226SourceTermWeight_le_targetLedger_of_scalarDictionaries
                  (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
                  M (q t k) (C2 t k) (kappa1 t k)
                  (delta t k) (kappa t k) (gamma t k) (gk t k)
                  s.gapScale s.gapCard s.volumeRate (alpha t k) Z0.card
                  s.domainMetric Finset.univ P
                  (cmp116Eq226DomainProduct
                    (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
                    M (q t k) (C2 t k) (kappa1 t k)
                    (delta t k) (kappa t k)
                    cmp116CubeSourceTreeMetric (DParts t k Z D))
                  (gamma2 t k) (hp t k).epsilon1 (gk t k)
                  ((eq231Boundary t k).pBonds Z D P)
                  (hp t k).kappa1 (localizationScale t k) 1
                  (gapCard t k Z Z0')
                  (Calpha5 t k) (alpha5 t k) (sourceCard t k Z)
                  (hE0_nonneg t k) (hepsilon1_nonneg t k)
                  (hC1_nonneg t k) (halpha4_pos t k).le
                  hdomain.le
                  hPpenalty.le hgappenalty.le hgaussianExponent
              simpa [
                R, s, cmp116Eq226PhysicalContourResummationScaleFamily,
                cmp116Eq226PhysicalContourResummation,
                CMP116Eq226PhysicalContourTermSource.termWeight] using hledger)
            (by
              have hencoding :=
                hcomponentEncoding t k Z D hD P hP Z0' hZ0'
              simpa [R, cmp116Eq237ComponentProduct] using
                hencoding.fiberEntropy)
      _ ≤
          ((∏ Y ∈ DParts t k Z D,
              cmp116Eq229Weight
                (alpha6 t k) (delta t k) (kappa t k)
                cmp116CubeSourceTreeMetric Y) *
            cmp116Eq228PResidualWeight
              (E0 t k) (epsilon1 t k) (C1 t k) (alpha4 t k)
              (alpha6 t k) M (q t k) (C2 t k) (kappa1 t k)
              (delta t k) (kappa t k)
              (cmp116Eq229ShiftedCardMetric (unionOf t k Z) : ℝ)
              (gamma2 t k) (hp t k).epsilon1 (gk t k)
              ((eq231Boundary t k).pBonds Z D P)) *
            cmp116Eq237FixedZ0PrimeWeight
              (hp t k)
              (localizationScale t k)
              (C237 t k) (Calpha5 t k) (alpha5 t k)
              (sourceCard t k) (gapCard t k)
              (components t k) (componentMetric t k) Z Z0' := by
        exact mul_le_mul_of_nonneg_right hextract hfixed_nonneg
      _ =
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
              (components t k) (componentMetric t k) Z Z0' := by
        simp only [cmp116Eq229WeightedPWeight, cmp116Eq229Product]
        rw [← hdelta_source t k, ← hkappa_source t k]
        rfl
  let eq229 :
      CMP116Lemma3Eq229ScaleBoundary hp R DParts alpha6
        (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y) :=
    CMP116Lemma3Eq229ScaleBoundary.of_cubeSourceTreeMetric_exactUnionInjection
      hp R DParts domainFamily unionOf hunion_nonempty hdomains
      hparts_mem hparts_inj
      alpha6 (fun t k => (halpha6 t k).le)
      hdeltaKappa hEq229Cq hEq229Uniform
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
    CMP116Lemma3WeightedPostPSourceScaleBoundary.of_eq237SourceMajorization
      hp R sourceMetric DParts alpha6
      (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y)
      pResidualWeight localizationScale C237 Calpha5 alpha5
      sourceCard gapCard components componentMetric sourceZ0PrimeIndex
      postPSourceWeight hC237_nonneg
      (fun t k => (halpha6 t k).le) hpResidual_nonneg
      hindex
      (by simpa [pResidualWeight] using heq237_fixed)
      (fun t k Z => by
        letI : NeZero (localizationScale t k) :=
          ⟨hlocalizationScale_ne t k⟩
        have hA :
            0 ≤
              cmp116Eq237Amplitude
                (hp t k).blockScale (C237 t k)
                (hp t k).epsilon2 :=
          cmp116Eq237Amplitude_nonneg
            (hp t k).blockScale
            (hC237_nonneg t k)
            (hp t k).epsilon2_nonneg
        have hsum :=
          cmp116Eq237_fixedZ0PrimeSum_le_amplitude_mul_sourceRootedBudget
            (L := L)
            (hp t k) (localizationScale t k)
            (C237 t k) (Calpha5 t k) (alpha5 t k)
            (sourceCard t k) (sourceMetric t k)
            (gapCard t k)
            (components t k) (componentMetric t k)
            (sourceZ0PrimeIndex t k)
            (componentAtomMetric t k)
            (componentCarrier t k)
            (gapCost t k)
            (cmp116Eq237ComponentTransportRate (hp t k))
            (cmp116Eq237ComponentEntropyRate (hp t k))
            Z
            (hgapComponentCovering t k)
            (cmp116Eq237_componentTransportRate_nonneg_of_fifteen_delta
              (hp t k) (by
                simpa [← hkappa_source t k] using hkappa_nonneg t k)
              (by simpa [← hdelta_source t k] using hfifteenDelta t k))
            (cmp116Eq237_componentRate_eq_transport_add_entropy
              (hp t k))
            (hgapPays t k)
            (CMP116Eq234GapIndexEncoding.of_physicalSubregions
              (localizationScale t k)
              (gapCarrier t k Z)
              (sourceZ0PrimeIndex t k Z)
              (hsourceZ0Prime_sub t k Z))
            (hcomponentFamilyEncoding t k Z)
            (hcomponentFamilies_nonempty t k Z)
            (hrootedComponentDictionary t k Z)
            hA
            (cmp116Eq237_componentEntropyRate_nonneg
              (hp t k)
              (by simpa [← hdelta_source t k] using hdelta_nonneg t k)
              (by simpa [← hkappa_source t k] using hkappa_nonneg t k))
            (cmp116Eq237_componentRootedSmall_of_eq229
              (hp t k) (hdeltaKappa t k) (hblockScale_two t k)
              (hEq229Cq t k))
        simpa [postPSourceWeight] using hsum)
      (by
        simpa [postPSourceWeight] using
          cmp116PostPResidualSourceMajorizationScaleFamily_of_shiftedTransportPrefactor
            hp sourceMetric
            (fun t k Z =>
              cmp116Eq237SourcePostComponentBudget
                (cmp116Eq226GaussianVolumeFactor
                  (Calpha5 t k) (alpha5 t k) (sourceCard t k Z))
                (cmp116Eq237Amplitude
                  (hp t k).blockScale (C237 t k)
                  (hp t k).epsilon2)
                (hp t k).kappa1
                (gapCarrier t k Z).card
                (componentCarrier t k Z).card
                (cmp116Eq237ComponentEntropyRate (hp t k)))
            (fun t k =>
              cmp116Eq237Amplitude
                (hp t k).blockScale (C237 t k)
                (hp t k).epsilon2)
            postLinearRate
            (fun t k =>
              cmp116Eq237Amplitude_nonneg
                (hp t k).blockScale
                (hC237_nonneg t k)
                (hp t k).epsilon2_nonneg)
            (fun t k => by
              have hsmall :=
                cmp116Eq237_componentRootedSmall_of_eq229
                  (hp t k) (hdeltaKappa t k) (hblockScale_two t k)
                  (hEq229Cq t k)
              have hdenom :
                  0 ≤
                    (1 - 64 * Real.exp
                      (-(cmp116Eq237ComponentEntropyRate (hp t k) / 24)))⁻¹ :=
                inv_nonneg.mpr (by linarith)
              have hroot :
                  0 ≤
                    cmp116Eq237RootedComponentLinearRate
                      24
                      (cmp116Eq237ComponentEntropyRate (hp t k)) := by
                unfold cmp116Eq237RootedComponentLinearRate
                exact mul_nonneg (by norm_num) hdenom
              dsimp [postLinearRate]
              exact add_nonneg
                (add_nonneg
                  (add_nonneg
                    (mul_nonneg (Real.exp_nonneg _)
                      (mul_nonneg (by norm_num)
                        (hgapCarrierScale_nonneg t k)))
                    (mul_nonneg
                      (hvolumeTarget_nonneg t k)
                      (mul_nonneg (by norm_num)
                        (hsourceCardScale_nonneg t k))))
                  hroot)
                (mul_nonneg
                  (cmp116Eq237Amplitude_nonneg
                    (hp t k).blockScale
                    (hC237_nonneg t k)
                    (hp t k).epsilon2_nonneg)
                  hroot))
            (fun t k => by
              simpa [postLinearRate] using hpostRateBudget t k)
            (fun t k => by
              have hepsilon2 :
                  (hp t k).epsilon2 =
                    cmp116Lemma3Epsilon2OfSourceConstants
                      (E0 t k) (C1 t k)
                      (alpha4 t k) (alpha6 t k) (M : ℝ)
                      (C2 t k) (kappa1 t k) (q t k)
                      (hp t k).epsilon1 := by
                calc
                  (hp t k).epsilon2 = epsilon2 t k :=
                    hhp_epsilon2_source t k
                  _ =
                    cmp116Eq228SourceCoefficient
                      (E0 t k) (epsilon1 t k) (C1 t k)
                      (alpha4 t k) (alpha6 t k)
                      M (q t k) (C2 t k) (kappa1 t k) :=
                        hepsilon2_source t k
                  _ =
                    cmp116Lemma3Epsilon2OfSourceConstants
                      (E0 t k) (C1 t k)
                      (alpha4 t k) (alpha6 t k) (M : ℝ)
                      (C2 t k) (kappa1 t k) (q t k)
                      (hp t k).epsilon1 := by
                    rw [hepsilon1_source t k]
                    unfold cmp116Eq228SourceCoefficient
                      cmp116Lemma3Epsilon2OfSourceConstants
                      cmp116Lemma3Epsilon2SourceFactor
                    ring
              calc
                cmp116Eq237Amplitude
                      (hp t k).blockScale (C237 t k)
                      (hp t k).epsilon2 *
                    Real.exp (postLinearRate t k) =
                  cmp116Eq237Amplitude
                      (hp t k).blockScale (C237 t k)
                      (cmp116Lemma3Epsilon2OfSourceConstants
                        (E0 t k) (C1 t k)
                        (alpha4 t k) (alpha6 t k) (M : ℝ)
                        (C2 t k) (kappa1 t k) (q t k)
                        (hp t k).epsilon1) *
                    Real.exp (postLinearRate t k) := by
                      rw [hepsilon2]
                _ =
                  cmp116Lemma3C3OfShiftedSourceConstants
                      (hp t k).blockScale
                      (C237 t k) (E0 t k) (C1 t k)
                      (alpha4 t k) (alpha6 t k) (M : ℝ)
                      (C2 t k) (kappa1 t k)
                      (postLinearRate t k) (q t k) *
                    (hp t k).epsilon1 :=
                      cmp116Eq237Amplitude_mul_exp_eq_shiftedC3_mul_epsilon1_of_sourceConstants
                        (hp t k).blockScale
                        (C237 t k) (E0 t k) (C1 t k)
                        (alpha4 t k) (alpha6 t k) (M : ℝ)
                        (C2 t k) (kappa1 t k)
                        (hp t k).epsilon1 (postLinearRate t k)
                        (q t k)
                _ ≤ (hp t k).C3 * (hp t k).epsilon1 := by
                  rw [← hC3_source_shifted t k])
            (fun t k Z =>
              cmp116Eq237SourcePostComponentBudget_le_exp_of_shiftedLinearCards
                (Calpha5 t k) (alpha5 t k) (hp t k).kappa1
                (sourceCard t k Z)
                (gapCarrier t k Z).card
                (componentCarrier t k Z).card
                (sourceMetric t k Z)
                (cmp116Eq237Amplitude
                  (hp t k).blockScale (C237 t k)
                  (hp t k).epsilon2)
                (cmp116Eq237ComponentEntropyRate (hp t k))
                (24 * sourceCardScale t k)
                (24 * gapCarrierScale t k)
                24
                (postLinearRate t k)
                (hvolumeTarget_nonneg t k)
                (cmp116Eq237Amplitude_nonneg
                  (hp t k).blockScale
                  (hC237_nonneg t k)
                  (hp t k).epsilon2_nonneg)
                (by norm_num)
                (cmp116Eq237_componentRootedSmall_of_eq229
                  (hp t k) (hdeltaKappa t k) (hblockScale_two t k)
                  (hEq229Cq t k))
                (hsourceCard_linear t k Z)
                (hgapCarrier_linear t k Z)
                (hcomponentCarrier_linear t k Z)
                (by
                  simp only [postLinearRate]
                  exact le_rfl)))
  exact
    cmp116Eq226PhysicalContour_lemma3ActivityEstimate_of_cubeSourceTreeBoundaries
      Dict E0 epsilon1 C1 alpha4 q C2 kappa1 delta kappa gamma gk
      alpha outerBound outerRate sourceRate
      DIndex PIndex Z0Index Z0PrimeIndex S hp sourceMetric DParts
      domainFamily unionOf hunion_nonempty hdomains
      hparts_mem hparts_inj
      alpha6 (fun t k => (halpha6 t k).le)
      hdeltaKappa hEq229Cq hEq229Uniform
      pResidualWeight pStageBlockScale pEntropyConstant
      epsilon2 pStageKappa postPSourceWeight
      (fun t k =>
        cmp116Eq237Amplitude
          (hp t k).blockScale (C237 t k) (hp t k).epsilon2)
      pStage postP

end YangMills.RG

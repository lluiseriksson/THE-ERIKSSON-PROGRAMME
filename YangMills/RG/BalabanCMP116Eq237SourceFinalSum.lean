/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq237GapComponentCovering
import YangMills.RG.BalabanCMP116Eq237GapComponentFamilySum

/-!
# Source-faithful final CMP116 equation-(2.37) sum

The final source argument reserves half of the outer Cauchy gap decay.  One
half, together with the transport part of the connected-component decay,
pays the global metric by the adapted equation-(2.32) geometry.  The other
half is summed jointly with the component entropy by equation (2.34).

This module implements that exact split.  Unlike the earlier sufficient
route, it does not spend the entire gap factor on global transport and then
discard the printed equation-(2.34) summation.
-/

namespace YangMills.RG

noncomputable section

open scoped BigOperators

/-- The outer Cauchy gap factor splits exactly into two equal halves. -/
theorem cmp116Eq237_gapFactor_eq_half_mul_half
    (kappa1 : ℝ) (localizationScale gapCard : ℕ) :
    cmp116Eq226GapFactor
        kappa1 localizationScale 1 gapCard =
      cmp116Eq226GapFactor
          ((kappa1 + 1) / 2) localizationScale 1 gapCard *
        cmp116Eq226GapFactor
          ((kappa1 + 1) / 2) localizationScale 1 gapCard := by
  unfold cmp116Eq226GapFactor
  simp only [Nat.mul_one]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The half-gap factor is the literal equation-(2.34) subset weight after
the normalized gap-cardinality dictionary is applied. -/
theorem cmp116Eq237_halfGapFactor_eq
    (kappa1 : ℝ) (localizationScale gapCard gapChoiceCard : ℕ)
    (hnormalized :
      ((((localizationScale : ℝ) ^ 4)⁻¹) * (gapCard : ℝ)) =
        (gapChoiceCard : ℝ)) :
    cmp116Eq226GapFactor
        ((kappa1 + 1) / 2) localizationScale 1 gapCard =
      Real.exp
        (-(((kappa1 - 1) / 2) * (gapChoiceCard : ℝ))) := by
  unfold cmp116Eq226GapFactor
  simp only [Nat.mul_one]
  rw [show
      ((kappa1 + 1) / 2 - 1) =
        (kappa1 - 1) / 2 by ring,
    mul_assoc, hnormalized]

/-- The final `Z0'` sum with the source split: global transport survives,
while the reserved half-gap and component entropy are summed jointly. -/
theorem cmp116Eq237_fixedZ0PrimeSum_le_source_gapComponentGas
    {σ ιZ0' ιC α : Type*}
    [DecidableEq ιZ0'] [DecidableEq α]
    (hp : CMP116Lemma3Parameters)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard sourceMetric : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (index : σ → Finset ιZ0')
    (gapCost transportRate entropyRate : ℝ)
    (Z : σ)
    (Cover :
      CMP116Eq237GapComponentCovering
        sourceMetric index gapCard components componentMetric
        localizationScale gapCost)
    (htransport : 0 ≤ transportRate)
    (hsplit :
      ((1 - 7 * hp.delta) / 2) *
          (hp.blockScale : ℝ) * hp.kappa =
        transportRate + entropyRate)
    (hpayHalf :
      transportRate * gapCost ≤ (hp.kappa1 - 1) / 2)
    (Gap :
      CMP116Eq234GapIndexEncoding
        α (index Z) (gapCard Z) localizationScale)
    (Comp :
      CMP116Eq237ComponentFamilyEncoding
        (index Z)
        (components Z)
        (fun Z0' Zi =>
          cmp116Eq237Amplitude
              hp.blockScale C237 hp.epsilon2 *
            Real.exp
              (-(entropyRate *
                (componentMetric Z Z0' Zi : ℝ)))))
    (hcomponents_nonempty :
      ∀ Z0', Z0' ∈ index Z → (components Z Z0').Nonempty) :
    (∑ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0') ≤
      Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 (sourceCard Z) *
        Real.exp
          (Real.exp (-((hp.kappa1 - 1) / 2)) *
            (Gap.carrier.card : ℝ)) *
        (Real.exp
            (∑ Zi ∈ Comp.componentUniverse,
              Comp.atomWeight Zi) - 1) := by
  let amplitude : ℝ :=
    cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2
  let gaussian : ℝ :=
    cmp116Eq226GaussianVolumeFactor
      Calpha5 alpha5 (sourceCard Z)
  let entropyFactor : ιZ0' → ιC → ℝ := fun Z0' Zi =>
    amplitude *
      Real.exp
        (-(entropyRate *
          (componentMetric Z Z0' Zi : ℝ)))
  let halfKappa : ℝ := (hp.kappa1 + 1) / 2
  have hhalfPay :
      transportRate * gapCost ≤ halfKappa - 1 := by
    dsimp [halfKappa]
    nlinarith
  have hgaussian : 0 ≤ gaussian := by
    dsimp [gaussian, cmp116Eq226GaussianVolumeFactor]
    positivity
  have hpoint :
      ∀ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
            hp localizationScale C237 Calpha5 alpha5
            sourceCard gapCard components componentMetric Z Z0' ≤
          (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
            gaussian) *
            (Real.exp
                (-(((hp.kappa1 - 1) / 2) *
                  (((localizationScale : ℝ) ^ 4)⁻¹) *
                  (gapCard Z Z0' : ℝ))) *
              ∏ Zi ∈ components Z Z0',
                entropyFactor Z0' Zi) := by
    intro Z0' hZ0'
    have hsplitProduct :=
      cmp116Eq237_componentProduct_split
        (components Z Z0')
        (componentMetric Z Z0')
        amplitude
        (((1 - 7 * hp.delta) / 2) *
          (hp.blockScale : ℝ) * hp.kappa)
        transportRate entropyRate hsplit
    have htransportGlobal :=
      cmp116Eq237_gap_mul_componentTransport_le_globalTransport
        sourceMetric index gapCard components componentMetric
        localizationScale gapCost transportRate halfKappa
        Cover htransport hhalfPay Z Z0' hZ0'
    have hentropy_nonneg :
        0 ≤
          Real.exp
              (-(((hp.kappa1 - 1) / 2) *
                (((localizationScale : ℝ) ^ 4)⁻¹) *
                (gapCard Z Z0' : ℝ))) *
            ∏ Zi ∈ components Z Z0',
              entropyFactor Z0' Zi := by
      exact mul_nonneg (Real.exp_nonneg _)
        (Finset.prod_nonneg fun Zi hZi =>
          Comp.componentFactor_nonneg Z0' hZ0' Zi hZi)
    rw [
      cmp116Eq237FixedZ0PrimeWeight_eq_gap_mul_componentProduct_mul_gaussian,
      cmp116Eq237ComponentProduct,
      hsplitProduct,
      cmp116Eq237_gapFactor_eq_half_mul_half]
    have hhalfEq :
        cmp116Eq226GapFactor
            halfKappa localizationScale 1 (gapCard Z Z0') =
          Real.exp
            (-(((hp.kappa1 - 1) / 2) *
              (((localizationScale : ℝ) ^ 4)⁻¹) *
              (gapCard Z Z0' : ℝ))) := by
      dsimp [halfKappa]
      unfold cmp116Eq226GapFactor
      simp only [Nat.mul_one]
      congr 1
      ring
    rw [hhalfEq]
    have hmul :=
      mul_le_mul_of_nonneg_right
        htransportGlobal hentropy_nonneg
    have hmul' :=
      mul_le_mul_of_nonneg_right hmul hgaussian
    rw [hhalfEq] at hmul'
    dsimp only [gaussian, entropyFactor] at hmul' ⊢
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul'
  have hjoint :
      (∑ Z0' ∈ index Z,
          Real.exp
              (-(((hp.kappa1 - 1) / 2) *
                (((localizationScale : ℝ) ^ 4)⁻¹) *
                (gapCard Z Z0' : ℝ))) *
            (∏ Zi ∈ components Z Z0',
              entropyFactor Z0' Zi)) ≤
        Real.exp
            (Real.exp (-((hp.kappa1 - 1) / 2)) *
              (Gap.carrier.card : ℝ)) *
          (Real.exp
              (∑ Zi ∈ Comp.componentUniverse,
                Comp.atomWeight Zi) - 1) := by
    simpa [amplitude, entropyFactor] using
      cmp116Eq237_gapComponentFamilySum_le
        (index Z) (gapCard Z) localizationScale
        (components Z) (fun Z0' Zi =>
          amplitude *
            Real.exp
              (-(entropyRate *
                (componentMetric Z Z0' Zi : ℝ))))
        Gap Comp hcomponents_nonempty hp.kappa1
  have hfront_nonneg :
      0 ≤
        Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
          gaussian :=
    mul_nonneg (Real.exp_nonneg _) hgaussian
  calc
    (∑ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0') ≤
      ∑ Z0' ∈ index Z,
        (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
          gaussian) *
          (Real.exp
              (-(((hp.kappa1 - 1) / 2) *
                (((localizationScale : ℝ) ^ 4)⁻¹) *
                (gapCard Z Z0' : ℝ))) *
            ∏ Zi ∈ components Z Z0',
              entropyFactor Z0' Zi) :=
        Finset.sum_le_sum hpoint
    _ =
      (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        gaussian) *
        (∑ Z0' ∈ index Z,
          Real.exp
              (-(((hp.kappa1 - 1) / 2) *
                (((localizationScale : ℝ) ^ 4)⁻¹) *
                (gapCard Z Z0' : ℝ))) *
            ∏ Zi ∈ components Z Z0',
              entropyFactor Z0' Zi) := by
                rw [Finset.mul_sum]
    _ ≤
      (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        gaussian) *
        (Real.exp
            (Real.exp (-((hp.kappa1 - 1) / 2)) *
              (Gap.carrier.card : ℝ)) *
          (Real.exp
              (∑ Zi ∈ Comp.componentUniverse,
                Comp.atomWeight Zi) - 1)) :=
      mul_le_mul_of_nonneg_left hjoint hfront_nonneg
    _ =
      Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 (sourceCard Z) *
        Real.exp
          (Real.exp (-((hp.kappa1 - 1) / 2)) *
            (Gap.carrier.card : ℝ)) *
        (Real.exp
            (∑ Zi ∈ Comp.componentUniverse,
              Comp.atomWeight Zi) - 1) := by
                simp only [gaussian]
                ring

/-- The explicit prefactor left by the source-faithful equation-(2.37)
summation.  It records separately the Gaussian volume, the equation-(2.34)
gap-subset exponential, and the rooted connected-component gas. -/
def cmp116Eq237SourcePostComponentBudget
    (gaussian amplitude kappa1 : ℝ)
    (gapCarrierCard componentCarrierCard : ℕ)
    (entropyRate : ℝ) : ℝ :=
  gaussian *
    Real.exp
      (Real.exp (-((kappa1 - 1) / 2)) *
        (gapCarrierCard : ℝ)) *
    (cmp116Eq237RootedComponentBound
        componentCarrierCard entropyRate *
      Real.exp
        (amplitude *
          cmp116Eq237RootedComponentBound
            componentCarrierCard entropyRate))

/-- Rooted-animal completion of the source-faithful split.  The leading
activity is extracted only after the gap-subset and component-family sums
have been performed. -/
theorem cmp116Eq237_fixedZ0PrimeSum_le_amplitude_mul_sourceRootedBudget
    {L : ℕ} [NeZero L]
    {σ ιZ0' ιC α : Type*}
    [DecidableEq ιZ0'] [DecidableEq α]
    (hp : CMP116Lemma3Parameters)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard sourceMetric : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (index : σ → Finset ιZ0')
    (componentAtomMetric : σ → ιC → ℕ)
    (componentCarrier : σ → Finset (Cube 4 L))
    (gapCost transportRate entropyRate : ℝ)
    (Z : σ)
    (Cover :
      CMP116Eq237GapComponentCovering
        sourceMetric index gapCard components componentMetric
        localizationScale gapCost)
    (htransport : 0 ≤ transportRate)
    (hsplit :
      ((1 - 7 * hp.delta) / 2) *
          (hp.blockScale : ℝ) * hp.kappa =
        transportRate + entropyRate)
    (hpayHalf :
      transportRate * gapCost ≤ (hp.kappa1 - 1) / 2)
    (Gap :
      CMP116Eq234GapIndexEncoding
        α (index Z) (gapCard Z) localizationScale)
    (Comp :
      CMP116Eq237ComponentFamilyEncoding
        (index Z)
        (components Z)
        (fun Z0' Zi =>
          cmp116Eq237Amplitude
              hp.blockScale C237 hp.epsilon2 *
            Real.exp
              (-(entropyRate *
                (componentMetric Z Z0' Zi : ℝ)))))
    (hcomponents_nonempty :
      ∀ Z0', Z0' ∈ index Z → (components Z Z0').Nonempty)
    (D :
      CMP116Eq237RootedCubeComponentDictionary
        Comp.componentUniverse Comp.atomWeight
        (componentAtomMetric Z) (componentCarrier Z)
        (cmp116Eq237Amplitude
          hp.blockScale C237 hp.epsilon2)
        entropyRate)
    (hamplitude :
      0 ≤ cmp116Eq237Amplitude
        hp.blockScale C237 hp.epsilon2)
    (hentropy : 0 ≤ entropyRate)
    (hsmall :
      64 * Real.exp (-(entropyRate / 24)) < 1) :
    (∑ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0') ≤
      cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2 *
        (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
          cmp116Eq237SourcePostComponentBudget
            (cmp116Eq226GaussianVolumeFactor
              Calpha5 alpha5 (sourceCard Z))
            (cmp116Eq237Amplitude
              hp.blockScale C237 hp.epsilon2)
            hp.kappa1 Gap.carrier.card
            (componentCarrier Z).card entropyRate) := by
  let amplitude : ℝ :=
    cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2
  let gaussian : ℝ :=
    cmp116Eq226GaussianVolumeFactor
      Calpha5 alpha5 (sourceCard Z)
  let gapGas : ℝ :=
    Real.exp
      (Real.exp (-((hp.kappa1 - 1) / 2)) *
        (Gap.carrier.card : ℝ))
  let rootedBound : ℝ :=
    cmp116Eq237RootedComponentBound
      (componentCarrier Z).card entropyRate
  have hgaussian : 0 ≤ gaussian := by
    dsimp [gaussian, cmp116Eq226GaussianVolumeFactor]
    positivity
  have hrootedBound : 0 ≤ rootedBound := by
    have hdenom :
        0 < 1 - 64 * Real.exp (-(entropyRate / 24)) := by
      linarith
    exact mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr hdenom.le)
  have hfixed :=
    cmp116Eq237_fixedZ0PrimeSum_le_source_gapComponentGas
      hp localizationScale C237 Calpha5 alpha5
      sourceCard sourceMetric gapCard components componentMetric
      index gapCost transportRate entropyRate Z Cover htransport
      hsplit hpayHalf Gap Comp hcomponents_nonempty
  have hroot :
      (∑ Zi ∈ Comp.componentUniverse, Comp.atomWeight Zi) ≤
        amplitude * rootedBound := by
    simpa [amplitude, rootedBound] using
      cmp116Eq237_rootedCubeComponentWeightSum_le
        Comp.componentUniverse Comp.atomWeight
        (componentAtomMetric Z) (componentCarrier Z)
        amplitude entropyRate D
        (by simpa [amplitude] using hamplitude)
        hentropy hsmall
  have hgas :
      Real.exp
          (∑ Zi ∈ Comp.componentUniverse, Comp.atomWeight Zi) - 1 ≤
        amplitude *
          (rootedBound * Real.exp (amplitude * rootedBound)) :=
    cmp116Eq237_exp_componentSum_sub_one_le_amplitude_mul
      Comp.componentUniverse Comp.atomWeight amplitude rootedBound
      Comp.atomWeight_nonneg
      (by simpa [amplitude] using hamplitude)
      hrootedBound hroot
  have hfront_nonneg :
      0 ≤
        Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
          gaussian * gapGas :=
    mul_nonneg
      (mul_nonneg (Real.exp_nonneg _) hgaussian)
      (Real.exp_nonneg _)
  calc
    (∑ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0') ≤
      (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        gaussian * gapGas) *
        (Real.exp
            (∑ Zi ∈ Comp.componentUniverse, Comp.atomWeight Zi) - 1) := by
              simpa [gaussian, gapGas, mul_assoc] using hfixed
    _ ≤
      (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        gaussian * gapGas) *
        (amplitude *
          (rootedBound * Real.exp (amplitude * rootedBound))) :=
            mul_le_mul_of_nonneg_left hgas hfront_nonneg
    _ =
      amplitude *
        (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
          cmp116Eq237SourcePostComponentBudget
            (cmp116Eq226GaussianVolumeFactor
              Calpha5 alpha5 (sourceCard Z))
            (cmp116Eq237Amplitude
              hp.blockScale C237 hp.epsilon2)
            hp.kappa1 Gap.carrier.card
            (componentCarrier Z).card entropyRate) := by
              dsimp [cmp116Eq237SourcePostComponentBudget,
                amplitude, gaussian, gapGas, rootedBound]
              ring

/-- The source-faithful post-component prefactor is absorbed by one explicit
linear budget.  Compared with the older sufficient route, the budget contains
the additional printed equation-(2.34) contribution
`exp (-(kappa1-1)/2) * gapCarrierRate`. -/
theorem cmp116Eq237SourcePostComponentBudget_le_exp_of_linearCards_rate
    (Calpha5 alpha5 kappa1 : ℝ)
    (sourceCard gapCarrierCard componentCarrierCard sourceMetric : ℕ)
    (amplitude entropyRate sourceCardRate gapCarrierRate
      componentCarrierRate targetRate : ℝ)
    (hvolumeRate : 0 ≤ Calpha5 * alpha5)
    (hamplitude : 0 ≤ amplitude)
    (hcomponentCarrierRate : 0 ≤ componentCarrierRate)
    (hsmall :
      64 * Real.exp (-(entropyRate / 24)) < 1)
    (hsourceCard :
      (sourceCard : ℝ) ≤
        sourceCardRate * (sourceMetric : ℝ))
    (hgapCarrierCard :
      (gapCarrierCard : ℝ) ≤
        gapCarrierRate * (sourceMetric : ℝ))
    (hcomponentCarrierCard :
      (componentCarrierCard : ℝ) ≤
        componentCarrierRate * (sourceMetric : ℝ))
    (hbudget :
      Real.exp (-((kappa1 - 1) / 2)) * gapCarrierRate +
          Calpha5 * alpha5 * sourceCardRate +
          cmp116Eq237RootedComponentLinearRate
            componentCarrierRate entropyRate +
          amplitude *
            cmp116Eq237RootedComponentLinearRate
              componentCarrierRate entropyRate ≤
        targetRate) :
    cmp116Eq237SourcePostComponentBudget
        (cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 sourceCard)
        amplitude kappa1 gapCarrierCard componentCarrierCard entropyRate ≤
      Real.exp (targetRate * (sourceMetric : ℝ)) := by
  let gapLinearRate : ℝ :=
    Real.exp (-((kappa1 - 1) / 2)) * gapCarrierRate
  let postLinearRate : ℝ :=
    Calpha5 * alpha5 * sourceCardRate +
      cmp116Eq237RootedComponentLinearRate
        componentCarrierRate entropyRate +
      amplitude *
        cmp116Eq237RootedComponentLinearRate
          componentCarrierRate entropyRate
  let m : ℝ := (sourceMetric : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hgap :
      Real.exp
          (Real.exp (-((kappa1 - 1) / 2)) *
            (gapCarrierCard : ℝ)) ≤
        Real.exp (gapLinearRate * m) := by
    apply Real.exp_le_exp.mpr
    dsimp [gapLinearRate, m]
    calc
      Real.exp (-((kappa1 - 1) / 2)) *
          (gapCarrierCard : ℝ) ≤
        Real.exp (-((kappa1 - 1) / 2)) *
          (gapCarrierRate * (sourceMetric : ℝ)) :=
            mul_le_mul_of_nonneg_left hgapCarrierCard
              (Real.exp_nonneg _)
      _ =
        (Real.exp (-((kappa1 - 1) / 2)) *
          gapCarrierRate) * (sourceMetric : ℝ) := by ring
  have hpost :
      cmp116Eq237PostComponentBudget
          (cmp116Eq226GaussianVolumeFactor
            Calpha5 alpha5 sourceCard)
          amplitude componentCarrierCard entropyRate ≤
        Real.exp (postLinearRate * m) := by
    apply
      cmp116Eq237PostComponentBudget_le_exp_of_linearCards_rate
        Calpha5 alpha5 sourceCard componentCarrierCard sourceMetric
        amplitude entropyRate sourceCardRate componentCarrierRate
        postLinearRate hvolumeRate hamplitude hcomponentCarrierRate
        hsmall hsourceCard hcomponentCarrierCard
    dsimp [postLinearRate]
    exact le_rfl
  have hpost_nonneg :
      0 ≤
        cmp116Eq237PostComponentBudget
          (cmp116Eq226GaussianVolumeFactor
            Calpha5 alpha5 sourceCard)
          amplitude componentCarrierCard entropyRate := by
    have hdenom :
        0 < 1 - 64 * Real.exp (-(entropyRate / 24)) := by
      linarith
    unfold cmp116Eq237PostComponentBudget
      cmp116Eq226GaussianVolumeFactor
      cmp116Eq237RootedComponentBound
    exact mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr hdenom.le))
        (Real.exp_nonneg _))
  calc
    cmp116Eq237SourcePostComponentBudget
        (cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 sourceCard)
        amplitude kappa1 gapCarrierCard componentCarrierCard entropyRate =
      Real.exp
          (Real.exp (-((kappa1 - 1) / 2)) *
            (gapCarrierCard : ℝ)) *
        cmp116Eq237PostComponentBudget
          (cmp116Eq226GaussianVolumeFactor
            Calpha5 alpha5 sourceCard)
          amplitude componentCarrierCard entropyRate := by
            unfold cmp116Eq237SourcePostComponentBudget
              cmp116Eq237PostComponentBudget
            ring
    _ ≤
      Real.exp (gapLinearRate * m) *
        cmp116Eq237PostComponentBudget
          (cmp116Eq226GaussianVolumeFactor
            Calpha5 alpha5 sourceCard)
          amplitude componentCarrierCard entropyRate :=
            mul_le_mul_of_nonneg_right hgap hpost_nonneg
    _ ≤
      Real.exp (gapLinearRate * m) *
        Real.exp (postLinearRate * m) :=
          mul_le_mul_of_nonneg_left hpost (Real.exp_nonneg _)
    _ =
      Real.exp ((gapLinearRate + postLinearRate) * m) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤
      Real.exp (targetRate * m) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ hm
        simpa only [gapLinearRate, postLinearRate, add_assoc] using hbudget

/-- Backwards-compatible specialization using the full component-entropy
reserve as the target rate. -/
theorem cmp116Eq237SourcePostComponentBudget_le_exp_of_linearCards
    (Calpha5 alpha5 kappa1 : ℝ)
    (sourceCard gapCarrierCard componentCarrierCard sourceMetric : ℕ)
    (amplitude entropyRate sourceCardRate gapCarrierRate
      componentCarrierRate : ℝ)
    (hvolumeRate : 0 ≤ Calpha5 * alpha5)
    (hamplitude : 0 ≤ amplitude)
    (hcomponentCarrierRate : 0 ≤ componentCarrierRate)
    (hsmall :
      64 * Real.exp (-(entropyRate / 24)) < 1)
    (hsourceCard :
      (sourceCard : ℝ) ≤
        sourceCardRate * (sourceMetric : ℝ))
    (hgapCarrierCard :
      (gapCarrierCard : ℝ) ≤
        gapCarrierRate * (sourceMetric : ℝ))
    (hcomponentCarrierCard :
      (componentCarrierCard : ℝ) ≤
        componentCarrierRate * (sourceMetric : ℝ))
    (hbudget :
      Real.exp (-((kappa1 - 1) / 2)) * gapCarrierRate +
          Calpha5 * alpha5 * sourceCardRate +
          cmp116Eq237RootedComponentLinearRate
            componentCarrierRate entropyRate +
          amplitude *
            cmp116Eq237RootedComponentLinearRate
              componentCarrierRate entropyRate ≤
        entropyRate) :
    cmp116Eq237SourcePostComponentBudget
        (cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 sourceCard)
        amplitude kappa1 gapCarrierCard componentCarrierCard entropyRate ≤
      Real.exp (entropyRate * (sourceMetric : ℝ)) :=
  cmp116Eq237SourcePostComponentBudget_le_exp_of_linearCards_rate
    Calpha5 alpha5 kappa1 sourceCard gapCarrierCard
    componentCarrierCard sourceMetric amplitude entropyRate
    sourceCardRate gapCarrierRate componentCarrierRate entropyRate
    hvolumeRate hamplitude hcomponentCarrierRate hsmall
    hsourceCard hgapCarrierCard hcomponentCarrierCard hbudget

/-- Convention-robust source post-component absorption.

The source tree metric vanishes on a singleton, so volume and carrier
cardinalities cannot in general be bounded by a multiple of the unshifted
metric.  The valid geometric input is a bound by `sourceMetric + 1`.  This
theorem keeps that shift visible in the conclusion; a later majorization step
must pay the resulting constant factor rather than silently strengthening the
printed equation-(2.37) decay. -/
theorem cmp116Eq237SourcePostComponentBudget_le_exp_of_shiftedLinearCards
    (Calpha5 alpha5 kappa1 : ℝ)
    (sourceCard gapCarrierCard componentCarrierCard sourceMetric : ℕ)
    (amplitude entropyRate sourceCardRate gapCarrierRate
      componentCarrierRate targetRate : ℝ)
    (hvolumeRate : 0 ≤ Calpha5 * alpha5)
    (hamplitude : 0 ≤ amplitude)
    (hcomponentCarrierRate : 0 ≤ componentCarrierRate)
    (hsmall :
      64 * Real.exp (-(entropyRate / 24)) < 1)
    (hsourceCard :
      (sourceCard : ℝ) ≤
        sourceCardRate * ((sourceMetric : ℝ) + 1))
    (hgapCarrierCard :
      (gapCarrierCard : ℝ) ≤
        gapCarrierRate * ((sourceMetric : ℝ) + 1))
    (hcomponentCarrierCard :
      (componentCarrierCard : ℝ) ≤
        componentCarrierRate * ((sourceMetric : ℝ) + 1))
    (hbudget :
      Real.exp (-((kappa1 - 1) / 2)) * gapCarrierRate +
          Calpha5 * alpha5 * sourceCardRate +
          cmp116Eq237RootedComponentLinearRate
            componentCarrierRate entropyRate +
          amplitude *
            cmp116Eq237RootedComponentLinearRate
              componentCarrierRate entropyRate ≤
        targetRate) :
    cmp116Eq237SourcePostComponentBudget
        (cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 sourceCard)
        amplitude kappa1 gapCarrierCard componentCarrierCard entropyRate ≤
      Real.exp (targetRate * ((sourceMetric : ℝ) + 1)) := by
  have hsourceCard' :
      (sourceCard : ℝ) ≤
        sourceCardRate * (((sourceMetric + 1 : ℕ) : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hsourceCard
  have hgapCarrierCard' :
      (gapCarrierCard : ℝ) ≤
        gapCarrierRate * (((sourceMetric + 1 : ℕ) : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hgapCarrierCard
  have hcomponentCarrierCard' :
      (componentCarrierCard : ℝ) ≤
        componentCarrierRate * (((sourceMetric + 1 : ℕ) : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hcomponentCarrierCard
  simpa [Nat.cast_add, Nat.cast_one] using
    (cmp116Eq237SourcePostComponentBudget_le_exp_of_linearCards_rate
      Calpha5 alpha5 kappa1 sourceCard gapCarrierCard
      componentCarrierCard (sourceMetric + 1)
      amplitude entropyRate sourceCardRate gapCarrierRate
      componentCarrierRate targetRate hvolumeRate hamplitude
      hcomponentCarrierRate hsmall hsourceCard'
      hgapCarrierCard' hcomponentCarrierCard' hbudget)

end

end YangMills.RG

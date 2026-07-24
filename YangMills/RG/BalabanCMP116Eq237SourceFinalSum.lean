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

end

end YangMills.RG

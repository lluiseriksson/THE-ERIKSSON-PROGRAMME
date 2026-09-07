/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq237RootedComponentSum

/-!
# Gap--component metric covering for CMP116 equation (2.37)

The fixed-`Z0'` weight contains two geometric decay mechanisms:

* the normalized gap cardinality `|Z \ Z0'| / L^4`; and
* the sum of the metrics of the connected components of `Z0'`.

They must jointly pay the global metric of `Z`.  Discarding the gap factor and
spending all component decay on entropy leaves no global decay and cannot
produce the final Lemma-3 weight.

This module records the missing source geometry and proves the scalar
transport inequality that preserves a chosen part of the component decay.
-/

namespace YangMills.RG

noncomputable section

open scoped BigOperators

/-- Quarter-delta reserve spent on connected-component entropy. -/
def cmp116Eq237ComponentEntropyRate
    (hp : CMP116Lemma3Parameters) : ℝ :=
  (hp.delta / 4) * (hp.blockScale : ℝ) * hp.kappa

/-- The remainder of the printed seven-delta component rate, preserved for
global transport. -/
def cmp116Eq237ComponentTransportRate
    (hp : CMP116Lemma3Parameters) : ℝ :=
  ((1 - 7 * hp.delta) / 2) *
      (hp.blockScale : ℝ) * hp.kappa -
    cmp116Eq237ComponentEntropyRate hp

/-- Exact transport/entropy split of the printed component rate. -/
theorem cmp116Eq237_componentRate_eq_transport_add_entropy
    (hp : CMP116Lemma3Parameters) :
    ((1 - 7 * hp.delta) / 2) *
        (hp.blockScale : ℝ) * hp.kappa =
      cmp116Eq237ComponentTransportRate hp +
        cmp116Eq237ComponentEntropyRate hp := by
  simp [cmp116Eq237ComponentTransportRate]

/-- Source-faithful covering of the global metric by connected components and
the normalized gap.  The constant `gapCost` is expressed in the same metric
units as `sourceMetric` and `componentMetric`. -/
structure CMP116Eq237GapComponentCovering
    {σ ιZ0' ιC : Type*}
    (sourceMetric : σ → ℕ)
    (sourceZ0PrimeIndex : σ → Finset ιZ0')
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (localizationScale : ℕ)
    (gapCost : ℝ) where
  gapCost_nonneg : 0 ≤ gapCost
  metric_cover :
    ∀ Z Z0', Z0' ∈ sourceZ0PrimeIndex Z →
      (sourceMetric Z : ℝ) ≤
        (∑ Zi ∈ components Z Z0',
          (componentMetric Z Z0' Zi : ℝ)) +
        gapCost *
          ((((localizationScale : ℝ) ^ 4)⁻¹) *
            (gapCard Z Z0' : ℝ))

/-- If the gap penalty rate dominates the transport rate times the geometric
gap cost, then the gap factor and the reserved component decay jointly pay the
global source metric. -/
theorem cmp116Eq237_gap_mul_componentTransport_le_globalTransport
    {σ ιZ0' ιC : Type*}
    (sourceMetric : σ → ℕ)
    (sourceZ0PrimeIndex : σ → Finset ιZ0')
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (localizationScale : ℕ)
    (gapCost transportRate kappa1 : ℝ)
    (Cover :
      CMP116Eq237GapComponentCovering
        sourceMetric sourceZ0PrimeIndex gapCard
        components componentMetric localizationScale gapCost)
    (htransport : 0 ≤ transportRate)
    (hpay : transportRate * gapCost ≤ kappa1 - 1)
    (Z : σ) (Z0' : ιZ0')
    (hZ0' : Z0' ∈ sourceZ0PrimeIndex Z) :
    cmp116Eq226GapFactor
          kappa1 localizationScale 1 (gapCard Z Z0') *
        Real.exp
          (-(transportRate *
            (∑ Zi ∈ components Z Z0',
              (componentMetric Z Z0' Zi : ℝ)))) ≤
      Real.exp (-(transportRate * (sourceMetric Z : ℝ))) := by
  let gapNorm : ℝ :=
    (((localizationScale : ℝ) ^ 4)⁻¹) *
      (gapCard Z Z0' : ℝ)
  let componentSum : ℝ :=
    ∑ Zi ∈ components Z Z0',
      (componentMetric Z Z0' Zi : ℝ)
  have hgapNorm : 0 ≤ gapNorm := by
    dsimp [gapNorm]
    positivity
  have hcover :
      (sourceMetric Z : ℝ) ≤
        componentSum + gapCost * gapNorm := by
    simpa [componentSum, gapNorm, mul_assoc] using
      Cover.metric_cover Z Z0' hZ0'
  have hscaled :
      transportRate * (sourceMetric Z : ℝ) ≤
        transportRate * componentSum +
          (kappa1 - 1) * gapNorm := by
    calc
      transportRate * (sourceMetric Z : ℝ) ≤
          transportRate * (componentSum + gapCost * gapNorm) :=
        mul_le_mul_of_nonneg_left hcover htransport
      _ =
          transportRate * componentSum +
            (transportRate * gapCost) * gapNorm := by ring
      _ ≤
          transportRate * componentSum +
            (kappa1 - 1) * gapNorm := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hpay hgapNorm)
  rw [cmp116Eq226GapFactor]
  simp only [Nat.mul_one]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [gapNorm, componentSum] at hscaled ⊢
  linarith

/-- Exact splitting of a component product into a reserved global-transport
part and a smaller entropy fugacity. -/
theorem cmp116Eq237_componentProduct_split
    {ιC : Type*}
    (components : Finset ιC)
    (componentMetric : ιC → ℕ)
    (amplitude totalRate transportRate entropyRate : ℝ)
    (hsplit : totalRate = transportRate + entropyRate) :
    (∏ Zi ∈ components,
        amplitude *
          Real.exp
            (-(totalRate * (componentMetric Zi : ℝ)))) =
      Real.exp
          (-(transportRate *
            (∑ Zi ∈ components, (componentMetric Zi : ℝ)))) *
        ∏ Zi ∈ components,
          amplitude *
            Real.exp
              (-(entropyRate * (componentMetric Zi : ℝ))) := by
  classical
  have hpoint :
      ∀ Zi ∈ components,
        amplitude *
            Real.exp (-(totalRate * (componentMetric Zi : ℝ))) =
          Real.exp
              (-(transportRate * (componentMetric Zi : ℝ))) *
            (amplitude *
              Real.exp
                (-(entropyRate * (componentMetric Zi : ℝ)))) := by
    intro Zi _hZi
    have harg :
        -((totalRate) * (componentMetric Zi : ℝ)) =
          -(transportRate * (componentMetric Zi : ℝ)) +
            -(entropyRate * (componentMetric Zi : ℝ)) := by
      rw [hsplit]
      ring
    rw [harg, Real.exp_add]
    ring
  calc
    (∏ Zi ∈ components,
        amplitude *
          Real.exp
            (-(totalRate * (componentMetric Zi : ℝ)))) =
      ∏ Zi ∈ components,
        (Real.exp
            (-(transportRate * (componentMetric Zi : ℝ))) *
          (amplitude *
            Real.exp
              (-(entropyRate * (componentMetric Zi : ℝ))))) := by
                exact Finset.prod_congr rfl hpoint
    _ =
      (∏ Zi ∈ components,
          Real.exp
            (-(transportRate * (componentMetric Zi : ℝ)))) *
        ∏ Zi ∈ components,
          amplitude *
            Real.exp
              (-(entropyRate * (componentMetric Zi : ℝ))) := by
                rw [Finset.prod_mul_distrib]
    _ =
      Real.exp
          (-(transportRate *
            (∑ Zi ∈ components, (componentMetric Zi : ℝ)))) *
        ∏ Zi ∈ components,
          amplitude *
            Real.exp
              (-(entropyRate * (componentMetric Zi : ℝ))) := by
      congr 1
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.sum_neg_distrib, Finset.mul_sum]

/-- The source-fixed `Z0'` sum with decay split correctly: the gap and
transport pieces retain global metric decay, while only the entropy piece is
fed to the finite component gas. -/
theorem cmp116Eq237_fixedZ0PrimeSum_le_decayed_componentGas
    {σ ιZ0' ιC : Type*}
    (hp : CMP116Lemma3Parameters)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (sourceMetric : σ → ℕ)
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
    (hpay : transportRate * gapCost ≤ hp.kappa1 - 1)
    (E :
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
        (Real.exp
            (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1) := by
  classical
  let amplitude : ℝ :=
    cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2
  let gaussian : ℝ :=
    cmp116Eq226GaussianVolumeFactor
      Calpha5 alpha5 (sourceCard Z)
  let entropyFactor : ιZ0' → ιC → ℝ :=
    fun Z0' Zi =>
      amplitude *
        Real.exp
          (-(entropyRate *
            (componentMetric Z Z0' Zi : ℝ)))
  have hgaussian : 0 ≤ gaussian := by
    dsimp [gaussian, cmp116Eq226GaussianVolumeFactor]
    positivity
  have hpoint :
      ∀ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
            hp localizationScale C237 Calpha5 alpha5
            sourceCard gapCard components componentMetric Z Z0' ≤
          Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
            gaussian *
            ∏ Zi ∈ components Z Z0', entropyFactor Z0' Zi := by
    intro Z0' hZ0'
    rw [
      cmp116Eq237FixedZ0PrimeWeight_eq_gap_mul_componentProduct_mul_gaussian]
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
        localizationScale gapCost transportRate hp.kappa1
        Cover htransport hpay Z Z0' hZ0'
    have hentropy_nonneg :
        0 ≤ ∏ Zi ∈ components Z Z0', entropyFactor Z0' Zi := by
      exact Finset.prod_nonneg fun Zi hZi =>
        E.componentFactor_nonneg Z0' hZ0' Zi hZi
    rw [cmp116Eq237ComponentProduct]
    rw [hsplitProduct]
    have hmul :=
      mul_le_mul_of_nonneg_right
        htransportGlobal hentropy_nonneg
    have hmul' :=
      mul_le_mul_of_nonneg_right hmul hgaussian
    simpa [amplitude, gaussian, entropyFactor,
      mul_assoc, mul_left_comm, mul_comm] using hmul'
  have hfamily :
      (∑ Z0' ∈ index Z,
          ∏ Zi ∈ components Z Z0', entropyFactor Z0' Zi) ≤
        Real.exp
            (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1 := by
    simpa [amplitude, entropyFactor] using
      cmp116Eq237_componentFamilySum_le_exp_sum_sub_one
        (index Z) (components Z) entropyFactor E
        hcomponents_nonempty
  have hglobal_nonneg :
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
          ∏ Zi ∈ components Z Z0', entropyFactor Z0' Zi := by
            exact Finset.sum_le_sum hpoint
    _ =
      (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        gaussian) *
        (∑ Z0' ∈ index Z,
          ∏ Zi ∈ components Z Z0', entropyFactor Z0' Zi) := by
            rw [Finset.mul_sum]
    _ ≤
      (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        gaussian) *
        (Real.exp
            (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1) :=
          mul_le_mul_of_nonneg_left hfamily hglobal_nonneg
    _ =
      Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 (sourceCard Z) *
        (Real.exp
            (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1) := rfl

/-- Fully composed split-decay estimate: the transport part survives as
global metric decay, while the entropy part is summed by rooted cube animals.
-/
theorem cmp116Eq237_fixedZ0PrimeSum_le_amplitude_mul_decayedRootedBudget
    {L : ℕ} [NeZero L] {σ ιZ0' ιC : Type*}
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
    (hpay : transportRate * gapCost ≤ hp.kappa1 - 1)
    (E :
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
        E.componentUniverse E.atomWeight
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
      cmp116Eq237Amplitude
          hp.blockScale C237 hp.epsilon2 *
        (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
          cmp116Eq237PostComponentBudget
            (cmp116Eq226GaussianVolumeFactor
              Calpha5 alpha5 (sourceCard Z))
            (cmp116Eq237Amplitude
              hp.blockScale C237 hp.epsilon2)
            (componentCarrier Z).card entropyRate) := by
  classical
  let amplitude : ℝ :=
    cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2
  let gaussian : ℝ :=
    cmp116Eq226GaussianVolumeFactor
      Calpha5 alpha5 (sourceCard Z)
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
    cmp116Eq237_fixedZ0PrimeSum_le_decayed_componentGas
      hp localizationScale C237 Calpha5 alpha5
      sourceCard sourceMetric gapCard components componentMetric
      index gapCost transportRate entropyRate Z Cover htransport
      hsplit hpay E hcomponents_nonempty
  have hroot :
      (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) ≤
        amplitude * rootedBound := by
    simpa [amplitude, rootedBound] using
      cmp116Eq237_rootedCubeComponentWeightSum_le
        E.componentUniverse E.atomWeight
        (componentAtomMetric Z) (componentCarrier Z)
        amplitude entropyRate D
        (by simpa [amplitude] using hamplitude)
        hentropy hsmall
  have hgas :
      Real.exp
          (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1 ≤
        amplitude *
          (rootedBound * Real.exp (amplitude * rootedBound)) :=
    cmp116Eq237_exp_componentSum_sub_one_le_amplitude_mul
      E.componentUniverse E.atomWeight amplitude rootedBound
      E.atomWeight_nonneg
      (by simpa [amplitude] using hamplitude)
      hrootedBound hroot
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
      (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        gaussian) *
        (Real.exp
            (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1) := by
              simpa [gaussian, mul_assoc] using hfixed
    _ ≤
      (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
        gaussian) *
        (amplitude *
          (rootedBound * Real.exp (amplitude * rootedBound))) :=
            mul_le_mul_of_nonneg_left hgas hfront_nonneg
    _ =
      amplitude *
        (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
          (gaussian *
            (rootedBound * Real.exp (amplitude * rootedBound)))) := by ring
    _ =
      cmp116Eq237Amplitude
          hp.blockScale C237 hp.epsilon2 *
        (Real.exp (-(transportRate * (sourceMetric Z : ℝ))) *
          cmp116Eq237PostComponentBudget
            (cmp116Eq226GaussianVolumeFactor
              Calpha5 alpha5 (sourceCard Z))
            (cmp116Eq237Amplitude
              hp.blockScale C237 hp.epsilon2)
            (componentCarrier Z).card entropyRate) := by
      rfl

namespace CMP116Eq237MajorizationBoundary

/-- Construct the Eq. (2.37) majorization boundary from the split global
transport factor and one scalar bound on the explicit rooted prefactor.

The residual exponent is not arbitrary: it is exactly twice the entropy
reserve, hence exactly the printed `delta / 2` allowance. -/
def of_transportEntropyPrefactor
    {σ : ℕ → ℕ → Type*}
    (hp : ∀ _t _k, CMP116Lemma3Parameters)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (prefactor : ∀ t k, σ t k → ℝ)
    (C237 : ℕ → ℕ → ℝ)
    (hC237_nonneg : ∀ t k, 0 ≤ C237 t k)
    (hamplitude_le :
      ∀ t k,
        cmp116Eq237Amplitude
            (hp t k).blockScale (C237 t k)
            (hp t k).epsilon2 ≤
          (hp t k).C3 * (hp t k).epsilon1)
    (hprefactor :
      ∀ t k Z,
        prefactor t k Z ≤
          Real.exp
            (cmp116Eq237ComponentEntropyRate (hp t k) *
              (sourceMetric t k Z : ℝ))) :
    CMP116Eq237MajorizationBoundary
      hp sourceMetric
      (fun t k Z =>
        Real.exp
            (-(cmp116Eq237ComponentTransportRate (hp t k) *
              (sourceMetric t k Z : ℝ))) *
          prefactor t k Z)
      (fun t k =>
        cmp116Eq237Amplitude
          (hp t k).blockScale (C237 t k)
          (hp t k).epsilon2) where
  residualExponent := fun t k Z =>
    2 * cmp116Eq237ComponentEntropyRate (hp t k) *
      (sourceMetric t k Z : ℝ)
  amplitude_nonneg := by
    intro t k
    exact cmp116Eq237Amplitude_nonneg
      (hp t k).blockScale
      (hC237_nonneg t k)
      (hp t k).epsilon2_nonneg
  amplitude_le_C3 := hamplitude_le
  seven_delta_bound := by
    intro t k Z
    let transport := cmp116Eq237ComponentTransportRate (hp t k)
    let entropy := cmp116Eq237ComponentEntropyRate (hp t k)
    let m : ℝ := (sourceMetric t k Z : ℝ)
    have hfront : 0 ≤ Real.exp (-(transport * m)) :=
      Real.exp_nonneg _
    have hmul :
        Real.exp (-(transport * m)) * prefactor t k Z ≤
          Real.exp (-(transport * m)) *
            Real.exp (entropy * m) :=
      mul_le_mul_of_nonneg_left
        (by simpa [entropy, m] using hprefactor t k Z)
        hfront
    have harg :
        2 * entropy * m -
            ((1 - 7 * (hp t k).delta) / 2) *
              ((hp t k).blockScale : ℝ) *
              (hp t k).kappa * m =
          -(transport * m) + entropy * m := by
      have hsplit :=
        cmp116Eq237_componentRate_eq_transport_add_entropy
          (hp t k)
      dsimp [transport, entropy]
      rw [hsplit]
      ring
    calc
      Real.exp (-(transport * m)) * prefactor t k Z ≤
          Real.exp (-(transport * m)) *
            Real.exp (entropy * m) := hmul
      _ = Real.exp (-(transport * m) + entropy * m) := by
        rw [Real.exp_add]
      _ =
        Real.exp
          (2 * entropy * m -
            ((1 - 7 * (hp t k).delta) / 2) *
              ((hp t k).blockScale : ℝ) *
              (hp t k).kappa * m) := by
        rw [harg]
  residual_absorbed := by
    intro t k Z
    dsimp [cmp116Eq237ComponentEntropyRate]
    ring_nf
    exact le_rfl

end CMP116Eq237MajorizationBoundary

/-- Source-faithful majorization when cardinality absorption is available only
against the shifted metric `sourceMetric + 1`.

The shift is not inserted into the printed equation-(2.37) decay.  Instead its
constant exponential cost is paid explicitly in the amplitude comparison
`hamplitude_loss`.  This is the convention-robust route for metrics that vanish
on singleton domains. -/
theorem cmp116PostPResidualSourceMajorizationScaleFamily_of_shiftedTransportPrefactor
    {σ : ℕ → ℕ → Type*}
    (hp : ∀ _t _k, CMP116Lemma3Parameters)
    (sourceMetric : ∀ t k, σ t k → ℕ)
    (prefactor : ∀ t k, σ t k → ℝ)
    (postPAmplitude linearRate : ℕ → ℕ → ℝ)
    (hamplitude_nonneg :
      ∀ t k, 0 ≤ postPAmplitude t k)
    (hlinearRate_nonneg :
      ∀ t k, 0 ≤ linearRate t k)
    (hlinearRate_le :
      ∀ t k,
        linearRate t k ≤
          cmp116Eq237ComponentEntropyRate (hp t k))
    (hamplitude_loss :
      ∀ t k,
        postPAmplitude t k * Real.exp (linearRate t k) ≤
          (hp t k).C3 * (hp t k).epsilon1)
    (hprefactor :
      ∀ t k Z,
        prefactor t k Z ≤
          Real.exp
            (linearRate t k *
              ((sourceMetric t k Z : ℝ) + 1))) :
    CMP116PostPResidualSourceMajorizationScaleFamily
      sourceMetric
      (fun t k => (hp t k).blockScale)
      (fun t k => (hp t k).C3)
      (fun t k => (hp t k).epsilon1)
      (fun t k => (hp t k).delta)
      (fun t k => (hp t k).kappa)
      (fun t k Z =>
        Real.exp
            (-(cmp116Eq237ComponentTransportRate (hp t k) *
              (sourceMetric t k Z : ℝ))) *
          prefactor t k Z)
      postPAmplitude := by
  intro t k Z
  let m : ℝ := (sourceMetric t k Z : ℝ)
  let r : ℝ := linearRate t k
  let transport : ℝ := cmp116Eq237ComponentTransportRate (hp t k)
  let target : ℝ :=
    balabanCMP116Lemma3DecayRate
      (hp t k).blockScale (hp t k).delta (hp t k).kappa
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hr : 0 ≤ r := hlinearRate_nonneg t k
  have hfront : 0 ≤ Real.exp (-(transport * m)) :=
    Real.exp_nonneg _
  have hprefactor' :
      prefactor t k Z ≤ Real.exp (r * (m + 1)) := by
    simpa [r, m] using hprefactor t k Z
  have hproduct :
      postPAmplitude t k *
          (Real.exp (-(transport * m)) * prefactor t k Z) ≤
        postPAmplitude t k *
          (Real.exp (-(transport * m)) *
            Real.exp (r * (m + 1))) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprefactor' hfront)
      (hamplitude_nonneg t k)
  have hrewrite :
      postPAmplitude t k *
          (Real.exp (-(transport * m)) *
            Real.exp (r * (m + 1))) =
        (postPAmplitude t k * Real.exp r) *
          Real.exp (-((transport - r) * m)) := by
    calc
      postPAmplitude t k *
          (Real.exp (-(transport * m)) *
            Real.exp (r * (m + 1))) =
        postPAmplitude t k *
          Real.exp (r + -((transport - r) * m)) := by
            rw [← Real.exp_add]
            congr 2
            ring
      _ =
        (postPAmplitude t k * Real.exp r) *
          Real.exp (-((transport - r) * m)) := by
            rw [Real.exp_add]
            ring
  have htarget :
      target = transport -
          cmp116Eq237ComponentEntropyRate (hp t k) := by
    dsimp [target, transport, balabanCMP116Lemma3DecayRate,
      cmp116Eq237ComponentTransportRate,
      cmp116Eq237ComponentEntropyRate]
    ring
  have hrate : target ≤ transport - r := by
    rw [htarget]
    linarith [hlinearRate_le t k]
  have hexponent :
      -((transport - r) * m) ≤ -(target * m) := by
    nlinarith
  have htargetExp :
      Real.exp (-((transport - r) * m)) ≤
        Real.exp (-(target * m)) :=
    Real.exp_le_exp.mpr hexponent
  have hC3_nonneg :
      0 ≤ (hp t k).C3 * (hp t k).epsilon1 := by
    exact
      (mul_nonneg (hamplitude_nonneg t k) (Real.exp_nonneg _)).trans
        (hamplitude_loss t k)
  calc
    postPAmplitude t k *
        (Real.exp
            (-(cmp116Eq237ComponentTransportRate (hp t k) *
              (sourceMetric t k Z : ℝ))) *
          prefactor t k Z) ≤
      postPAmplitude t k *
        (Real.exp (-(transport * m)) *
          Real.exp (r * (m + 1))) := by
            simpa [transport, m] using hproduct
    _ =
      (postPAmplitude t k * Real.exp r) *
        Real.exp (-((transport - r) * m)) := hrewrite
    _ ≤
      ((hp t k).C3 * (hp t k).epsilon1) *
        Real.exp (-((transport - r) * m)) :=
          mul_le_mul_of_nonneg_right
            (by simpa [r] using hamplitude_loss t k)
            (Real.exp_nonneg _)
    _ ≤
      ((hp t k).C3 * (hp t k).epsilon1) *
        Real.exp (-(target * m)) :=
          mul_le_mul_of_nonneg_left htargetExp hC3_nonneg
    _ =
      ((hp t k).C3 * (hp t k).epsilon1) *
        balabanCMP116Lemma3Weight
          (hp t k).blockScale
          (hp t k).delta
          (hp t k).kappa
          (sourceMetric t k)
          Z := by
            simp [balabanCMP116Lemma3Weight, target, m]

end

end YangMills.RG

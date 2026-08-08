/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq237ComponentFamilySum
import YangMills.RG.BalabanCMP116Eq229ConnectedDomainSum
import YangMills.RG.BalabanCMP116Eq229CubeTreeMetric

/-!
# Rooted connected-component sum for CMP116 equation (2.37)

The finite component-family gas reduces the remaining entropy to the sum of
intrinsic component weights.  This module bounds that sum without ambient
volume dependence.

Each component atom is mapped injectively to a nonempty face-connected family
of four-dimensional coarse cubes contained in a fixed carrier.  Equation
(2.30), `|Y| / 24 ≤ d_k(Y)`, turns metric decay into a pure cardinal
fugacity.  The rooted lattice-animal theorem and the degree-eight cube graph
then give the explicit bound

`amplitude * |carrier| * (1 - 64*q)⁻¹`.

No post-summation estimate is stored in the source dictionary.
-/

namespace YangMills.RG

noncomputable section

open scoped BigOperators

/-- Source dictionary for the connected components entering equation (2.37).
The atom-to-domain map is injective on the actual finite universe, so no
uncontrolled multiplicity is hidden in the rooted-animal estimate. -/
structure CMP116Eq237RootedCubeComponentDictionary
    {L : ℕ} [NeZero L] {ιC : Type*}
    (atoms : Finset ιC)
    (atomWeight : ιC → ℝ)
    (metric : ιC → ℕ)
    (carrier : Finset (Cube 4 L))
    (amplitude decay : ℝ) where
  domainOf : ιC → Finset (Cube 4 L)
  domain_injective :
    Set.InjOn domainOf atoms
  domain_nonempty :
    ∀ Zi, Zi ∈ atoms → (domainOf Zi).Nonempty
  domain_connected :
    ∀ Zi, Zi ∈ atoms →
      walkConnected (cmp116CubeFaceAdj L) (domainOf Zi)
  domain_subset :
    ∀ Zi, Zi ∈ atoms →
      domainOf Zi ⊆ carrier
  metric_card :
    ∀ Zi, Zi ∈ atoms →
      ((domainOf Zi).card : ℝ) / 24 ≤ (metric Zi : ℝ)
  atomWeight_nonneg :
    ∀ Zi, Zi ∈ atoms → 0 ≤ atomWeight Zi
  atomWeight_le :
    ∀ Zi, Zi ∈ atoms →
      atomWeight Zi ≤
        amplitude * Real.exp (-(decay * (metric Zi : ℝ)))

/-- Equation (2.30) converts metric decay into cardinal fugacity. -/
theorem cmp116Eq237_exp_neg_metric_le_cardWeight
    {V : Type*}
    (decay : ℝ) (metric : Finset V → ℕ) (Y : Finset V)
    (hdecay : 0 ≤ decay)
    (hEq230 : (Y.card : ℝ) / 24 ≤ (metric Y : ℝ)) :
    Real.exp (-(decay * (metric Y : ℝ))) ≤
      Real.exp (-(decay / 24)) ^ Y.card := by
  have hscaled :
      decay * ((Y.card : ℝ) / 24) ≤
        decay * (metric Y : ℝ) :=
    mul_le_mul_of_nonneg_left hEq230 hdecay
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The intrinsic atom weights are summable by a rooted connected-domain
bound.  The only geometric size remaining is the physical carrier cardinality,
never the cardinality of the ambient torus. -/
theorem cmp116Eq237_rootedCubeComponentWeightSum_le
    {L : ℕ} [NeZero L] {ιC : Type*}
    (atoms : Finset ιC)
    (atomWeight : ιC → ℝ)
    (metric : ιC → ℕ)
    (carrier : Finset (Cube 4 L))
    (amplitude decay : ℝ)
    (D :
      CMP116Eq237RootedCubeComponentDictionary
        atoms atomWeight metric carrier amplitude decay)
    (hamplitude : 0 ≤ amplitude)
    (hdecay : 0 ≤ decay)
    (hsmall : 64 * Real.exp (-(decay / 24)) < 1) :
    (∑ Zi ∈ atoms, atomWeight Zi) ≤
      amplitude *
        ((carrier.card : ℝ) *
          (1 - 64 * Real.exp (-(decay / 24)))⁻¹) := by
  classical
  let q : ℝ := Real.exp (-(decay / 24))
  let family : Finset (Finset (Cube 4 L)) :=
    atoms.image D.domainOf
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hdomains :
      ∀ Y ∈ family,
        Y.Nonempty ∧ walkConnected (cmp116CubeFaceAdj L) Y := by
    intro Y hY
    rw [Finset.mem_image] at hY
    rcases hY with ⟨Zi, hZi, rfl⟩
    exact ⟨D.domain_nonempty Zi hZi, D.domain_connected Zi hZi⟩
  have hfamily_subset :
      ∀ Y ∈ family, Y ⊆ carrier := by
    intro Y hY
    rw [Finset.mem_image] at hY
    rcases hY with ⟨Zi, hZi, rfl⟩
    exact D.domain_subset Zi hZi
  have hfilter :
      family.filter (fun Y => Y ⊆ carrier) = family := by
    ext Y
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.1
    · intro hY
      exact ⟨hY, hfamily_subset Y hY⟩
  have hanimal :
      (∑ Y ∈ family, q ^ Y.card) ≤
        (carrier.card : ℝ) *
          (1 - 64 * q)⁻¹ := by
    have hsmall' : (8 : ℝ) ^ 2 * q < 1 := by
      norm_num [q]
      simpa using hsmall
    have h :=
      connectedDomainFamily_sum_pow_card_le
        family carrier hdomains
        (cmp116CubeFaceAdj_degree_le_eight L)
        (Δ := 8) (q := q) (by norm_num) hq0
        hsmall'
    norm_num [hfilter] at h ⊢
    exact h
  have hpoint :
      ∀ Zi ∈ atoms,
        atomWeight Zi ≤
          amplitude * q ^ (D.domainOf Zi).card := by
    intro Zi hZi
    calc
      atomWeight Zi ≤
          amplitude * Real.exp (-(decay * (metric Zi : ℝ))) :=
        D.atomWeight_le Zi hZi
      _ ≤
          amplitude * q ^ (D.domainOf Zi).card := by
        apply mul_le_mul_of_nonneg_left _ hamplitude
        simpa [q] using
          cmp116Eq237_exp_neg_metric_le_cardWeight
            decay (fun _Y => metric Zi) (D.domainOf Zi)
            hdecay (D.metric_card Zi hZi)
  have hsum_image :
      (∑ Y ∈ family, q ^ Y.card) =
        ∑ Zi ∈ atoms, q ^ (D.domainOf Zi).card := by
    simpa [family] using
      (Finset.sum_image
        (s := atoms)
        (g := D.domainOf)
        (f := fun Y => q ^ Y.card)
        D.domain_injective)
  calc
    (∑ Zi ∈ atoms, atomWeight Zi) ≤
      ∑ Zi ∈ atoms,
        amplitude * q ^ (D.domainOf Zi).card := by
          exact Finset.sum_le_sum hpoint
    _ =
      amplitude *
        (∑ Zi ∈ atoms, q ^ (D.domainOf Zi).card) := by
          rw [Finset.mul_sum]
    _ =
      amplitude * (∑ Y ∈ family, q ^ Y.card) := by
          rw [hsum_image]
    _ ≤
      amplitude *
        ((carrier.card : ℝ) * (1 - 64 * q)⁻¹) :=
          mul_le_mul_of_nonneg_left hanimal hamplitude
    _ =
      amplitude *
        ((carrier.card : ℝ) *
          (1 - 64 * Real.exp (-(decay / 24)))⁻¹) := rfl

/-- Elementary tangent bound for the positive real exponential. -/
private theorem cmp116Eq237_exp_sub_one_le_mul_exp_of_nonneg
    {x : ℝ} (_hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have hbase := Real.add_one_le_exp (-x)
  have hsmall : 1 - Real.exp (-x) ≤ x := by linarith
  have hmul :=
    mul_le_mul_of_nonneg_left hsmall (Real.exp_pos x).le
  have hinv : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith

/-- Extract the leading activity from the nonempty component gas after a
rooted bound on the atom sum. -/
theorem cmp116Eq237_exp_componentSum_sub_one_le_amplitude_mul
    {ιC : Type*}
    (atoms : Finset ιC) (atomWeight : ιC → ℝ)
    (amplitude rootedBound : ℝ)
    (hatom_nonneg :
      ∀ Zi, Zi ∈ atoms → 0 ≤ atomWeight Zi)
    (hamplitude : 0 ≤ amplitude)
    (hrootedBound : 0 ≤ rootedBound)
    (hsum :
      (∑ Zi ∈ atoms, atomWeight Zi) ≤
        amplitude * rootedBound) :
    Real.exp (∑ Zi ∈ atoms, atomWeight Zi) - 1 ≤
      amplitude *
        (rootedBound * Real.exp (amplitude * rootedBound)) := by
  have hsum_nonneg :
      0 ≤ ∑ Zi ∈ atoms, atomWeight Zi :=
    Finset.sum_nonneg fun Zi hZi => hatom_nonneg Zi hZi
  have htarget_nonneg :
      0 ≤ amplitude * rootedBound :=
    mul_nonneg hamplitude hrootedBound
  have hexp_mono :
      Real.exp (∑ Zi ∈ atoms, atomWeight Zi) - 1 ≤
        Real.exp (amplitude * rootedBound) - 1 := by
    linarith [Real.exp_le_exp.mpr hsum]
  have hlinear :=
    cmp116Eq237_exp_sub_one_le_mul_exp_of_nonneg htarget_nonneg
  calc
    Real.exp (∑ Zi ∈ atoms, atomWeight Zi) - 1 ≤
        Real.exp (amplitude * rootedBound) - 1 := hexp_mono
    _ ≤
        (amplitude * rootedBound) *
          Real.exp (amplitude * rootedBound) := hlinear
    _ =
      amplitude *
        (rootedBound * Real.exp (amplitude * rootedBound)) := by ring

/-- Explicit rooted-animal factor after summing connected component atoms. -/
def cmp116Eq237RootedComponentBound
    (carrierCard : ℕ) (decay : ℝ) : ℝ :=
  (carrierCard : ℝ) *
    (1 - 64 * Real.exp (-(decay / 24)))⁻¹

/-- Explicit factor remaining after the nonempty component gas is summed and
its leading activity has been extracted. -/
def cmp116Eq237PostComponentBudget
    (gaussian amplitude : ℝ) (carrierCard : ℕ) (decay : ℝ) : ℝ :=
  gaussian *
    (cmp116Eq237RootedComponentBound carrierCard decay *
      Real.exp
        (amplitude *
          cmp116Eq237RootedComponentBound carrierCard decay))

/-- Linear coefficient controlling the rooted component bound once the
carrier cardinality is bounded linearly by the source metric. -/
def cmp116Eq237RootedComponentLinearRate
    (carrierRate decay : ℝ) : ℝ :=
  carrierRate * (1 - 64 * Real.exp (-(decay / 24)))⁻¹

/-- The explicit post-component prefactor is absorbed by the entropy reserve
from linear source-cardinality and carrier-cardinality dictionaries.

The scalar budget has three transparent contributions:

* Gaussian volume: `volumeRate * sourceCardRate`;
* the rooted prefactor itself: `rootedLinearRate`; and
* its exponential: `amplitude * rootedLinearRate`.
-/
theorem cmp116Eq237PostComponentBudget_le_exp_of_linearCards_rate
    (Calpha5 alpha5 : ℝ)
    (sourceCard carrierCard sourceMetric : ℕ)
    (amplitude entropyRate sourceCardRate carrierRate targetRate : ℝ)
    (hvolumeRate : 0 ≤ Calpha5 * alpha5)
    (hamplitude : 0 ≤ amplitude)
    (hcarrierRate : 0 ≤ carrierRate)
    (hsmall :
      64 * Real.exp (-(entropyRate / 24)) < 1)
    (hsourceCard :
      (sourceCard : ℝ) ≤ sourceCardRate * (sourceMetric : ℝ))
    (hcarrierCard :
      (carrierCard : ℝ) ≤ carrierRate * (sourceMetric : ℝ))
    (hbudget :
      Calpha5 * alpha5 * sourceCardRate +
          cmp116Eq237RootedComponentLinearRate
            carrierRate entropyRate +
          amplitude *
            cmp116Eq237RootedComponentLinearRate
              carrierRate entropyRate ≤
        targetRate) :
    cmp116Eq237PostComponentBudget
        (cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 sourceCard)
        amplitude carrierCard entropyRate ≤
      Real.exp (targetRate * (sourceMetric : ℝ)) := by
  let denomInv : ℝ :=
    (1 - 64 * Real.exp (-(entropyRate / 24)))⁻¹
  let rootedLinearRate : ℝ :=
    cmp116Eq237RootedComponentLinearRate
      carrierRate entropyRate
  let rootedBound : ℝ :=
    cmp116Eq237RootedComponentBound carrierCard entropyRate
  let m : ℝ := (sourceMetric : ℝ)
  have hdenom :
      0 < 1 - 64 * Real.exp (-(entropyRate / 24)) := by
    linarith
  have hdenomInv : 0 ≤ denomInv := by
    exact inv_nonneg.mpr hdenom.le
  have hm : 0 ≤ m := by
    exact Nat.cast_nonneg _
  have hrootedLinearRate : 0 ≤ rootedLinearRate := by
    dsimp [rootedLinearRate,
      cmp116Eq237RootedComponentLinearRate, denomInv]
    exact mul_nonneg hcarrierRate hdenomInv
  have hrooted :
      rootedBound ≤ rootedLinearRate * m := by
    dsimp [rootedBound, cmp116Eq237RootedComponentBound,
      rootedLinearRate, cmp116Eq237RootedComponentLinearRate,
      denomInv]
    calc
      (carrierCard : ℝ) *
          (1 - 64 * Real.exp (-(entropyRate / 24)))⁻¹ ≤
        (carrierRate * m) *
          (1 - 64 * Real.exp (-(entropyRate / 24)))⁻¹ :=
            mul_le_mul_of_nonneg_right hcarrierCard hdenomInv
      _ =
        (carrierRate *
          (1 - 64 * Real.exp (-(entropyRate / 24)))⁻¹) * m := by
            ring
  have hrooted_nonneg : 0 ≤ rootedBound := by
    dsimp [rootedBound, cmp116Eq237RootedComponentBound]
    exact mul_nonneg (Nat.cast_nonneg _) hdenomInv
  have hrooted_exp :
      rootedBound ≤ Real.exp (rootedLinearRate * m) := by
    have hx : 0 ≤ rootedLinearRate * m :=
      mul_nonneg hrootedLinearRate hm
    have hxe : rootedLinearRate * m ≤
        Real.exp (rootedLinearRate * m) := by
      have h := Real.add_one_le_exp (rootedLinearRate * m)
      linarith
    exact hrooted.trans hxe
  have hgaussian :
      cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 sourceCard ≤
        Real.exp
          ((Calpha5 * alpha5 * sourceCardRate) * m) := by
    unfold cmp116Eq226GaussianVolumeFactor
    apply Real.exp_le_exp.mpr
    calc
      Calpha5 * alpha5 * (sourceCard : ℝ) ≤
          (Calpha5 * alpha5) * (sourceCardRate * m) :=
        mul_le_mul_of_nonneg_left hsourceCard hvolumeRate
      _ =
        (Calpha5 * alpha5 * sourceCardRate) * m := by ring
  have hsourceExp :
      Real.exp (amplitude * rootedBound) ≤
        Real.exp ((amplitude * rootedLinearRate) * m) := by
    apply Real.exp_le_exp.mpr
    calc
      amplitude * rootedBound ≤
          amplitude * (rootedLinearRate * m) :=
        mul_le_mul_of_nonneg_left hrooted hamplitude
      _ = (amplitude * rootedLinearRate) * m := by ring
  have hproduct :
      cmp116Eq237PostComponentBudget
          (cmp116Eq226GaussianVolumeFactor
            Calpha5 alpha5 sourceCard)
          amplitude carrierCard entropyRate ≤
        Real.exp
          (((Calpha5 * alpha5 * sourceCardRate) +
              rootedLinearRate +
              amplitude * rootedLinearRate) * m) := by
    unfold cmp116Eq237PostComponentBudget
    have hstep1 :
        cmp116Eq226GaussianVolumeFactor
              Calpha5 alpha5 sourceCard *
            rootedBound ≤
          Real.exp
              ((Calpha5 * alpha5 * sourceCardRate) * m) *
            Real.exp (rootedLinearRate * m) := by
      calc
        cmp116Eq226GaussianVolumeFactor
              Calpha5 alpha5 sourceCard *
            rootedBound ≤
          Real.exp
              ((Calpha5 * alpha5 * sourceCardRate) * m) *
            rootedBound :=
              mul_le_mul_of_nonneg_right hgaussian hrooted_nonneg
        _ ≤
          Real.exp
              ((Calpha5 * alpha5 * sourceCardRate) * m) *
            Real.exp (rootedLinearRate * m) :=
              mul_le_mul_of_nonneg_left hrooted_exp
                (Real.exp_nonneg _)
    have hstep2 :
        (cmp116Eq226GaussianVolumeFactor
              Calpha5 alpha5 sourceCard *
            rootedBound) *
            Real.exp (amplitude * rootedBound) ≤
          (Real.exp
              ((Calpha5 * alpha5 * sourceCardRate) * m) *
            Real.exp (rootedLinearRate * m)) *
            Real.exp ((amplitude * rootedLinearRate) * m) := by
      calc
        (cmp116Eq226GaussianVolumeFactor
              Calpha5 alpha5 sourceCard *
            rootedBound) *
            Real.exp (amplitude * rootedBound) ≤
          (Real.exp
              ((Calpha5 * alpha5 * sourceCardRate) * m) *
            Real.exp (rootedLinearRate * m)) *
            Real.exp (amplitude * rootedBound) :=
              mul_le_mul_of_nonneg_right hstep1 (Real.exp_nonneg _)
        _ ≤
          (Real.exp
              ((Calpha5 * alpha5 * sourceCardRate) * m) *
            Real.exp (rootedLinearRate * m)) *
            Real.exp ((amplitude * rootedLinearRate) * m) :=
              mul_le_mul_of_nonneg_left hsourceExp
                (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    calc
      cmp116Eq226GaussianVolumeFactor
            Calpha5 alpha5 sourceCard *
          (rootedBound * Real.exp (amplitude * rootedBound)) =
        (cmp116Eq226GaussianVolumeFactor
            Calpha5 alpha5 sourceCard * rootedBound) *
          Real.exp (amplitude * rootedBound) := by ring
      _ ≤
        (Real.exp
            ((Calpha5 * alpha5 * sourceCardRate) * m) *
          Real.exp (rootedLinearRate * m)) *
          Real.exp ((amplitude * rootedLinearRate) * m) := hstep2
      _ =
        Real.exp
          (((Calpha5 * alpha5 * sourceCardRate) +
              rootedLinearRate +
              amplitude * rootedLinearRate) * m) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  exact hproduct.trans
    (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right
        (by simpa [rootedLinearRate] using hbudget) hm))

/-- Backwards-compatible specialization in which the available absorption
rate is the component-entropy reserve itself. -/
theorem cmp116Eq237PostComponentBudget_le_exp_of_linearCards
    (Calpha5 alpha5 : ℝ)
    (sourceCard carrierCard sourceMetric : ℕ)
    (amplitude entropyRate sourceCardRate carrierRate : ℝ)
    (hvolumeRate : 0 ≤ Calpha5 * alpha5)
    (hamplitude : 0 ≤ amplitude)
    (hcarrierRate : 0 ≤ carrierRate)
    (hsmall :
      64 * Real.exp (-(entropyRate / 24)) < 1)
    (hsourceCard :
      (sourceCard : ℝ) ≤ sourceCardRate * (sourceMetric : ℝ))
    (hcarrierCard :
      (carrierCard : ℝ) ≤ carrierRate * (sourceMetric : ℝ))
    (hbudget :
      Calpha5 * alpha5 * sourceCardRate +
          cmp116Eq237RootedComponentLinearRate
            carrierRate entropyRate +
          amplitude *
            cmp116Eq237RootedComponentLinearRate
              carrierRate entropyRate ≤
        entropyRate) :
    cmp116Eq237PostComponentBudget
        (cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 sourceCard)
        amplitude carrierCard entropyRate ≤
      Real.exp (entropyRate * (sourceMetric : ℝ)) :=
  cmp116Eq237PostComponentBudget_le_exp_of_linearCards_rate
    Calpha5 alpha5 sourceCard carrierCard sourceMetric
    amplitude entropyRate sourceCardRate carrierRate entropyRate
    hvolumeRate hamplitude hcarrierRate hsmall
    hsourceCard hcarrierCard hbudget

/-- Source-composed post-`Z0'` estimate: component-family entropy, equation
(2.30), rooted-animal summation, and extraction of the leading activity are
all performed internally.  The remaining factor is explicit and contains no
sum over `Z0'` or connected components. -/
theorem cmp116Eq237_fixedZ0PrimeSum_le_amplitude_mul_rootedBudget
    {L : ℕ} [NeZero L] {σ ιZ0' ιC : Type*}
    (hp : CMP116Lemma3Parameters)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (index : σ → Finset ιZ0')
    (componentAtomMetric : σ → ιC → ℕ)
    (componentCarrier : σ → Finset (Cube 4 L))
    (Z : σ)
    (hkappa1 : 1 ≤ hp.kappa1)
    (E :
      CMP116Eq237ComponentFamilyEncoding
        (index Z)
        (components Z)
        (fun Z0' Zi =>
          cmp116Eq237Amplitude
              hp.blockScale C237 hp.epsilon2 *
            Real.exp
              (-(((1 - 7 * hp.delta) / 2) *
                (hp.blockScale : ℝ) * hp.kappa *
                  (componentMetric Z Z0' Zi : ℝ)))))
    (hcomponents_nonempty :
      ∀ Z0', Z0' ∈ index Z → (components Z Z0').Nonempty)
    (D :
      CMP116Eq237RootedCubeComponentDictionary
        E.componentUniverse E.atomWeight
        (componentAtomMetric Z) (componentCarrier Z)
        (cmp116Eq237Amplitude
          hp.blockScale C237 hp.epsilon2)
        (((1 - 7 * hp.delta) / 2) *
          (hp.blockScale : ℝ) * hp.kappa))
    (hamplitude :
      0 ≤ cmp116Eq237Amplitude
        hp.blockScale C237 hp.epsilon2)
    (hdecay :
      0 ≤
        ((1 - 7 * hp.delta) / 2) *
          (hp.blockScale : ℝ) * hp.kappa)
    (hsmall :
      64 *
        Real.exp
          (-(
            (((1 - 7 * hp.delta) / 2) *
              (hp.blockScale : ℝ) * hp.kappa) / 24)) < 1) :
    (∑ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0') ≤
      cmp116Eq237Amplitude
          hp.blockScale C237 hp.epsilon2 *
        cmp116Eq237PostComponentBudget
          (cmp116Eq226GaussianVolumeFactor
            Calpha5 alpha5 (sourceCard Z))
          (cmp116Eq237Amplitude
            hp.blockScale C237 hp.epsilon2)
          (componentCarrier Z).card
          (((1 - 7 * hp.delta) / 2) *
            (hp.blockScale : ℝ) * hp.kappa) := by
  classical
  let amplitude : ℝ :=
    cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2
  let decay : ℝ :=
    ((1 - 7 * hp.delta) / 2) *
      (hp.blockScale : ℝ) * hp.kappa
  let rootedBound : ℝ :=
    cmp116Eq237RootedComponentBound
      (componentCarrier Z).card decay
  let gaussian : ℝ :=
    cmp116Eq226GaussianVolumeFactor
      Calpha5 alpha5 (sourceCard Z)
  have hgaussian : 0 ≤ gaussian := by
    dsimp [gaussian, cmp116Eq226GaussianVolumeFactor]
    positivity
  have hrootedBound : 0 ≤ rootedBound := by
    have hdenom :
        0 < 1 - 64 * Real.exp (-(decay / 24)) := by
      dsimp [decay] at hsmall ⊢
      linarith
    exact mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr hdenom.le)
  have hfixed :=
    cmp116Eq237_fixedZ0PrimeSum_le_gaussian_mul_exp_componentSum_sub_one
      hp localizationScale C237 Calpha5 alpha5
      sourceCard gapCard components componentMetric index Z
      hkappa1 E hcomponents_nonempty
  have hroot :
      (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) ≤
        amplitude * rootedBound := by
    simpa [amplitude, decay, rootedBound] using
      cmp116Eq237_rootedCubeComponentWeightSum_le
        E.componentUniverse E.atomWeight
        (componentAtomMetric Z) (componentCarrier Z)
        amplitude decay D
        (by simpa [amplitude] using hamplitude)
        (by simpa [decay] using hdecay)
        (by simpa [decay] using hsmall)
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
  calc
    (∑ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0') ≤
      gaussian *
        (Real.exp
            (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1) := by
              simpa [gaussian] using hfixed
    _ ≤
      gaussian *
        (amplitude *
          (rootedBound * Real.exp (amplitude * rootedBound))) :=
            mul_le_mul_of_nonneg_left hgas hgaussian
    _ =
      amplitude *
        (gaussian *
          (rootedBound * Real.exp (amplitude * rootedBound))) := by ring
    _ =
      cmp116Eq237Amplitude
          hp.blockScale C237 hp.epsilon2 *
        cmp116Eq237PostComponentBudget
          (cmp116Eq226GaussianVolumeFactor
            Calpha5 alpha5 (sourceCard Z))
          (cmp116Eq237Amplitude
            hp.blockScale C237 hp.epsilon2)
          (componentCarrier Z).card
          (((1 - 7 * hp.delta) / 2) *
            (hp.blockScale : ℝ) * hp.kappa) := by
      rfl

end

end YangMills.RG

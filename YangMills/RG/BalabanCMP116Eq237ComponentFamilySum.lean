/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq237ComponentFiberEncoding
import YangMills.RG.AppendixFFiberEntropy

/-!
# Summing CMP116 equation-(2.37) component families

The fixed-`Z0'` fiber estimate leaves a finite sum over the possible outer
regions `Z0'`.  Such a region is determined by its finite family of connected
components.  This module turns that source dictionary into a gas bound:

`∑_{Z0'} ∏_{Zi ∈ components Z0'} factor(Z0', Zi)
  ≤ ∏_{Zi ∈ universe} (1 + atomWeight Zi)`.

The proof maps each region injectively to its component family, overcounts the
image by the full powerset of the component universe, and expands the latter
exactly.  No ambient-volume cardinality and no post-summation hypothesis occur.

This is the finite family-combinatorics step only.  A source constructor must
still provide the actual connected-component universe and bound its rooted
weights by the CMP116 decay estimates.
-/

namespace YangMills.RG

noncomputable section

open scoped BigOperators

/-- Source-facing encoding of a finite family of possible outer regions by
their connected components.  The factor attached to a component may initially
depend on the outer region, but it must be dominated by an intrinsic atom
weight on a common finite component universe. -/
structure CMP116Eq237ComponentFamilyEncoding
    {ιZ0' ιC : Type*}
    (index : Finset ιZ0')
    (components : ιZ0' → Finset ιC)
    (componentFactor : ιZ0' → ιC → ℝ) where
  componentUniverse : Finset ιC
  atomWeight : ιC → ℝ
  components_subset :
    ∀ Z0', Z0' ∈ index →
      components Z0' ⊆ componentUniverse
  components_ext :
    ∀ Z0'₁, Z0'₁ ∈ index →
      ∀ Z0'₂, Z0'₂ ∈ index →
        components Z0'₁ = components Z0'₂ →
          Z0'₁ = Z0'₂
  componentFactor_nonneg :
    ∀ Z0', Z0' ∈ index →
      ∀ Zi, Zi ∈ components Z0' →
        0 ≤ componentFactor Z0' Zi
  componentFactor_le_atomWeight :
    ∀ Z0', Z0' ∈ index →
      ∀ Zi, Zi ∈ components Z0' →
        componentFactor Z0' Zi ≤ atomWeight Zi
  atomWeight_nonneg :
    ∀ Zi, Zi ∈ componentUniverse →
      0 ≤ atomWeight Zi

/-- The sum over outer regions is bounded by the finite component gas.
Injectivity is required only on the physical index, so coincident component
families outside the source index are irrelevant. -/
theorem cmp116Eq237_componentFamilySum_le_prod_one_add
    {ιZ0' ιC : Type*}
    (index : Finset ιZ0')
    (components : ιZ0' → Finset ιC)
    (componentFactor : ιZ0' → ιC → ℝ)
    (E :
      CMP116Eq237ComponentFamilyEncoding
        index components componentFactor) :
    (∑ Z0' ∈ index,
        ∏ Zi ∈ components Z0', componentFactor Z0' Zi) ≤
      ∏ Zi ∈ E.componentUniverse, (1 + E.atomWeight Zi) := by
  classical
  have hpoint :
      ∀ Z0' ∈ index,
        (∏ Zi ∈ components Z0', componentFactor Z0' Zi) ≤
          ∏ Zi ∈ components Z0', E.atomWeight Zi := by
    intro Z0' hZ0'
    exact Finset.prod_le_prod
      (fun Zi hZi =>
        E.componentFactor_nonneg Z0' hZ0' Zi hZi)
      (fun Zi hZi =>
        E.componentFactor_le_atomWeight Z0' hZ0' Zi hZi)
  have hinj :
      Set.InjOn components index := by
    intro Z0'₁ hZ0'₁ Z0'₂ hZ0'₂ hEq
    exact E.components_ext Z0'₁ hZ0'₁ Z0'₂ hZ0'₂ hEq
  have hsum_image_eq :
      (∑ S ∈ index.image components,
          ∏ Zi ∈ S, E.atomWeight Zi) =
        ∑ Z0' ∈ index,
          ∏ Zi ∈ components Z0', E.atomWeight Zi := by
    simpa using
      (Finset.sum_image
        (s := index)
        (g := components)
        (f := fun S => ∏ Zi ∈ S, E.atomWeight Zi)
        hinj)
  have himage_subset :
      index.image components ⊆
        E.componentUniverse.powerset := by
    intro S hS
    rw [Finset.mem_image] at hS
    rcases hS with ⟨Z0', hZ0', rfl⟩
    rw [Finset.mem_powerset]
    exact E.components_subset Z0' hZ0'
  have hsum_image_le :
      (∑ S ∈ index.image components,
          ∏ Zi ∈ S, E.atomWeight Zi) ≤
        ∑ S ∈ E.componentUniverse.powerset,
          ∏ Zi ∈ S, E.atomWeight Zi := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      himage_subset
      (fun S hS _hnot =>
        Finset.prod_nonneg fun Zi hZi =>
          E.atomWeight_nonneg Zi
            ((Finset.mem_powerset.mp hS) hZi))
  calc
    (∑ Z0' ∈ index,
        ∏ Zi ∈ components Z0', componentFactor Z0' Zi) ≤
      ∑ Z0' ∈ index,
        ∏ Zi ∈ components Z0', E.atomWeight Zi := by
          exact Finset.sum_le_sum fun Z0' hZ0' =>
            hpoint Z0' hZ0'
    _ = ∑ S ∈ index.image components,
          ∏ Zi ∈ S, E.atomWeight Zi := hsum_image_eq.symm
    _ ≤ ∑ S ∈ E.componentUniverse.powerset,
          ∏ Zi ∈ S, E.atomWeight Zi := hsum_image_le
    _ = ∏ Zi ∈ E.componentUniverse, (1 + E.atomWeight Zi) := by
      exact (Finset.prod_one_add
        (s := E.componentUniverse) (f := E.atomWeight)).symm

/-- If every physical outer region has a nonempty component family, the empty
subset can be removed from the powerset overcount.  The result is the
source-useful bound `exp (sum atomWeight) - 1`, which retains the leading
small activity factor instead of paying for an artificial empty family. -/
theorem cmp116Eq237_componentFamilySum_le_exp_sum_sub_one
    {ιZ0' ιC : Type*}
    (index : Finset ιZ0')
    (components : ιZ0' → Finset ιC)
    (componentFactor : ιZ0' → ιC → ℝ)
    (E :
      CMP116Eq237ComponentFamilyEncoding
        index components componentFactor)
    (hcomponents_nonempty :
      ∀ Z0', Z0' ∈ index → (components Z0').Nonempty) :
    (∑ Z0' ∈ index,
        ∏ Zi ∈ components Z0', componentFactor Z0' Zi) ≤
      Real.exp
          (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1 := by
  classical
  have hpoint :
      ∀ Z0' ∈ index,
        (∏ Zi ∈ components Z0', componentFactor Z0' Zi) ≤
          ∏ Zi ∈ components Z0', E.atomWeight Zi := by
    intro Z0' hZ0'
    exact Finset.prod_le_prod
      (fun Zi hZi =>
        E.componentFactor_nonneg Z0' hZ0' Zi hZi)
      (fun Zi hZi =>
        E.componentFactor_le_atomWeight Z0' hZ0' Zi hZi)
  have hinj :
      Set.InjOn components index := by
    intro Z0'₁ hZ0'₁ Z0'₂ hZ0'₂ hEq
    exact E.components_ext Z0'₁ hZ0'₁ Z0'₂ hZ0'₂ hEq
  have hsum_image_eq :
      (∑ S ∈ index.image components,
          ∏ Zi ∈ S, E.atomWeight Zi) =
        ∑ Z0' ∈ index,
          ∏ Zi ∈ components Z0', E.atomWeight Zi := by
    simpa using
      (Finset.sum_image
        (s := index)
        (g := components)
        (f := fun S => ∏ Zi ∈ S, E.atomWeight Zi)
        hinj)
  have himage_subset :
      index.image components ⊆
        E.componentUniverse.powerset.erase ∅ := by
    intro S hS
    rw [Finset.mem_image] at hS
    rcases hS with ⟨Z0', hZ0', rfl⟩
    rw [Finset.mem_erase, Finset.mem_powerset]
    exact ⟨
      Finset.nonempty_iff_ne_empty.mp
        (hcomponents_nonempty Z0' hZ0'),
      E.components_subset Z0' hZ0'⟩
  have hsum_image_le :
      (∑ S ∈ index.image components,
          ∏ Zi ∈ S, E.atomWeight Zi) ≤
        ∑ S ∈ E.componentUniverse.powerset.erase ∅,
          ∏ Zi ∈ S, E.atomWeight Zi := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      himage_subset
      (fun S hS _hnot => by
        rw [Finset.mem_erase, Finset.mem_powerset] at hS
        exact Finset.prod_nonneg fun Zi hZi =>
          E.atomWeight_nonneg Zi (hS.2 hZi))
  calc
    (∑ Z0' ∈ index,
        ∏ Zi ∈ components Z0', componentFactor Z0' Zi) ≤
      ∑ Z0' ∈ index,
        ∏ Zi ∈ components Z0', E.atomWeight Zi := by
          exact Finset.sum_le_sum fun Z0' hZ0' =>
            hpoint Z0' hZ0'
    _ = ∑ S ∈ index.image components,
          ∏ Zi ∈ S, E.atomWeight Zi := hsum_image_eq.symm
    _ ≤ ∑ S ∈ E.componentUniverse.powerset.erase ∅,
          ∏ Zi ∈ S, E.atomWeight Zi := hsum_image_le
    _ ≤
      Real.exp
          (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1 :=
        sum_powerset_erase_empty_prod_le_exp_sub_one
          E.componentUniverse E.atomWeight E.atomWeight_nonneg

namespace CMP116Eq237ComponentFamilyEncoding

/-- Method form of the finite component-gas estimate. -/
theorem familySum
    {ιZ0' ιC : Type*}
    {index : Finset ιZ0'}
    {components : ιZ0' → Finset ιC}
    {componentFactor : ιZ0' → ιC → ℝ}
    (E :
      CMP116Eq237ComponentFamilyEncoding
        index components componentFactor) :
    (∑ Z0' ∈ index,
        ∏ Zi ∈ components Z0', componentFactor Z0' Zi) ≤
      ∏ Zi ∈ E.componentUniverse, (1 + E.atomWeight Zi) :=
  cmp116Eq237_componentFamilySum_le_prod_one_add
    index components componentFactor E

end CMP116Eq237ComponentFamilyEncoding

/-- The equation-(2.26) gap penalty is at most one once the printed
coefficient `kappa1 - 1` is nonnegative. -/
theorem cmp116Eq226GapFactor_le_one_of_one_le
    (kappa1 : ℝ) (localizationScale gapCard : ℕ)
    (hkappa1 : 1 ≤ kappa1) :
    cmp116Eq226GapFactor
        kappa1 localizationScale 1 gapCard ≤ 1 := by
  rw [cmp116Eq226GapFactor]
  have hcoeff :
      0 ≤
        (kappa1 - 1) *
          ((((localizationScale * 1 : ℕ) : ℝ) ^ 4)⁻¹) *
          (gapCard : ℝ) := by
    exact mul_nonneg
      (mul_nonneg
        (sub_nonneg.mpr hkappa1)
        (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) 4)))
      (Nat.cast_nonneg _)
  simpa only [Real.exp_zero] using
    Real.exp_le_exp.mpr (neg_nonpos.mpr hcoeff)

/-- The complete fixed-`Z0'` sum is bounded by the Gaussian volume factor
times the finite component gas.  The gap factor is discarded only through its
literal sign, while all component entropy is produced by the source family
encoding. -/
theorem cmp116Eq237_fixedZ0PrimeSum_le_gaussian_mul_componentGas
    {σ ιZ0' ιC : Type*}
    (hp : CMP116Lemma3Parameters)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (index : σ → Finset ιZ0')
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
                  (componentMetric Z Z0' Zi : ℝ))))) :
    (∑ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0') ≤
      cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 (sourceCard Z) *
        ∏ Zi ∈ E.componentUniverse, (1 + E.atomWeight Zi) := by
  classical
  let componentFactor : ιZ0' → ιC → ℝ :=
    fun Z0' Zi =>
      cmp116Eq237Amplitude
          hp.blockScale C237 hp.epsilon2 *
        Real.exp
          (-(((1 - 7 * hp.delta) / 2) *
            (hp.blockScale : ℝ) * hp.kappa *
              (componentMetric Z Z0' Zi : ℝ)))
  let gaussian : ℝ :=
    cmp116Eq226GaussianVolumeFactor
      Calpha5 alpha5 (sourceCard Z)
  have hgaussian : 0 ≤ gaussian := by
    dsimp [gaussian, cmp116Eq226GaussianVolumeFactor]
    positivity
  have hpoint :
      ∀ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
            hp localizationScale C237 Calpha5 alpha5
            sourceCard gapCard components componentMetric Z Z0' ≤
          gaussian *
            ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi := by
    intro Z0' hZ0'
    rw [
      cmp116Eq237FixedZ0PrimeWeight_eq_gap_mul_componentProduct_mul_gaussian]
    have hgap :=
      cmp116Eq226GapFactor_le_one_of_one_le
        hp.kappa1 localizationScale (gapCard Z Z0') hkappa1
    have hproduct_nonneg :
        0 ≤ ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi := by
      exact Finset.prod_nonneg fun Zi hZi =>
        E.componentFactor_nonneg Z0' hZ0' Zi hZi
    have hmul :
        cmp116Eq226GapFactor
              hp.kappa1 localizationScale 1 (gapCard Z Z0') *
            (∏ Zi ∈ components Z Z0', componentFactor Z0' Zi) ≤
          ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi := by
      calc
        cmp116Eq226GapFactor
              hp.kappa1 localizationScale 1 (gapCard Z Z0') *
            (∏ Zi ∈ components Z Z0', componentFactor Z0' Zi) ≤
          1 * (∏ Zi ∈ components Z Z0', componentFactor Z0' Zi) :=
            mul_le_mul_of_nonneg_right hgap hproduct_nonneg
        _ = ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi := one_mul _
    have :=
      mul_le_mul_of_nonneg_right hmul hgaussian
    simpa [cmp116Eq237ComponentProduct, componentFactor, gaussian,
      mul_assoc, mul_left_comm, mul_comm] using this
  have hfamily :
      (∑ Z0' ∈ index Z,
          ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi) ≤
        ∏ Zi ∈ E.componentUniverse, (1 + E.atomWeight Zi) := by
    simpa [componentFactor] using E.familySum
  calc
    (∑ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0') ≤
      ∑ Z0' ∈ index Z,
        gaussian *
          ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi := by
            exact Finset.sum_le_sum hpoint
    _ =
      gaussian *
        (∑ Z0' ∈ index Z,
          ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi) := by
            rw [Finset.mul_sum]
    _ ≤
      gaussian *
        ∏ Zi ∈ E.componentUniverse, (1 + E.atomWeight Zi) :=
          mul_le_mul_of_nonneg_left hfamily hgaussian
    _ =
      cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 (sourceCard Z) *
        ∏ Zi ∈ E.componentUniverse, (1 + E.atomWeight Zi) := rfl

/-- Nonempty source component families give the sharper fixed-`Z0'` bound
with the empty gas configuration removed. -/
theorem cmp116Eq237_fixedZ0PrimeSum_le_gaussian_mul_exp_componentSum_sub_one
    {σ ιZ0' ιC : Type*}
    (hp : CMP116Lemma3Parameters)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (index : σ → Finset ιZ0')
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
      ∀ Z0', Z0' ∈ index Z → (components Z Z0').Nonempty) :
    (∑ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0') ≤
      cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 (sourceCard Z) *
        (Real.exp
            (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1) := by
  classical
  let componentFactor : ιZ0' → ιC → ℝ :=
    fun Z0' Zi =>
      cmp116Eq237Amplitude
          hp.blockScale C237 hp.epsilon2 *
        Real.exp
          (-(((1 - 7 * hp.delta) / 2) *
            (hp.blockScale : ℝ) * hp.kappa *
              (componentMetric Z Z0' Zi : ℝ)))
  let gaussian : ℝ :=
    cmp116Eq226GaussianVolumeFactor
      Calpha5 alpha5 (sourceCard Z)
  have hgaussian : 0 ≤ gaussian := by
    dsimp [gaussian, cmp116Eq226GaussianVolumeFactor]
    positivity
  have hpoint :
      ∀ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
            hp localizationScale C237 Calpha5 alpha5
            sourceCard gapCard components componentMetric Z Z0' ≤
          gaussian *
            ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi := by
    intro Z0' hZ0'
    rw [
      cmp116Eq237FixedZ0PrimeWeight_eq_gap_mul_componentProduct_mul_gaussian]
    have hgap :=
      cmp116Eq226GapFactor_le_one_of_one_le
        hp.kappa1 localizationScale (gapCard Z Z0') hkappa1
    have hproduct_nonneg :
        0 ≤ ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi := by
      exact Finset.prod_nonneg fun Zi hZi =>
        E.componentFactor_nonneg Z0' hZ0' Zi hZi
    have hmul :
        cmp116Eq226GapFactor
              hp.kappa1 localizationScale 1 (gapCard Z Z0') *
            (∏ Zi ∈ components Z Z0', componentFactor Z0' Zi) ≤
          ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi := by
      calc
        cmp116Eq226GapFactor
              hp.kappa1 localizationScale 1 (gapCard Z Z0') *
            (∏ Zi ∈ components Z Z0', componentFactor Z0' Zi) ≤
          1 * (∏ Zi ∈ components Z Z0', componentFactor Z0' Zi) :=
            mul_le_mul_of_nonneg_right hgap hproduct_nonneg
        _ = ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi := one_mul _
    have :=
      mul_le_mul_of_nonneg_right hmul hgaussian
    simpa [cmp116Eq237ComponentProduct, componentFactor, gaussian,
      mul_assoc, mul_left_comm, mul_comm] using this
  have hfamily :
      (∑ Z0' ∈ index Z,
          ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi) ≤
        Real.exp
            (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1 := by
    simpa [componentFactor] using
      cmp116Eq237_componentFamilySum_le_exp_sum_sub_one
        (index Z) (components Z) componentFactor E hcomponents_nonempty
  calc
    (∑ Z0' ∈ index Z,
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0') ≤
      ∑ Z0' ∈ index Z,
        gaussian *
          ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi := by
            exact Finset.sum_le_sum hpoint
    _ =
      gaussian *
        (∑ Z0' ∈ index Z,
          ∏ Zi ∈ components Z Z0', componentFactor Z0' Zi) := by
            rw [Finset.mul_sum]
    _ ≤
      gaussian *
        (Real.exp
            (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1) :=
          mul_le_mul_of_nonneg_left hfamily hgaussian
    _ =
      cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 (sourceCard Z) *
        (Real.exp
            (∑ Zi ∈ E.componentUniverse, E.atomWeight Zi) - 1) := rfl

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq234GapSubsetSum
import YangMills.RG.BalabanCMP116Eq237ComponentFamilySum

/-!
# Joint CMP116 gap and component-family sum

The final equation-(2.37) summation indexes each outer region `Z0'` by two
pieces of source data:

* its gap `Z \ Z0'`, carrying the reserved equation-(2.34) Cauchy weight; and
* its nonempty family of connected components, carrying the component gas.

This module combines the two independently verified finite encodings.  It
does not discard either weight and it does not assume a post-summation bound.
The physical sum is bounded by the product of the gap powerset exponential
and the nonempty component-gas exponential.
-/

namespace YangMills.RG

noncomputable section

open scoped BigOperators

/-- A diagonal finite sum of products is bounded by the product of the two
nonnegative marginal sums. -/
private theorem sum_mul_le_sum_mul_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, i ∈ s → 0 ≤ a i)
    (hb : ∀ i, i ∈ s → 0 ≤ b i) :
    (∑ i ∈ s, a i * b i) ≤
      (∑ i ∈ s, a i) * (∑ i ∈ s, b i) := by
  have hbsum : 0 ≤ ∑ i ∈ s, b i :=
    Finset.sum_nonneg fun i hi => hb i hi
  calc
    (∑ i ∈ s, a i * b i) ≤
      ∑ i ∈ s, a i * (∑ j ∈ s, b j) := by
        exact Finset.sum_le_sum fun i hi => by
          apply mul_le_mul_of_nonneg_left _ (ha i hi)
          exact Finset.single_le_sum
            (fun j hj => hb j hj) hi
    _ = (∑ i ∈ s, a i) * (∑ j ∈ s, b j) := by
      rw [Finset.sum_mul]

/-- The source-indexed product of the reserved gap weight and the component
family weight is bounded by the product of the literal equation-(2.34)
exponential and the nonempty component-gas exponential. -/
theorem cmp116Eq237_gapComponentFamilySum_le
    {ιZ0' ιC α : Type*}
    [DecidableEq ιZ0'] [DecidableEq α]
    (index : Finset ιZ0')
    (gapCard : ιZ0' → ℕ)
    (localizationScale : ℕ)
    (components : ιZ0' → Finset ιC)
    (componentFactor : ιZ0' → ιC → ℝ)
    (Gap :
      CMP116Eq234GapIndexEncoding
        α index gapCard localizationScale)
    (Comp :
      CMP116Eq237ComponentFamilyEncoding
        index components componentFactor)
    (hcomponents_nonempty :
      ∀ Z0', Z0' ∈ index → (components Z0').Nonempty)
    (kappa1 : ℝ) :
    (∑ Z0' ∈ index,
        Real.exp
            (-(((kappa1 - 1) / 2) *
              (((localizationScale : ℝ) ^ 4)⁻¹) *
              (gapCard Z0' : ℝ))) *
          (∏ Zi ∈ components Z0',
            componentFactor Z0' Zi)) ≤
      Real.exp
          (Real.exp (-((kappa1 - 1) / 2)) *
            (Gap.carrier.card : ℝ)) *
        (Real.exp
            (∑ Zi ∈ Comp.componentUniverse,
              Comp.atomWeight Zi) - 1) := by
  let a : ιZ0' → ℝ := fun Z0' =>
    Real.exp
      (-(((kappa1 - 1) / 2) *
        (((localizationScale : ℝ) ^ 4)⁻¹) *
        (gapCard Z0' : ℝ)))
  let b : ιZ0' → ℝ := fun Z0' =>
    ∏ Zi ∈ components Z0', componentFactor Z0' Zi
  have ha : ∀ Z0', Z0' ∈ index → 0 ≤ a Z0' :=
    fun _ _ => (Real.exp_pos _).le
  have hb : ∀ Z0', Z0' ∈ index → 0 ≤ b Z0' := by
    intro Z0' hZ0'
    exact Finset.prod_nonneg fun Zi hZi =>
      Comp.componentFactor_nonneg Z0' hZ0' Zi hZi
  have hdiag :
      (∑ Z0' ∈ index, a Z0' * b Z0') ≤
        (∑ Z0' ∈ index, a Z0') *
          (∑ Z0' ∈ index, b Z0') :=
    sum_mul_le_sum_mul_sum index a b ha hb
  have hgap :
      (∑ Z0' ∈ index, a Z0') ≤
        Real.exp
          (Real.exp (-((kappa1 - 1) / 2)) *
            (Gap.carrier.card : ℝ)) := by
    simpa [a] using
      cmp116Eq234_gapIndexSum_le_exp
        index gapCard localizationScale Gap kappa1
  have hcomponent :
      (∑ Z0' ∈ index, b Z0') ≤
        Real.exp
            (∑ Zi ∈ Comp.componentUniverse,
              Comp.atomWeight Zi) - 1 := by
    simpa [b] using
      cmp116Eq237_componentFamilySum_le_exp_sum_sub_one
        index components componentFactor Comp hcomponents_nonempty
  have hcomponentTarget_nonneg :
      0 ≤
        Real.exp
            (∑ Zi ∈ Comp.componentUniverse,
              Comp.atomWeight Zi) - 1 := by
    have hsum :
        0 ≤ ∑ Zi ∈ Comp.componentUniverse, Comp.atomWeight Zi :=
      Finset.sum_nonneg fun Zi hZi => Comp.atomWeight_nonneg Zi hZi
    exact sub_nonneg.mpr (Real.one_le_exp hsum)
  have hgapTarget_nonneg :
      0 ≤
        Real.exp
          (Real.exp (-((kappa1 - 1) / 2)) *
            (Gap.carrier.card : ℝ)) :=
    (Real.exp_pos _).le
  calc
    (∑ Z0' ∈ index,
        Real.exp
            (-(((kappa1 - 1) / 2) *
              (((localizationScale : ℝ) ^ 4)⁻¹) *
              (gapCard Z0' : ℝ))) *
          (∏ Zi ∈ components Z0',
            componentFactor Z0' Zi)) =
      ∑ Z0' ∈ index, a Z0' * b Z0' := rfl
    _ ≤
      (∑ Z0' ∈ index, a Z0') *
        (∑ Z0' ∈ index, b Z0') := hdiag
    _ ≤
      Real.exp
          (Real.exp (-((kappa1 - 1) / 2)) *
            (Gap.carrier.card : ℝ)) *
        (Real.exp
            (∑ Zi ∈ Comp.componentUniverse,
              Comp.atomWeight Zi) - 1) :=
      mul_le_mul hgap hcomponent
        (Finset.sum_nonneg fun Z0' hZ0' => hb Z0' hZ0')
        hgapTarget_nonneg

end

end YangMills.RG

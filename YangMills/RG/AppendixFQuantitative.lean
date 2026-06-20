/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHoleTargetFamily

/-!
# Appendix F: finite quantitative first-activity bounds

This module starts the quantitative Appendix-F layer after the exact finite
target-family compiler.  It proves only the source-independent finite norm
step for the first connected activity `K(Y)`: a raw pointwise decay bound on
`h i` gives a positive connected-cover majorant for the finite sum of raw Mayer
products.

No connected-cover entropy, modified-metric stitching, ultralocal integration,
second Ursell expansion, or Yang--Mills raw activity estimate is proved here.
The output deliberately exposes the remaining finite connected-cover sum that
Dimock Appendix F equations (641)--(642) must control.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open Finset
open scoped BigOperators

private theorem exp_neg_mul_nat_le_one {ι : Type*} (metric : ι → ℕ)
    {κ : ℝ} (hκ : 0 ≤ κ) (i : ι) :
    Real.exp (-κ * (metric i : ℝ)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ) (Nat.cast_nonneg _)

private theorem rawMayer_factor_norm_le_metric
    {ι : Type*} (metric : ι → ℕ) (h : ι → ℂ)
    {H0 κ : ℝ} (hH0 : 0 ≤ H0) (hH01 : H0 ≤ 1) (hκ : 0 ≤ κ)
    {i : ι}
    (hraw : ‖h i‖ ≤ H0 * Real.exp (-κ * (metric i : ℝ))) :
    ‖Complex.exp (h i) - 1‖ ≤
      (2 * H0) * Real.exp (-κ * (metric i : ℝ)) := by
  have hdecay_nonneg : 0 ≤ Real.exp (-κ * (metric i : ℝ)) :=
    Real.exp_nonneg _
  have hsmall_rhs :
      H0 * Real.exp (-κ * (metric i : ℝ)) ≤ 1 := by
    calc
      H0 * Real.exp (-κ * (metric i : ℝ)) ≤ H0 * 1 := by
        exact mul_le_mul_of_nonneg_left
          (exp_neg_mul_nat_le_one metric hκ i) hH0
      _ ≤ 1 := by simpa using hH01
  have hsmall : ‖h i‖ ≤ 1 := hraw.trans hsmall_rhs
  calc
    ‖Complex.exp (h i) - 1‖ ≤ 2 * ‖h i‖ :=
      Complex.norm_exp_sub_one_le hsmall
    _ ≤ 2 * (H0 * Real.exp (-κ * (metric i : ℝ))) :=
      mul_le_mul_of_nonneg_left hraw zero_le_two
    _ = (2 * H0) * Real.exp (-κ * (metric i : ℝ)) := by ring

/-- One connected raw cover is bounded by the product of its factorwise
metric majorants.  This is the finite product step underneath the first
Appendix-F connected activity `K(Y)`. -/
theorem norm_appendixFComponentWeight_expSubOne_le_metricProduct
    {ι : Type*} [DecidableEq ι]
    (C : Finset ι) (metric : ι → ℕ) (h : ι → ℂ)
    (H0 κ : ℝ)
    (hH0 : 0 ≤ H0) (hH01 : H0 ≤ 1) (hκ : 0 ≤ κ)
    (hraw : ∀ i, i ∈ C →
      ‖h i‖ ≤ H0 * Real.exp (-κ * (metric i : ℝ))) :
    ‖appendixFComponentWeight (fun i => Complex.exp (h i) - 1) C‖ ≤
      ∏ i ∈ C, (2 * H0) * Real.exp (-κ * (metric i : ℝ)) := by
  classical
  unfold appendixFComponentWeight
  rw [norm_prod]
  refine Finset.prod_le_prod ?nonneg ?bound
  · intro i _hi
    exact norm_nonneg (Complex.exp (h i) - 1)
  · intro i hi
    exact rawMayer_factor_norm_le_metric metric h hH0 hH01 hκ
      (hraw i hi)

/-- Product form of the finite first-activity majorant.  It is just the
triangle inequality over the target fiber plus the factorwise raw-Mayer bound.
-/
theorem norm_appendixFConnectedActivity_le_metricProductCoverSum
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site)
    (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (metric : ι → ℕ) (h : ι → ℂ)
    (Y : Finset Site) (H0 κ : ℝ)
    (hH0 : 0 ≤ H0) (hH01 : H0 ≤ 1) (hκ : 0 ≤ κ)
    (hraw : ∀ i, i ∈ Λ →
      ‖h i‖ ≤ H0 * Real.exp (-κ * (metric i : ℝ))) :
    ‖appendixFConnectedActivity Ω overlapSupport targetSupport Λ h Y‖ ≤
      ∑ C ∈ appendixFTargetFiber Ω overlapSupport targetSupport Λ Y,
        ∏ i ∈ C, (2 * H0) * Real.exp (-κ * (metric i : ℝ)) := by
  classical
  let fiber := appendixFTargetFiber Ω overlapSupport targetSupport Λ Y
  calc
    ‖appendixFConnectedActivity Ω overlapSupport targetSupport Λ h Y‖
        = ‖∑ C ∈ fiber, ∏ i ∈ C, (Complex.exp (h i) - 1)‖ := by
          simp [appendixFConnectedActivity, appendixFTargetFiber, fiber]
    _ ≤ ∑ C ∈ fiber, ‖∏ i ∈ C, (Complex.exp (h i) - 1)‖ := by
          simpa using
            (norm_sum_le fiber
              (fun C => ∏ i ∈ C, (Complex.exp (h i) - 1)))
    _ ≤ ∑ C ∈ fiber,
          ∏ i ∈ C, (2 * H0) * Real.exp (-κ * (metric i : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro C hC
          have hCregion :
              C ∈ appendixFConnectedCoverRegion Ω overlapSupport Λ :=
            ((mem_appendixFTargetFiber_iff Ω overlapSupport targetSupport
              Λ Y C).mp hC).1
          have hCsub : C ⊆ Λ :=
            ((mem_appendixFConnectedCoverRegion_iff Ω overlapSupport
              Λ C).mp hCregion).1
          exact norm_appendixFComponentWeight_expSubOne_le_metricProduct
            C metric h H0 κ hH0 hH01 hκ
            (fun i hi => hraw i (hCsub hi))

/-- The product of factorwise metric weights collapses to a size factor times
the exponential of the total cover metric. -/
theorem appendixF_metricProduct_eq_metricCoverWeight
    {ι : Type*} [DecidableEq ι]
    (C : Finset ι) (metric : ι → ℕ) (H0 κ : ℝ) :
    (∏ i ∈ C, (2 * H0) * Real.exp (-κ * (metric i : ℝ))) =
      (2 * H0) ^ C.card *
        Real.exp (-κ * ∑ i ∈ C, (metric i : ℝ)) := by
  classical
  calc
    (∏ i ∈ C, (2 * H0) * Real.exp (-κ * (metric i : ℝ)))
        =
      (∏ _i ∈ C, (2 * H0)) *
        ∏ i ∈ C, Real.exp (-κ * (metric i : ℝ)) := by
          rw [Finset.prod_mul_distrib]
    _ =
      (2 * H0) ^ C.card *
        ∏ i ∈ C, Real.exp (-κ * (metric i : ℝ)) := by
          rw [Finset.prod_const]
    _ =
      (2 * H0) ^ C.card *
        Real.exp (∑ i ∈ C, -κ * (metric i : ℝ)) := by
          rw [Real.exp_sum]
    _ =
      (2 * H0) ^ C.card *
        Real.exp (-κ * ∑ i ∈ C, (metric i : ℝ)) := by
          rw [← Finset.mul_sum]

/-- Finite quantitative first-activity bound in the standard collapsed metric
form.  The right-hand side is still a finite connected-cover sum; no
Appendix-F entropy or metric-stitching estimate is hidden inside the theorem.
-/
theorem norm_appendixFConnectedActivity_le_metricCoverSum
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site)
    (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (metric : ι → ℕ) (h : ι → ℂ)
    (Y : Finset Site) (H0 κ : ℝ)
    (hH0 : 0 ≤ H0) (hH01 : H0 ≤ 1) (hκ : 0 ≤ κ)
    (hraw : ∀ i, i ∈ Λ →
      ‖h i‖ ≤ H0 * Real.exp (-κ * (metric i : ℝ))) :
    ‖appendixFConnectedActivity Ω overlapSupport targetSupport Λ h Y‖ ≤
      ∑ C ∈ appendixFTargetFiber Ω overlapSupport targetSupport Λ Y,
        (2 * H0) ^ C.card *
          Real.exp (-κ * ∑ i ∈ C, (metric i : ℝ)) := by
  classical
  calc
    ‖appendixFConnectedActivity Ω overlapSupport targetSupport Λ h Y‖
        ≤
      ∑ C ∈ appendixFTargetFiber Ω overlapSupport targetSupport Λ Y,
        ∏ i ∈ C, (2 * H0) * Real.exp (-κ * (metric i : ℝ)) :=
          norm_appendixFConnectedActivity_le_metricProductCoverSum
            Ω overlapSupport targetSupport Λ metric h Y H0 κ
            hH0 hH01 hκ hraw
    _ =
      ∑ C ∈ appendixFTargetFiber Ω overlapSupport targetSupport Λ Y,
        (2 * H0) ^ C.card *
          Real.exp (-κ * ∑ i ∈ C, (metric i : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro C _hC
          exact appendixF_metricProduct_eq_metricCoverWeight C metric H0 κ

/-- Source-facing with-holes specialization of the finite first-activity
majorant.  Connectivity uses active skeletons and target fibers use full
hole-polymer unions, exactly as in `AppendixFHoleTargetFamily`. -/
theorem norm_appendixFHoleConnectedMayerActivity_expSubOne_le_metricCoverSum
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (metric : OmegaPolymerType HF z → ℕ)
    (h : OmegaPolymerType HF z → ℂ)
    (Y : Finset (Cube d L)) (H0 κ : ℝ)
    (hH0 : 0 ≤ H0) (hH01 : H0 ≤ 1) (hκ : 0 ≤ κ)
    (hraw : ∀ X, X ∈ Λ →
      ‖h X‖ ≤ H0 * Real.exp (-κ * (metric X : ℝ))) :
    ‖appendixFHoleConnectedMayerActivity HF z Λ
        (fun X => Complex.exp (h X) - 1) Y‖ ≤
      ∑ C ∈ appendixFTargetFiber
          (Finset.univ : Finset (Cube d L))
          (fun X : OmegaPolymerType HF z => skeleton HF X.val)
          (fun X : OmegaPolymerType HF z => X.val)
          Λ Y,
        (2 * H0) ^ C.card *
          Real.exp (-κ * ∑ X ∈ C, (metric X : ℝ)) := by
  classical
  simpa [appendixFHoleConnectedMayerActivity, appendixFConnectedActivity,
    appendixFConnectedMayerActivity] using
    norm_appendixFConnectedActivity_le_metricCoverSum
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ metric h Y H0 κ hH0 hH01 hκ hraw

end YangMills.RG

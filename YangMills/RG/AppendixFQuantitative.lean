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

/-- The positive weight attached to one connected raw cover by the finite
Appendix-F first-activity majorant. -/
noncomputable def appendixFMetricCoverWeight
    {ι : Type*} [DecidableEq ι]
    (metric : ι → ℕ) (H0 κ : ℝ) (C : Finset ι) : ℝ :=
  (2 * H0) ^ C.card * Real.exp (-κ * ∑ i ∈ C, (metric i : ℝ))

theorem appendixFMetricCoverWeight_nonneg
    {ι : Type*} [DecidableEq ι]
    (metric : ι → ℕ) {H0 κ : ℝ} (hH0 : 0 ≤ H0) (C : Finset ι) :
    0 ≤ appendixFMetricCoverWeight metric H0 κ C := by
  unfold appendixFMetricCoverWeight
  exact mul_nonneg
    (pow_nonneg (mul_nonneg zero_le_two hH0) C.card)
    (Real.exp_nonneg _)

/-- If a finite connected set `S` spans the active skeleton of `X`, then the
modified metric of `X` plus one is bounded by `|S|`.  This is the reusable
finite variational inequality behind the Appendix-F metric-stitching step. -/
theorem discreteModifiedMetric_add_one_le_card_of_spanning_set
    {d L : ℕ} (HF : HoleFamily d L)
    (X S : Finset (Cube d L))
    (hskel_ne : (skeleton HF X).Nonempty)
    (hskel : skeleton HF X ⊆ S)
    (hSsub : S ⊆ X) (hSconn : cubeConnected S) :
    discreteModifiedMetric HF X + 1 ≤ S.card := by
  classical
  have h_ex :
      ∃ T : Finset (Cube d L),
        skeleton HF X ⊆ T ∧ T ⊆ X ∧ cubeConnected T :=
    ⟨S, hskel, hSsub, hSconn⟩
  have h_metric :
      discreteModifiedMetric HF X =
        sInf {n | ∃ T : Finset (Cube d L),
          skeleton HF X ⊆ T ∧ T ⊆ X ∧ cubeConnected T ∧
            T.card - 1 = n} := by
    unfold discreteModifiedMetric
    rw [dif_pos h_ex]
  have hS_ne : S.Nonempty := by
    rcases hskel_ne with ⟨r, hr⟩
    exact ⟨r, hskel hr⟩
  have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr hS_ne
  have hle : discreteModifiedMetric HF X ≤ S.card - 1 := by
    rw [h_metric]
    apply Nat.sInf_le
    exact ⟨S, hskel, hSsub, hSconn, rfl⟩
  omega

/-- Metric stitching for a finite `Ω`-connected cover of source-facing
with-holes polymers.  The target metric of the full cover union is bounded by
the sum of the shifted metrics of the raw polymers in the cover:

`d_M(⋃ X, mod holes) + 1 ≤ Σ_X (d_M(X, mod holes) + 1)`.

This is the finite geometric part of Dimock's Appendix-F inequality (641), for
the repository's discrete modified metric and the active-skeleton/full-target
split.  It carries no analytic constants and no entropy estimate. -/
theorem appendixFHoleCoverUnion_discreteModifiedMetric_add_one_le_sum
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {C : Finset (OmegaPolymerType HF z)}
    (hC : C ∈ appendixFConnectedCoverRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ) :
    discreteModifiedMetric HF
        (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C) + 1
      ≤ ∑ X ∈ C, (discreteModifiedMetric HF X.val + 1) := by
  classical
  let root : OmegaPolymerType HF z → Cube d L := fun X =>
    Classical.choose X.property.right.right.right
  have hroot : ∀ X : OmegaPolymerType HF z, root X ∈ skeleton HF X.val := by
    intro X
    exact Classical.choose_spec X.property.right.right.right
  let S : OmegaPolymerType HF z → Finset (Cube d L) := fun X =>
    Classical.choose
      (exists_minimal_spanning_set HF X.val (root X) (hroot X)
        X.property.right.left)
  have hS_skel : ∀ X : OmegaPolymerType HF z, skeleton HF X.val ⊆ S X := by
    intro X
    exact (Classical.choose_spec
      (exists_minimal_spanning_set HF X.val (root X) (hroot X)
        X.property.right.left)).1
  have hS_sub : ∀ X : OmegaPolymerType HF z, S X ⊆ X.val := by
    intro X
    exact (Classical.choose_spec
      (exists_minimal_spanning_set HF X.val (root X) (hroot X)
        X.property.right.left)).2.1
  have hS_conn : ∀ X : OmegaPolymerType HF z, cubeConnected (S X) := by
    intro X
    exact (Classical.choose_spec
      (exists_minimal_spanning_set HF X.val (root X) (hroot X)
        X.property.right.left)).2.2.1
  have hS_card :
      ∀ X : OmegaPolymerType HF z,
        (S X).card = discreteModifiedMetric HF X.val + 1 := by
    intro X
    exact (Classical.choose_spec
      (exists_minimal_spanning_set HF X.val (root X) (hroot X)
        X.property.right.left)).2.2.2.2
  have hSUnion_skel :
      skeleton HF
          (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C)
        ⊆ C.biUnion S := by
    intro r hr
    rw [appendixFHoleCoverUnion_skeleton HF z C] at hr
    rw [appendixFCoverUnion, Finset.mem_biUnion] at hr
    rw [Finset.mem_biUnion]
    rcases hr with ⟨X, hX, hrX⟩
    exact ⟨X, hX, hS_skel X hrX⟩
  have hSUnion_sub :
      C.biUnion S ⊆
        appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C := by
    intro r hr
    rw [Finset.mem_biUnion] at hr
    rw [appendixFCoverUnion, Finset.mem_biUnion]
    rcases hr with ⟨X, hX, hrS⟩
    exact ⟨X, hX, hS_sub X hrS⟩
  have hS_hadj :
      ∀ X Y : OmegaPolymerType HF z,
        (omegaOverlapGraph (Finset.univ : Finset (Cube d L))
          (fun P : OmegaPolymerType HF z => skeleton HF P.val)).Adj X Y →
          ¬ Disjoint (S X) (S Y) := by
    intro X Y hAdj hdisj
    rw [omegaOverlapGraph_adj_iff] at hAdj
    apply hAdj.2
    rw [Finset.disjoint_left]
    intro r hrX hrY
    have hrX' : r ∈ S X := hS_skel X (by simpa using hrX)
    have hrY' : r ∈ S Y := hS_skel Y (by simpa using hrY)
    exact (Finset.disjoint_left.mp hdisj hrX') hrY'
  have hCdata :=
    (mem_appendixFConnectedCoverRegion_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ C).mp hC
  have hSUnion_conn : cubeConnected (C.biUnion S) := by
    rw [cubeConnected]
    intro x hx y hy
    rw [Finset.mem_biUnion] at hx hy
    rcases hx with ⟨X, hX, hxS⟩
    rcases hy with ⟨Y, hY, hyS⟩
    obtain ⟨w, hwC⟩ := hCdata.2.2 X hX Y hY
    obtain ⟨wCube, hwCube⟩ :=
      walk_union_connected
        (omegaOverlapGraph (Finset.univ : Finset (Cube d L))
          (fun P : OmegaPolymerType HF z => skeleton HF P.val))
        (cubeAdj d L) S hS_conn hS_hadj w x hxS y hyS
    refine ⟨wCube, ?_⟩
    intro v hv
    rcases hwCube v hv with ⟨P, hPw, hvP⟩
    exact Finset.mem_biUnion.mpr ⟨P, hwC P hPw, hvP⟩
  have hskel_ne :
      (skeleton HF
        (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C)).Nonempty := by
    rw [appendixFHoleCoverUnion_skeleton]
    exact appendixFHoleActiveCoverUnion_nonempty HF z Λ hC
  have hmetric :
      discreteModifiedMetric HF
          (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C) + 1
        ≤ (C.biUnion S).card :=
    discreteModifiedMetric_add_one_le_card_of_spanning_set HF
      (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C)
      (C.biUnion S) hskel_ne hSUnion_skel hSUnion_sub hSUnion_conn
  have hcard :
      (C.biUnion S).card ≤ ∑ X ∈ C, (S X).card :=
    Finset.card_biUnion_le
  have hsum :
      ∑ X ∈ C, (S X).card =
        ∑ X ∈ C, (discreteModifiedMetric HF X.val + 1) := by
    simp [hS_card]
  exact hmetric.trans (hcard.trans_eq hsum)

/-- Fiber form of the with-holes metric-stitching inequality. -/
theorem appendixFHoleTargetFiber_discreteModifiedMetric_add_one_le_sum
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)} {C : Finset (OmegaPolymerType HF z)}
    (hC : C ∈ appendixFTargetFiber
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y) :
    discreteModifiedMetric HF Y + 1
      ≤ ∑ X ∈ C, (discreteModifiedMetric HF X.val + 1) := by
  classical
  have hCdata :=
    (mem_appendixFTargetFiber_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y C).mp hC
  rw [← hCdata.2]
  exact appendixFHoleCoverUnion_discreteModifiedMetric_add_one_le_sum
    HF z Λ hCdata.1

/-- If every source hole-polymer in a finite cover has full cardinality
bounded by a multiple of its shifted modified metric, then the full target
cover union has cardinality bounded by the corresponding cover-metric sum.

This is deliberately a cover-sum statement, not a claim that the full target
cardinality is controlled by `d_M` of the target itself.  The latter needs an
extra source geometric compression estimate. -/
theorem appendixFHoleCoverUnion_card_le_metricSum_of_source_card_le_metric
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (C : Finset (OmegaPolymerType HF z)) {θ : ℝ}
    (hsource : ∀ X, X ∈ C →
      (X.val.card : ℝ) ≤
        θ * ((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) :
    ((appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C).card : ℝ) ≤
      θ * ∑ X ∈ C,
        ((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ) := by
  classical
  have hcard :
      ((appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C).card : ℝ) ≤
        ∑ X ∈ C, (X.val.card : ℝ) :=
    appendixFCoverUnion_card_real_le_sum
      (fun X : OmegaPolymerType HF z => X.val) C
  have hsum :
      (∑ X ∈ C, (X.val.card : ℝ)) ≤
        ∑ X ∈ C,
          θ * ((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ) :=
    Finset.sum_le_sum hsource
  have hfactor :
      (∑ X ∈ C,
          θ * ((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) =
        θ * ∑ X ∈ C,
          ((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
  exact hcard.trans (hsum.trans_eq hfactor)

/-- Fiber form of
`appendixFHoleCoverUnion_card_le_metricSum_of_source_card_le_metric`: a target
fiber equation rewrites the cover-union cardinality to the represented full
target `Y`. -/
theorem appendixFHoleTargetFiber_card_le_metricSum_of_source_card_le_metric
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)} {C : Finset (OmegaPolymerType HF z)}
    {θ : ℝ}
    (hC : C ∈ appendixFTargetFiber
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y)
    (hsource : ∀ X, X ∈ C →
      (X.val.card : ℝ) ≤
        θ * ((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) :
    (Y.card : ℝ) ≤
      θ * ∑ X ∈ C,
        ((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ) := by
  classical
  have hCdata :=
    (mem_appendixFTargetFiber_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y C).mp hC
  rw [← hCdata.2]
  exact appendixFHoleCoverUnion_card_le_metricSum_of_source_card_le_metric
    HF z C hsource

/-- The finite target-fiber metric majorant for the first connected activity.
This is the right-hand side of
`norm_appendixFConnectedActivity_le_metricCoverSum`, packaged for reuse. -/
noncomputable def appendixFTargetMetricCoverSum
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site)
    (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (metric : ι → ℕ)
    (Y : Finset Site) (H0 κ : ℝ) : ℝ :=
  ∑ C ∈ appendixFTargetFiber Ω overlapSupport targetSupport Λ Y,
    appendixFMetricCoverWeight metric H0 κ C

/-- The local/pinned metric majorant: all connected covers having at least one
raw target support through the pin `r`.  This is the finite localization step
toward the source's local-influence estimates; it still does not bound this
sum by a closed Dimock constant. -/
noncomputable def appendixFPinnedMetricCoverSum
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site)
    (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (metric : ι → ℕ)
    (r : Site) (H0 κ : ℝ) : ℝ :=
  ∑ C ∈ (appendixFConnectedCoverRegion Ω overlapSupport Λ).filter
      (fun C => ∃ i ∈ C, r ∈ targetSupport i),
    appendixFMetricCoverWeight metric H0 κ C

/-- A target-fiber metric sum is bounded by any pinned connected-cover sum
through a site of the target.  This is a pure finite localization/lumping
lemma: if `r ∈ Y`, every cover whose target union is `Y` contains at least one
raw support through `r`. -/
theorem appendixFTargetMetricCoverSum_le_pinnedMetricCoverSum
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site)
    (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (metric : ι → ℕ)
    (Y : Finset Site) (r : Site) (H0 κ : ℝ)
    (hH0 : 0 ≤ H0) (hr : r ∈ Y) :
    appendixFTargetMetricCoverSum Ω overlapSupport targetSupport Λ metric
        Y H0 κ ≤
      appendixFPinnedMetricCoverSum Ω overlapSupport targetSupport Λ metric
        r H0 κ := by
  classical
  unfold appendixFTargetMetricCoverSum appendixFPinnedMetricCoverSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
  · intro C hC
    rw [Finset.mem_filter]
    have hfiber := (mem_appendixFTargetFiber_iff Ω overlapSupport
      targetSupport Λ Y C).mp hC
    refine ⟨hfiber.1, ?_⟩
    have hrUnion : r ∈ appendixFCoverUnion targetSupport C := by
      rw [hfiber.2]
      exact hr
    rcases Finset.mem_biUnion.mp hrUnion with ⟨i, hiC, hri⟩
    exact ⟨i, hiC, hri⟩
  · intro C _hpinned _hCnotFiber
    exact appendixFMetricCoverWeight_nonneg metric hH0 C

/-- Finite localized first-activity bound: after the raw pointwise exponential
estimate, a target activity `K(Y)` is controlled by the pinned connected-cover
metric sum through any `r ∈ Y`. -/
theorem norm_appendixFConnectedActivity_le_pinnedMetricCoverSum
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site)
    (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (metric : ι → ℕ) (h : ι → ℂ)
    (Y : Finset Site) (r : Site) (H0 κ : ℝ)
    (hH0 : 0 ≤ H0) (hH01 : H0 ≤ 1) (hκ : 0 ≤ κ)
    (hraw : ∀ i, i ∈ Λ →
      ‖h i‖ ≤ H0 * Real.exp (-κ * (metric i : ℝ)))
    (hr : r ∈ Y) :
    ‖appendixFConnectedActivity Ω overlapSupport targetSupport Λ h Y‖ ≤
      appendixFPinnedMetricCoverSum Ω overlapSupport targetSupport Λ metric
        r H0 κ := by
  classical
  have hmetric :=
    norm_appendixFConnectedActivity_le_metricCoverSum
      Ω overlapSupport targetSupport Λ metric h Y H0 κ
      hH0 hH01 hκ hraw
  have hpinned :=
    appendixFTargetMetricCoverSum_le_pinnedMetricCoverSum
      Ω overlapSupport targetSupport Λ metric Y r H0 κ hH0 hr
  exact hmetric.trans (by
    simpa [appendixFTargetMetricCoverSum, appendixFMetricCoverWeight] using
      hpinned)

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

/-- Source-facing target-fiber metric majorant for `omegaHolePolymerSystem`. -/
noncomputable def appendixFHoleTargetMetricCoverSum
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (metric : OmegaPolymerType HF z → ℕ)
    (Y : Finset (Cube d L)) (H0 κ : ℝ) : ℝ :=
  appendixFTargetMetricCoverSum
    (Finset.univ : Finset (Cube d L))
    (fun X : OmegaPolymerType HF z => skeleton HF X.val)
    (fun X : OmegaPolymerType HF z => X.val)
    Λ metric Y H0 κ

/-- Source-facing pinned connected-cover metric majorant for
`omegaHolePolymerSystem`.  It sums all skeleton-connected covers containing a
raw full polymer through the pinned cube `r`. -/
noncomputable def appendixFHolePinnedMetricCoverSum
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (metric : OmegaPolymerType HF z → ℕ)
    (r : Cube d L) (H0 κ : ℝ) : ℝ :=
  appendixFPinnedMetricCoverSum
    (Finset.univ : Finset (Cube d L))
    (fun X : OmegaPolymerType HF z => skeleton HF X.val)
    (fun X : OmegaPolymerType HF z => X.val)
    Λ metric r H0 κ

theorem appendixFHoleTargetMetricCoverSum_le_pinnedMetricCoverSum
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (metric : OmegaPolymerType HF z → ℕ)
    (Y : Finset (Cube d L)) (r : Cube d L) (H0 κ : ℝ)
    (hH0 : 0 ≤ H0) (hr : r ∈ Y) :
    appendixFHoleTargetMetricCoverSum HF z Λ metric Y H0 κ ≤
      appendixFHolePinnedMetricCoverSum HF z Λ metric r H0 κ := by
  classical
  simpa [appendixFHoleTargetMetricCoverSum, appendixFHolePinnedMetricCoverSum]
    using appendixFTargetMetricCoverSum_le_pinnedMetricCoverSum
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ metric Y r H0 κ hH0 hr

/-- Source-facing localized first-activity bound for the with-holes carrier.
This is the finite bridge from a raw pointwise estimate to a pinned local
connected-cover sum.  The pinned sum still needs the later Appendix-F
metric/entropy estimate. -/
theorem norm_appendixFHoleConnectedMayerActivity_expSubOne_le_pinnedMetricCoverSum
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (metric : OmegaPolymerType HF z → ℕ)
    (h : OmegaPolymerType HF z → ℂ)
    (Y : Finset (Cube d L)) (r : Cube d L) (H0 κ : ℝ)
    (hH0 : 0 ≤ H0) (hH01 : H0 ≤ 1) (hκ : 0 ≤ κ)
    (hraw : ∀ X, X ∈ Λ →
      ‖h X‖ ≤ H0 * Real.exp (-κ * (metric X : ℝ)))
    (hr : r ∈ Y) :
    ‖appendixFHoleConnectedMayerActivity HF z Λ
        (fun X => Complex.exp (h X) - 1) Y‖ ≤
      appendixFHolePinnedMetricCoverSum HF z Λ metric r H0 κ := by
  classical
  simpa [appendixFHoleConnectedMayerActivity, appendixFConnectedActivity,
    appendixFConnectedMayerActivity, appendixFHolePinnedMetricCoverSum] using
    norm_appendixFConnectedActivity_le_pinnedMetricCoverSum
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ metric h Y r H0 κ hH0 hH01 hκ hraw hr

end YangMills.RG

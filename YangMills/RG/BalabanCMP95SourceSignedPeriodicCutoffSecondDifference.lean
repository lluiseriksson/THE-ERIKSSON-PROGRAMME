/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95SourceSignedPeriodicCutoffSlope

/-!
# PRE-VALIDATION: second differences of the signed periodic CMP95 cutoff

The source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the Lean compiler.

The three evaluation points of a centred second difference are reduced to the
union of their literal two-point active windows.  The resulting six-term sum
transports the canonical quadratic profile estimate without differentiating a
square root and without accepting positivity of the source profile.

This is the one-dimensional analytic core.  Tensoring it through a coordinate
shift and identifying the literal cutoff-Laplacian species remain separate
physical obligations.
-/

namespace YangMills.RG

noncomputable section

/-- Linear periodization preserves the quadratic centred-difference scale.
The factor `12 = 6 * 2` is the union-cardinality bound for the three active
windows times the canonical source-profile estimate. -/
theorem norm_cmp95PeriodicSignedCutoff_centeredSecondDifference_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (x h : ℝ) :
    ‖cmp95PeriodicSignedCutoff P Q cell (x + h) -
        2 * cmp95PeriodicSignedCutoff P Q cell x +
        cmp95PeriodicSignedCutoff P Q cell (x - h)‖ ≤
      (12 * P.secondDerivBound) * ‖h‖ ^ 2 := by
  classical
  let W :=
    (cmp95PeriodicActiveWindow Q cell (x + h) ∪
      cmp95PeriodicActiveWindow Q cell x) ∪
        cmp95PeriodicActiveWindow Q cell (x - h)
  have hplus : cmp95PeriodicSignedCutoff P Q cell (x + h) =
      ∑ k ∈ W, P.value
        ((x + h) - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) := by
    unfold cmp95PeriodicSignedCutoff
    exact tsum_eq_sum fun k hk => by
      by_contra hne
      have hmem := mem_cmp95PeriodicActiveWindow_of_ne_zero
        P Q cell (x + h) k (pow_ne_zero 2 hne)
      exact hk (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
  have hzero : cmp95PeriodicSignedCutoff P Q cell x =
      ∑ k ∈ W, P.value
        (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) := by
    unfold cmp95PeriodicSignedCutoff
    exact tsum_eq_sum fun k hk => by
      by_contra hne
      have hmem := mem_cmp95PeriodicActiveWindow_of_ne_zero
        P Q cell x k (pow_ne_zero 2 hne)
      exact hk (Finset.mem_union_left _ (Finset.mem_union_right _ hmem))
  have hminus : cmp95PeriodicSignedCutoff P Q cell (x - h) =
      ∑ k ∈ W, P.value
        ((x - h) - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) := by
    unfold cmp95PeriodicSignedCutoff
    exact tsum_eq_sum fun k hk => by
      by_contra hne
      have hmem := mem_cmp95PeriodicActiveWindow_of_ne_zero
        P Q cell (x - h) k (pow_ne_zero 2 hne)
      exact hk (Finset.mem_union_right _ hmem)
  rw [hplus, hzero, hminus]
  calc
    ‖(∑ k ∈ W, P.value
          ((x + h) - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))) -
        2 * (∑ k ∈ W, P.value
          (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))) +
        (∑ k ∈ W, P.value
          ((x - h) - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)))‖ =
      ‖∑ k ∈ W,
        (P.value
            ((x + h) - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) -
          2 * P.value
            (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) +
          P.value
            ((x - h) - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)))‖ := by
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
    _ ≤ ∑ k ∈ W, ‖P.value
          ((x + h) - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) -
        2 * P.value
          (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) +
        P.value
          ((x - h) - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ W, (2 * P.secondDerivBound) * ‖h‖ ^ 2 := by
      gcongr with k hk
      have hprofile := P.norm_centeredSecondDifference_le_secondDerivBound
        (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) h
      convert hprofile using 1 <;> ring
    _ = (W.card : ℝ) * ((2 * P.secondDerivBound) * ‖h‖ ^ 2) := by
      simp
    _ ≤ 6 * ((2 * P.secondDerivBound) * ‖h‖ ^ 2) := by
      have hcard : W.card ≤ 6 := by
        calc
          W.card ≤
              (cmp95PeriodicActiveWindow Q cell (x + h) ∪
                cmp95PeriodicActiveWindow Q cell x).card +
                (cmp95PeriodicActiveWindow Q cell (x - h)).card :=
            Finset.card_union_le _ _
          _ ≤ ((cmp95PeriodicActiveWindow Q cell (x + h)).card +
                (cmp95PeriodicActiveWindow Q cell x).card) +
                (cmp95PeriodicActiveWindow Q cell (x - h)).card := by
            gcongr
            exact Finset.card_union_le _ _
          _ = 6 := by
            rw [card_cmp95PeriodicActiveWindow,
              card_cmp95PeriodicActiveWindow,
              card_cmp95PeriodicActiveWindow]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · exact mul_nonneg
          (mul_nonneg (by norm_num) P.secondDerivBound_nonneg)
          (sq_nonneg ‖h‖)
    _ = (12 * P.secondDerivBound) * ‖h‖ ^ 2 := by ring

/-- The explicit one-cell branch is constant; otherwise the signed bound
applies unchanged. -/
theorem norm_cmp95SourcePeriodicSignedCutoff_centeredSecondDifference_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (x h : ℝ) :
    ‖cmp95SourcePeriodicSignedCutoff P Q cell (x + h) -
        2 * cmp95SourcePeriodicSignedCutoff P Q cell x +
        cmp95SourcePeriodicSignedCutoff P Q cell (x - h)‖ ≤
      (12 * P.secondDerivBound) * ‖h‖ ^ 2 := by
  by_cases hQ1 : Q = 1
  · simp [cmp95SourcePeriodicSignedCutoff, hQ1]
    exact mul_nonneg
      (mul_nonneg (show (0 : ℝ) ≤ 12 by norm_num)
        P.secondDerivBound_nonneg) (sq_nonneg |h|)
  · simpa [cmp95SourcePeriodicSignedCutoff, hQ1] using
      norm_cmp95PeriodicSignedCutoff_centeredSecondDifference_le
        P Q cell x h

/-- Physical rescaling exposes the inverse-square cutoff scale before any
tensor, cell, or Green sum. -/
theorem
    norm_cmp95RescaledSourcePeriodicSignedCutoff_centeredSecondDifference_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    {M0 : ℝ} (hM0 : 0 < M0) (cell : Fin Q) (x h : ℝ) :
    ‖cmp95RescaledSourcePeriodicSignedCutoff P Q M0 cell (x + h) -
        2 * cmp95RescaledSourcePeriodicSignedCutoff P Q M0 cell x +
        cmp95RescaledSourcePeriodicSignedCutoff P Q M0 cell (x - h)‖ ≤
      ((12 * P.secondDerivBound) / M0 ^ 2) * ‖h‖ ^ 2 := by
  have hraw :=
    norm_cmp95SourcePeriodicSignedCutoff_centeredSecondDifference_le
      P Q cell (x / M0) (h / M0)
  unfold cmp95RescaledSourcePeriodicSignedCutoff
  calc
    ‖cmp95SourcePeriodicSignedCutoff P Q cell ((x + h) / M0) -
        2 * cmp95SourcePeriodicSignedCutoff P Q cell (x / M0) +
        cmp95SourcePeriodicSignedCutoff P Q cell ((x - h) / M0)‖ =
      ‖cmp95SourcePeriodicSignedCutoff P Q cell (x / M0 + h / M0) -
        2 * cmp95SourcePeriodicSignedCutoff P Q cell (x / M0) +
        cmp95SourcePeriodicSignedCutoff P Q cell (x / M0 - h / M0)‖ := by
      congr 3 <;> field_simp <;> ring
    _ ≤ (12 * P.secondDerivBound) * ‖h / M0‖ ^ 2 := hraw
    _ = ((12 * P.secondDerivBound) / M0 ^ 2) * ‖h‖ ^ 2 := by
      rw [norm_div, show ‖M0‖ = M0 by
        simpa [Real.norm_eq_abs] using abs_of_pos hM0]
      field_simp [ne_of_gt hM0]

end

end YangMills.RG

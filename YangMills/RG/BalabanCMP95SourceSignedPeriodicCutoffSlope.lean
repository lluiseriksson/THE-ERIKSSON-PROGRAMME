/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95SourceSignedPeriodicCutoff
import YangMills.RG.BalabanCMP95PeriodicSquareTorusSlope

/-!
# PRE-VALIDATION: slope of the signed periodic CMP95 cutoff

The source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the Lean compiler.

This module supplies the first analytic replacement required after switching
from the square-root cutoff to the source-faithful signed periodization.  The
linear periodization is reduced to the union of the two active windows at the
endpoints.  Hence its one-dimensional slope is bounded by four copies of the
literal source-profile derivative budget, independently of the period.  The
explicit one-cell branch is constant and satisfies the same bound.

Physical rescaling exposes the inverse cutoff scale before tensoring.  The
four-dimensional tensor estimate pays the four coordinate directions and no
cell-count, overlap, Green, or Poincare factor.  This is a slope theorem only;
the quadratic second difference and the regional physical partition remain
separate obligations.
-/

namespace YangMills.RG

noncomputable section

/-- Linear periodization has a volume-independent global slope.  The factor
four is the cardinality of the union of the two two-point active windows. -/
theorem norm_cmp95PeriodicSignedCutoff_sub_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (x y : ℝ) :
    ‖cmp95PeriodicSignedCutoff P Q cell y -
        cmp95PeriodicSignedCutoff P Q cell x‖ ≤
      (4 * P.derivBound) * ‖y - x‖ := by
  classical
  let W := cmp95PeriodicActiveWindow Q cell x ∪
    cmp95PeriodicActiveWindow Q cell y
  have hy : cmp95PeriodicSignedCutoff P Q cell y =
      ∑ k ∈ W, P.value
        (y - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) := by
    unfold cmp95PeriodicSignedCutoff
    exact tsum_eq_sum fun k hk => by
      by_contra hne
      have hmem := mem_cmp95PeriodicActiveWindow_of_ne_zero
        P Q cell y k (pow_ne_zero 2 hne)
      exact hk (Finset.mem_union_right _ hmem)
  have hx : cmp95PeriodicSignedCutoff P Q cell x =
      ∑ k ∈ W, P.value
        (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) := by
    unfold cmp95PeriodicSignedCutoff
    exact tsum_eq_sum fun k hk => by
      by_contra hne
      have hmem := mem_cmp95PeriodicActiveWindow_of_ne_zero
        P Q cell x k (pow_ne_zero 2 hne)
      exact hk (Finset.mem_union_left _ hmem)
  rw [hy, hx, ← Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ W,
        (P.value
          (y - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) -
        P.value
          (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)))‖ ≤
      ∑ k ∈ W, ‖P.value
          (y - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) -
        P.value
          (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ W, P.derivBound * ‖y - x‖ := by
      gcongr with k hk
      simpa only [sub_sub_sub_cancel_right] using
        P.norm_value_sub_value_le
          (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))
          (y - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))
    _ = (W.card : ℝ) * (P.derivBound * ‖y - x‖) := by simp
    _ ≤ 4 * (P.derivBound * ‖y - x‖) := by
      have hcard : W.card ≤ 4 := by
        calc
          W.card ≤
              (cmp95PeriodicActiveWindow Q cell x).card +
                (cmp95PeriodicActiveWindow Q cell y).card :=
            Finset.card_union_le _ _
          _ = 4 := by
            rw [card_cmp95PeriodicActiveWindow,
              card_cmp95PeriodicActiveWindow]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · exact mul_nonneg P.derivBound_nonneg (norm_nonneg _)
    _ = (4 * P.derivBound) * ‖y - x‖ := by ring

/-- The source-faithful cutoff, including its one-cell branch, has the same
uniform slope bound. -/
theorem norm_cmp95SourcePeriodicSignedCutoff_sub_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (x y : ℝ) :
    ‖cmp95SourcePeriodicSignedCutoff P Q cell y -
        cmp95SourcePeriodicSignedCutoff P Q cell x‖ ≤
      (4 * P.derivBound) * ‖y - x‖ := by
  by_cases hQ1 : Q = 1
  · simp [cmp95SourcePeriodicSignedCutoff, hQ1]
    exact mul_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
      (abs_nonneg _)
  · simpa [cmp95SourcePeriodicSignedCutoff, hQ1] using
      norm_cmp95PeriodicSignedCutoff_sub_le P Q cell x y

/-- The source-faithful cutoff is contractive because its square is one term
of the exact finite square partition. -/
theorem norm_cmp95SourcePeriodicSignedCutoff_le_one
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    ‖cmp95SourcePeriodicSignedCutoff P Q cell t‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
  rw [sq_abs, one_pow, cmp95SourcePeriodicSignedCutoff_sq]
  exact cmp95PeriodicSquareWeight_le_one P Q cell t

/-- The explicit one-cell branch and the signed branch are both periodic. -/
theorem cmp95SourcePeriodicSignedCutoff_add_period
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    cmp95SourcePeriodicSignedCutoff P Q cell (t + Q) =
      cmp95SourcePeriodicSignedCutoff P Q cell t := by
  by_cases hQ1 : Q = 1
  · simp [cmp95SourcePeriodicSignedCutoff, hQ1]
  · simpa [cmp95SourcePeriodicSignedCutoff, hQ1] using
      cmp95PeriodicSignedCutoff_add_period P Q cell t

/-- Physical rescaling of the source-faithful signed periodic cutoff. -/
def cmp95RescaledSourcePeriodicSignedCutoff
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : Fin Q) (t : ℝ) : ℝ :=
  cmp95SourcePeriodicSignedCutoff P Q cell (t / M0)

theorem cmp95RescaledSourcePeriodicSignedCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : Fin Q) (t : ℝ) :
    cmp95RescaledSourcePeriodicSignedCutoff P Q M0 cell t ^ 2 =
      cmp95RescaledPeriodicSquareWeight P Q M0 cell t := by
  exact cmp95SourcePeriodicSignedCutoff_sq P Q cell (t / M0)

theorem norm_cmp95RescaledSourcePeriodicSignedCutoff_le_one
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : Fin Q) (t : ℝ) :
    ‖cmp95RescaledSourcePeriodicSignedCutoff P Q M0 cell t‖ ≤ 1 :=
  norm_cmp95SourcePeriodicSignedCutoff_le_one P Q cell (t / M0)

/-- Rescaling exposes the exact inverse physical scale. -/
theorem norm_cmp95RescaledSourcePeriodicSignedCutoff_sub_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    {M0 : ℝ} (hM0 : 0 < M0) (cell : Fin Q) (x y : ℝ) :
    ‖cmp95RescaledSourcePeriodicSignedCutoff P Q M0 cell y -
        cmp95RescaledSourcePeriodicSignedCutoff P Q M0 cell x‖ ≤
      ((4 * P.derivBound) / M0) * ‖y - x‖ := by
  have h := norm_cmp95SourcePeriodicSignedCutoff_sub_le
    P Q cell (x / M0) (y / M0)
  unfold cmp95RescaledSourcePeriodicSignedCutoff
  calc
    _ ≤ (4 * P.derivBound) * ‖y / M0 - x / M0‖ := h
    _ = (4 * P.derivBound) * ‖(y - x) / M0‖ := by ring_nf
    _ = ((4 * P.derivBound) / M0) * ‖y - x‖ := by
      rw [norm_div, show ‖M0‖ = M0 by
        simpa [Real.norm_eq_abs] using abs_of_pos hM0]
      ring

theorem cmp95RescaledSourcePeriodicSignedCutoff_add_period
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (hM0 : M0 ≠ 0) (cell : Fin Q) (t : ℝ) :
    cmp95RescaledSourcePeriodicSignedCutoff P Q M0 cell (t + M0 * Q) =
      cmp95RescaledSourcePeriodicSignedCutoff P Q M0 cell t := by
  unfold cmp95RescaledSourcePeriodicSignedCutoff
  rw [show (t + M0 * Q) / M0 = t / M0 + Q by field_simp]
  exact cmp95SourcePeriodicSignedCutoff_add_period P Q cell (t / M0)

/-- Tensor product of the physically rescaled signed cutoffs. -/
def cmp95RescaledSourcePeriodicSignedTensorCutoff
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : FinBox 4 Q) (x : Fin 4 → ℝ) : ℝ :=
  ∏ i, cmp95RescaledSourcePeriodicSignedCutoff P Q M0 (cell i) (x i)

theorem cmp95RescaledSourcePeriodicSignedTensorCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : FinBox 4 Q) (x : Fin 4 → ℝ) :
    cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell x ^ 2 =
      cmp95RescaledPeriodicTensorSquareWeight P Q M0 cell x := by
  unfold cmp95RescaledSourcePeriodicSignedTensorCutoff
    cmp95RescaledPeriodicTensorSquareWeight
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ =>
    cmp95RescaledSourcePeriodicSignedCutoff_sq P Q M0 (cell i) (x i)

theorem sum_cmp95RescaledSourcePeriodicSignedTensorCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (x : Fin 4 → ℝ) :
    ∑ cell : FinBox 4 Q,
      cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell x ^ 2 = 1 := by
  simp_rw [cmp95RescaledSourcePeriodicSignedTensorCutoff_sq]
  exact sum_cmp95RescaledPeriodicTensorSquareWeight P Q M0 x

theorem norm_cmp95RescaledSourcePeriodicSignedTensorCutoff_le_one
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : FinBox 4 Q) (x : Fin 4 → ℝ) :
    ‖cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell x‖ ≤ 1 := by
  classical
  rw [cmp95RescaledSourcePeriodicSignedTensorCutoff, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ =>
    norm_cmp95RescaledSourcePeriodicSignedCutoff_le_one
      P Q M0 (cell i) (x i)

/-- Boundary-safe tensor slope on the physical four-torus.  The constant
`16` is four coordinate directions times the one-dimensional active-window
constant `4`; it is independent of `Q` and of any later cell overlap sum. -/
theorem norm_cmp95RescaledSourcePeriodicSignedTensorCutoff_finBox_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (M0 Q : ℕ) [NeZero M0] [NeZero Q]
    (cell : FinBox 4 Q) (offset : Fin 4 → ℝ)
    (x y : FinBox 4 (M0 * Q)) :
    ‖cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun i => (y i).val + offset i) -
        cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun i => (x i).val + offset i)‖ ≤
      ((16 * P.derivBound) / M0) * (finBoxDist x y : ℝ) := by
  classical
  unfold cmp95RescaledSourcePeriodicSignedTensorCutoff
  calc
    ‖∏ i, cmp95RescaledSourcePeriodicSignedCutoff P Q M0 (cell i)
          ((y i).val + offset i) -
        ∏ i, cmp95RescaledSourcePeriodicSignedCutoff P Q M0 (cell i)
          ((x i).val + offset i)‖ ≤
      ∑ i, ‖cmp95RescaledSourcePeriodicSignedCutoff P Q M0 (cell i)
          ((y i).val + offset i) -
        cmp95RescaledSourcePeriodicSignedCutoff P Q M0 (cell i)
          ((x i).val + offset i)‖ := by
      apply CMP95SourceSmoothPartitionProfile.norm_prod_sub_prod_le_sum_norm_sub
        Finset.univ
      · intro i _
        exact norm_cmp95RescaledSourcePeriodicSignedCutoff_le_one
          P Q M0 (cell i) ((y i).val + offset i)
      · intro i _
        exact norm_cmp95RescaledSourcePeriodicSignedCutoff_le_one
          P Q M0 (cell i) ((x i).val + offset i)
    _ ≤ ∑ _i : Fin 4,
        ((4 * P.derivBound) / M0) * (finBoxDist x y : ℝ) := by
      gcongr with i
      let f : ℝ → ℝ := fun t =>
        cmp95RescaledSourcePeriodicSignedCutoff P Q M0
          (cell i) (t + offset i)
      have hi : ‖f (y i).val - f (x i).val‖ ≤
          ((4 * P.derivBound) / M0) *
            (finTorusDist (x i) (y i) : ℝ) := by
        apply norm_periodic_fin_value_sub_le_finTorusDist
        · exact div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
            (Nat.cast_nonneg M0)
        · intro t
          dsimp [f]
          rw [show t + (M0 * Q : ℕ) + offset i =
              (t + offset i) + (M0 : ℝ) * Q by push_cast; ring]
          exact cmp95RescaledSourcePeriodicSignedCutoff_add_period
            P Q M0 (by exact_mod_cast NeZero.ne M0) (cell i) (t + offset i)
        · intro u v
          dsimp [f]
          simpa only [add_sub_add_right_eq_sub] using
            norm_cmp95RescaledSourcePeriodicSignedCutoff_sub_le P Q
              (by exact_mod_cast NeZero.pos M0) (cell i)
              (u + offset i) (v + offset i)
      exact hi.trans
        (mul_le_mul_of_nonneg_left
          (Nat.cast_le.2 (finTorusDist_le_finBoxDist x y i))
          (div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
            (Nat.cast_nonneg M0)))
    _ = ((16 * P.derivBound) / M0) * (finBoxDist x y : ℝ) := by
      simp
      ring

end

end YangMills.RG

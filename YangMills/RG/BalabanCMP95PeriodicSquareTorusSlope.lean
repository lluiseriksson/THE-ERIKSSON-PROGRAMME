/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicSquareSlope
import YangMills.RG.PhysicalBondDistance

/-!
# Boundary-safe CMP95 cutoff slope on the generated fine torus

The raw-coordinate slope of the periodized CMP95 square cutoff is not yet a
torus estimate: canonical `Fin` representatives jump at the periodic seam.
This file uses the exact physical period proved for the generated cutoff to
choose the shorter periodic representative and obtains a bound in the
existing `finTorusDist`/`finBoxDist` geometry.

No new metric and no coordinate-chart hypothesis is introduced.
-/

namespace YangMills.RG

noncomputable section

/-- Away from the diagonal, the circular distance is the smaller of the
direct representative gap and the gap through the periodic seam. -/
theorem finTorusDist_eq_min_sub_of_lt
    {N : ℕ} [NeZero N] {a b : Fin N} (hab : a.val < b.val) :
    finTorusDist a b =
      min (b.val - a.val) (N - (b.val - a.val)) := by
  have hle : ((a.val : ZMod N)).val ≤ ((b.val : ZMod N)).val := by
    rw [ZMod.val_cast_of_lt a.isLt, ZMod.val_cast_of_lt b.isLt]
    exact Nat.le_of_lt hab
  have hdiff : (b.val : ZMod N) - (a.val : ZMod N) ≠ 0 := by
    intro hzero
    have heq : (b.val : ZMod N) = (a.val : ZMod N) := sub_eq_zero.mp hzero
    have hfin : b = a := finToZMod_injective heq
    exact (Nat.ne_of_gt hab) (by simpa [hfin])
  letI : NeZero ((b.val : ZMod N) - (a.val : ZMod N)) := ⟨hdiff⟩
  unfold finTorusDist zmodCircDist
  rw [zmodCircVal_sub_comm]
  unfold zmodCircVal
  rw [ZMod.val_sub hle, ZMod.val_neg_of_ne_zero]
  rw [ZMod.val_sub hle]
  rw [ZMod.val_cast_of_lt b.isLt, ZMod.val_cast_of_lt a.isLt]

/-- A real function with period `N` and raw Lipschitz constant `L` is
Lipschitz with the same constant for the circular distance on `Fin N`.
The proof compares both the direct lift and the lift through the seam. -/
theorem norm_periodic_fin_value_sub_le_finTorusDist
    {N : ℕ} [NeZero N] (f : ℝ → ℝ) {L : ℝ}
    (hL : 0 ≤ L)
    (hperiod : ∀ t, f (t + N) = f t)
    (hlip : ∀ x y, ‖f y - f x‖ ≤ L * ‖y - x‖)
    (a b : Fin N) :
    ‖f b.val - f a.val‖ ≤ L * (finTorusDist a b : ℝ) := by
  rcases lt_trichotomy a.val b.val with hab | hab | hab
  · have hdirect : ‖f b.val - f a.val‖ ≤
        L * (b.val - a.val : ℕ) := by
      have hgap : ‖(b.val : ℝ) - (a.val : ℝ)‖ =
          (b.val - a.val : ℕ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact (Nat.cast_sub (R := ℝ) (Nat.le_of_lt hab)).symm
        · apply sub_nonneg.mpr
          exact_mod_cast Nat.le_of_lt hab
      simpa only [hgap] using hlip (a.val : ℝ) (b.val : ℝ)
    have hperiodSub : f ((b.val : ℝ) - N) = f b.val := by
      have hp := hperiod ((b.val : ℝ) - N)
      convert hp.symm using 1 <;> ring
    have hwrap : ‖f b.val - f a.val‖ ≤
        L * (N - (b.val - a.val) : ℕ) := by
      rw [← hperiodSub]
      have hgap : ‖((b.val : ℝ) - N) - (a.val : ℝ)‖ =
          (N - (b.val - a.val) : ℕ) := by
        rw [Real.norm_eq_abs, abs_of_nonpos]
        · rw [Nat.cast_sub (show b.val - a.val ≤ N by omega),
            Nat.cast_sub (Nat.le_of_lt hab)]
          ring
        · apply sub_nonpos.mpr
          have hbN : (b.val : ℝ) ≤ N := by
            exact_mod_cast Nat.le_of_lt b.isLt
          linarith
      simpa only [hgap] using
        hlip (a.val : ℝ) ((b.val : ℝ) - N)
    rw [finTorusDist_eq_min_sub_of_lt hab, Nat.cast_min]
    rcases le_total (b.val - a.val) (N - (b.val - a.val)) with hmin | hmin
    · rw [min_eq_left (by exact_mod_cast hmin)]
      exact hdirect
    · rw [min_eq_right (by exact_mod_cast hmin)]
      exact hwrap
  · have heq : a = b := Fin.ext hab
    subst b
    simp
  · rw [finTorusDist_comm]
    have h := norm_periodic_fin_value_sub_le_finTorusDist
      f hL hperiod hlip b a
    simpa [norm_sub_rev] using h

/-- One generated one-dimensional square weight has the uniform physical
slope `8L/M0` in circular distance, including across the periodic seam. -/
theorem norm_cmp95RescaledPeriodicSquareWeight_finTorus_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (M0 Q : ℕ) [NeZero M0] [NeZero Q]
    (cell : Fin Q) (x y : Fin (M0 * Q)) :
    ‖cmp95RescaledPeriodicSquareWeight P Q M0 cell y.val -
        cmp95RescaledPeriodicSquareWeight P Q M0 cell x.val‖ ≤
      ((8 * P.derivBound) / M0) * (finTorusDist x y : ℝ) := by
  apply norm_periodic_fin_value_sub_le_finTorusDist
  · exact div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
      (Nat.cast_nonneg M0)
  · intro t
    simpa only [Nat.cast_mul] using
      cmp95RescaledPeriodicSquareWeight_add_period
        P Q (M0 : ℝ) (by exact_mod_cast NeZero.ne M0) cell t
  · exact norm_cmp95RescaledPeriodicSquareWeight_sub_le
      P Q (by exact_mod_cast NeZero.pos M0) cell

/-- Tensorization converts the circular coordinate bounds into the existing
four-dimensional Chebyshev torus distance, with the explicit factor four. -/
theorem norm_cmp95RescaledPeriodicTensorSquareWeight_finBox_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (M0 Q : ℕ) [NeZero M0] [NeZero Q]
    (cell : FinBox 4 Q) (offset : Fin 4 → ℝ)
    (x y : FinBox 4 (M0 * Q)) :
    ‖cmp95RescaledPeriodicTensorSquareWeight P Q M0 cell
          (fun i => (y i).val + offset i) -
        cmp95RescaledPeriodicTensorSquareWeight P Q M0 cell
          (fun i => (x i).val + offset i)‖ ≤
      ((32 * P.derivBound) / M0) * (finBoxDist x y : ℝ) := by
  classical
  unfold cmp95RescaledPeriodicTensorSquareWeight
  calc
    ‖∏ i, cmp95RescaledPeriodicSquareWeight P Q M0 (cell i)
          ((y i).val + offset i) -
        ∏ i, cmp95RescaledPeriodicSquareWeight P Q M0 (cell i)
          ((x i).val + offset i)‖ ≤
      ∑ i, ‖cmp95RescaledPeriodicSquareWeight P Q M0 (cell i)
          ((y i).val + offset i) -
        cmp95RescaledPeriodicSquareWeight P Q M0 (cell i)
          ((x i).val + offset i)‖ := by
      apply CMP95SourceSmoothPartitionProfile.norm_prod_sub_prod_le_sum_norm_sub
        Finset.univ
      · intro i _
        rw [Real.norm_eq_abs, abs_of_nonneg
          (cmp95RescaledPeriodicSquareWeight_nonneg P Q M0 (cell i)
            ((y i).val + offset i))]
        exact cmp95RescaledPeriodicSquareWeight_le_one P Q M0 (cell i)
          ((y i).val + offset i)
      · intro i _
        rw [Real.norm_eq_abs, abs_of_nonneg
          (cmp95RescaledPeriodicSquareWeight_nonneg P Q M0 (cell i)
            ((x i).val + offset i))]
        exact cmp95RescaledPeriodicSquareWeight_le_one P Q M0 (cell i)
          ((x i).val + offset i)
    _ ≤ ∑ _i : Fin 4,
        ((8 * P.derivBound) / M0) * (finBoxDist x y : ℝ) := by
      gcongr with i
      let f : ℝ → ℝ := fun t =>
        cmp95RescaledPeriodicSquareWeight P Q M0 (cell i) (t + offset i)
      have hi : ‖f (y i).val - f (x i).val‖ ≤
          ((8 * P.derivBound) / M0) *
            (finTorusDist (x i) (y i) : ℝ) := by
        apply norm_periodic_fin_value_sub_le_finTorusDist
        · exact div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
            (Nat.cast_nonneg M0)
        · intro t
          dsimp [f]
          rw [show t + (M0 * Q : ℕ) + offset i =
              (t + offset i) + (M0 : ℝ) * Q by push_cast; ring]
          exact cmp95RescaledPeriodicSquareWeight_add_period
            P Q M0 (by exact_mod_cast NeZero.ne M0) (cell i) (t + offset i)
        · intro u v
          change ‖cmp95RescaledPeriodicSquareWeight P Q M0 (cell i)
              (v + offset i) -
            cmp95RescaledPeriodicSquareWeight P Q M0 (cell i)
              (u + offset i)‖ ≤ _
          simpa only [add_sub_add_right_eq_sub] using
            norm_cmp95RescaledPeriodicSquareWeight_sub_le P Q
              (by exact_mod_cast NeZero.pos M0) (cell i)
              (u + offset i) (v + offset i)
      exact hi.trans
        (mul_le_mul_of_nonneg_left
          (Nat.cast_le.2 (finTorusDist_le_finBoxDist x y i))
          (div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
            (Nat.cast_nonneg M0)))
    _ = ((32 * P.derivBound) / M0) * (finBoxDist x y : ℝ) := by
      simp
      ring

/-- Boundary-safe generated fine-lattice cutoff slope in the physical
`finBoxDist`.  The scale and torus side are generated internally. -/
theorem norm_cmp99SourceGeneratedFineCellSquareWeight_finBox_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q)
    (x y : FinBox 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1))) :
    ‖cmp99SourceGeneratedFineCellSquareWeight P M Q depth cell y -
        cmp99SourceGeneratedFineCellSquareWeight P M Q depth cell x‖ ≤
      ((32 * P.derivBound) /
        cmp99SourceGeneratedCellCutoffScale M depth) *
        (finBoxDist x y : ℝ) := by
  classical
  let M0 := 2 * M ^ (depth + 1)
  have hM0 : NeZero M0 :=
    ⟨Nat.mul_ne_zero (by omega) (pow_ne_zero _ (NeZero.ne M))⟩
  have hperiodNat : M0 * Q =
      cmp99RegionalLatticeSize M (2 * Q) (depth + 1) :=
    cmp99SourceGeneratedCellCutoffScale_mul_Q M Q depth
  let offset : Fin 4 → ℝ := fun _ =>
    1 / 2 - cmp99SourceGeneratedCellCutoffScale M depth / 2
  have hcoord (i : Fin 4) :
      ‖cmp95RescaledPeriodicSquareWeight P Q
          (cmp99SourceGeneratedCellCutoffScale M depth) (cell i)
          (cmp99SourceGeneratedFineCellCoordinate M depth
            (fun i => (y i).val) i) -
        cmp95RescaledPeriodicSquareWeight P Q
          (cmp99SourceGeneratedCellCutoffScale M depth) (cell i)
          (cmp99SourceGeneratedFineCellCoordinate M depth
            (fun i => (x i).val) i)‖ ≤
        ((8 * P.derivBound) / M0) *
          (finTorusDist (x i) (y i) : ℝ) := by
    let f : ℝ → ℝ := fun t =>
      cmp95RescaledPeriodicSquareWeight P Q M0 (cell i) (t + offset i)
    have hraw := norm_periodic_fin_value_sub_le_finTorusDist
      (L := ((8 * P.derivBound) / M0)) f
      (div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
        (Nat.cast_nonneg M0))
      (fun t => by
        dsimp [f]
        have hperiodNat' :
            M * cmp99RegionalLatticeSize M (2 * Q) depth = M0 * Q := by
          rw [cmp99RegionalLatticeSize_eq_pow_mul]
          dsimp [M0]
          rw [pow_succ]
          ring
        rw [hperiodNat']
        push_cast
        rw [show t + (M0 : ℝ) * Q + offset i =
            (t + offset i) + (M0 : ℝ) * Q by ring]
        exact cmp95RescaledPeriodicSquareWeight_add_period
          P Q M0 (by exact_mod_cast NeZero.ne M0) (cell i) (t + offset i))
      (fun u v => by
        dsimp [f]
        simpa only [add_sub_add_right_eq_sub] using
          norm_cmp95RescaledPeriodicSquareWeight_sub_le P Q
            (by exact_mod_cast NeZero.pos M0) (cell i)
            (u + offset i) (v + offset i))
      (x i) (y i)
    simpa [f, M0, offset, cmp99SourceGeneratedCellCutoffScale,
      cmp99SourceGeneratedFineCellCoordinate, sub_eq_add_neg, add_assoc] using hraw
  unfold cmp99SourceGeneratedFineCellSquareWeight
    cmp95RescaledPeriodicTensorSquareWeight
  calc
    ‖∏ i, cmp95RescaledPeriodicSquareWeight P Q
          (cmp99SourceGeneratedCellCutoffScale M depth) (cell i)
          (cmp99SourceGeneratedFineCellCoordinate M depth
            (fun i => (y i).val) i) -
        ∏ i, cmp95RescaledPeriodicSquareWeight P Q
          (cmp99SourceGeneratedCellCutoffScale M depth) (cell i)
          (cmp99SourceGeneratedFineCellCoordinate M depth
            (fun i => (x i).val) i)‖ ≤
      ∑ i, ‖cmp95RescaledPeriodicSquareWeight P Q M0 (cell i)
          (cmp99SourceGeneratedFineCellCoordinate M depth
            (fun i => (y i).val) i) -
        cmp95RescaledPeriodicSquareWeight P Q M0 (cell i)
          (cmp99SourceGeneratedFineCellCoordinate M depth
            (fun i => (x i).val) i)‖ := by
      simp only [M0, cmp99SourceGeneratedCellCutoffScale]
      apply CMP95SourceSmoothPartitionProfile.norm_prod_sub_prod_le_sum_norm_sub
        Finset.univ
      · intro i _
        rw [Real.norm_eq_abs, abs_of_nonneg
          (cmp95RescaledPeriodicSquareWeight_nonneg P Q _ (cell i) _)]
        exact cmp95RescaledPeriodicSquareWeight_le_one P Q _ (cell i) _
      · intro i _
        rw [Real.norm_eq_abs, abs_of_nonneg
          (cmp95RescaledPeriodicSquareWeight_nonneg P Q _ (cell i) _)]
        exact cmp95RescaledPeriodicSquareWeight_le_one P Q _ (cell i) _
    _ ≤ ∑ _i : Fin 4,
        ((8 * P.derivBound) / M0) * (finBoxDist x y : ℝ) := by
      gcongr with i
      exact (hcoord i).trans (mul_le_mul_of_nonneg_left
        (Nat.cast_le.2 (finTorusDist_le_finBoxDist x y i))
        (div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
          (Nat.cast_nonneg M0)))
    _ = ((32 * P.derivBound) /
        cmp99SourceGeneratedCellCutoffScale M depth) *
        (finBoxDist x y : ℝ) := by
      simp [M0, cmp99SourceGeneratedCellCutoffScale]
      ring

end

end YangMills.RG

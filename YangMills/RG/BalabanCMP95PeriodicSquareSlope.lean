/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95RescaledPeriodicSquarePartition
import Mathlib.Data.Int.Interval

/-!
# Uniformly finite support of the periodized CMP95 square cutoff

The source profile is supported in `(-2/3,2/3)`.  Since distinct translates
in one residue class are separated by the positive integer period `Q`, a
nonzero term can only occur at one of the two integers bracketing the
dimensionless coordinate `(t-cell)/Q`.  This is the finite-overlap input
needed to turn the profile slope into a volume-independent periodized slope.
-/

namespace YangMills.RG

noncomputable section

/-- The two integer translates which may meet the source support at a fixed
coordinate. -/
def cmp95PeriodicActiveWindow
    (Q : ℕ) [NeZero Q] (cell : Fin Q) (t : ℝ) : Finset ℤ :=
  let n := ⌊(t - cell.val) / Q⌋
  Finset.Icc n (n + 1)

/-- Compact support and positive period force every nonzero summand into the
two-point active window.  No cardinality of the periodic lattice appears. -/
theorem mem_cmp95PeriodicActiveWindow_of_ne_zero
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) (k : ℤ)
    (hk : P.value
      (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2 ≠ 0) :
    k ∈ cmp95PeriodicActiveWindow Q cell t := by
  have hvalue : P.value
      (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ≠ 0 := by
    intro h
    exact hk (by rw [h, zero_pow (by omega)])
  have hsupp := P.support_subset (Function.mem_support.mpr hvalue)
  let u : ℝ := (t - cell.val) / Q
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast NeZero.pos Q
  have hQone : (1 : ℝ) ≤ Q := by
    exact_mod_cast (NeZero.one_le : 1 ≤ Q)
  have hid : (Q : ℝ) * (u - (k : ℝ)) =
      t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ) := by
    dsimp [u]
    field_simp
    push_cast
    ring
  have huLower : -(2 / 3 : ℝ) < u - (k : ℝ) := by
    rcases hsupp with ⟨hsuppLower, hsuppUpper⟩
    nlinarith
  have huUpper : u - (k : ℝ) < 2 / 3 := by
    rcases hsupp with ⟨hsuppLower, hsuppUpper⟩
    nlinarith
  have hfloorLower : ((⌊u⌋ : ℤ) : ℝ) ≤ u := Int.floor_le u
  have hfloorUpper : u < ((⌊u⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one u
  have hkLowerReal : (((⌊u⌋ : ℤ) - 1 : ℤ) : ℝ) < (k : ℝ) := by
    push_cast
    nlinarith
  have hkUpperReal : (k : ℝ) < ((((⌊u⌋ : ℤ) + 2 : ℤ)) : ℝ) := by
    push_cast
    nlinarith
  have hkLowerInt : (⌊u⌋ : ℤ) ≤ k := by
    have : (⌊u⌋ : ℤ) - 1 < k := by exact_mod_cast hkLowerReal
    omega
  have hkUpperInt : k ≤ (⌊u⌋ : ℤ) + 1 := by
    have : k < (⌊u⌋ : ℤ) + 2 := by exact_mod_cast hkUpperReal
    omega
  exact Finset.mem_Icc.mpr ⟨hkLowerInt, hkUpperInt⟩

/-- The active window has exactly two integer points. -/
theorem card_cmp95PeriodicActiveWindow
    (Q : ℕ) [NeZero Q] (cell : Fin Q) (t : ℝ) :
    (cmp95PeriodicActiveWindow Q cell t).card = 2 := by
  unfold cmp95PeriodicActiveWindow
  rw [Int.card_Icc]
  have h :
      (⌊(t - (cell.val : ℝ)) / Q⌋ + 1 + 1 -
        ⌊(t - (cell.val : ℝ)) / Q⌋ : ℤ) = 2 := by
    omega
  rw [h]
  rfl

/-- The infinite residue-class sum is literally the sum over its two-point
active window. -/
theorem cmp95PeriodicSquareWeight_eq_sum_activeWindow
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    cmp95PeriodicSquareWeight P Q cell t =
      ∑ k ∈ cmp95PeriodicActiveWindow Q cell t,
        P.value
          (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2 := by
  unfold cmp95PeriodicSquareWeight
  exact tsum_eq_sum fun k hk => by
    by_contra hne
    exact hk (mem_cmp95PeriodicActiveWindow_of_ne_zero P Q cell t k hne)

/-- A periodized one-dimensional square weight has a global slope `8L`.
The factor is the product of the elementary square cost `2`, and the at most
four translates in the union of the two active windows.  In particular the
constant is independent of `Q`. -/
theorem norm_cmp95PeriodicSquareWeight_sub_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (x y : ℝ) :
    ‖cmp95PeriodicSquareWeight P Q cell y -
        cmp95PeriodicSquareWeight P Q cell x‖ ≤
      (8 * P.derivBound) * ‖y - x‖ := by
  classical
  let W := cmp95PeriodicActiveWindow Q cell x ∪
    cmp95PeriodicActiveWindow Q cell y
  have hy : cmp95PeriodicSquareWeight P Q cell y =
      ∑ k ∈ W, P.value
        (y - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2 := by
    unfold cmp95PeriodicSquareWeight
    exact tsum_eq_sum fun k hk => by
      by_contra hne
      have hmem := mem_cmp95PeriodicActiveWindow_of_ne_zero
        P Q cell y k hne
      exact hk (Finset.mem_union_right _ hmem)
  have hx : cmp95PeriodicSquareWeight P Q cell x =
      ∑ k ∈ W, P.value
        (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2 := by
    unfold cmp95PeriodicSquareWeight
    exact tsum_eq_sum fun k hk => by
      by_contra hne
      have hmem := mem_cmp95PeriodicActiveWindow_of_ne_zero
        P Q cell x k hne
      exact hk (Finset.mem_union_left _ hmem)
  rw [hy, hx, ← Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ W,
        (P.value
          (y - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2 -
        P.value
          (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2)‖ ≤
      ∑ k ∈ W, ‖P.value
          (y - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2 -
        P.value
          (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ W, (2 * P.derivBound) * ‖y - x‖ := by
      gcongr with k hk
      simpa only [sub_sub_sub_cancel_right] using
        P.norm_value_sq_sub_value_sq_le
          (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))
          (y - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))
    _ = (W.card : ℝ) * ((2 * P.derivBound) * ‖y - x‖) := by
      simp
    _ ≤ 4 * ((2 * P.derivBound) * ‖y - x‖) := by
      have hcard : W.card ≤ 4 := by
        calc
          W.card ≤
              (cmp95PeriodicActiveWindow Q cell x).card +
              (cmp95PeriodicActiveWindow Q cell y).card :=
            by
              change
                (cmp95PeriodicActiveWindow Q cell x ∪
                  cmp95PeriodicActiveWindow Q cell y).card ≤ _
              exact Finset.card_union_le
                (cmp95PeriodicActiveWindow Q cell x)
                (cmp95PeriodicActiveWindow Q cell y)
          _ = 4 := by
            rw [card_cmp95PeriodicActiveWindow,
              card_cmp95PeriodicActiveWindow]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · exact mul_nonneg
          (mul_nonneg (by norm_num) P.derivBound_nonneg)
          (norm_nonneg _)
    _ = (8 * P.derivBound) * ‖y - x‖ := by ring

/-- Each residue-class square weight is contractive.  This is derived from
nonnegativity and the exact finite partition, not added to the source data. -/
theorem cmp95PeriodicSquareWeight_le_one
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    cmp95PeriodicSquareWeight P Q cell t ≤ 1 := by
  calc
    cmp95PeriodicSquareWeight P Q cell t ≤
        ∑ c : Fin Q, cmp95PeriodicSquareWeight P Q c t := by
      exact Finset.single_le_sum
        (fun c _hc => cmp95PeriodicSquareWeight_nonneg P Q c t)
        (Finset.mem_univ cell)
    _ = 1 := sum_cmp95PeriodicSquareWeight P Q t

/-- Physical rescaling converts the uniform periodized slope into `8L/M0`. -/
theorem norm_cmp95RescaledPeriodicSquareWeight_sub_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    {M0 : ℝ} (hM0 : 0 < M0) (cell : Fin Q) (x y : ℝ) :
    ‖cmp95RescaledPeriodicSquareWeight P Q M0 cell y -
        cmp95RescaledPeriodicSquareWeight P Q M0 cell x‖ ≤
      ((8 * P.derivBound) / M0) * ‖y - x‖ := by
  have h := norm_cmp95PeriodicSquareWeight_sub_le
    P Q cell (x / M0) (y / M0)
  unfold cmp95RescaledPeriodicSquareWeight
  calc
    ‖cmp95PeriodicSquareWeight P Q cell (y / M0) -
        cmp95PeriodicSquareWeight P Q cell (x / M0)‖ ≤
      (8 * P.derivBound) * ‖y / M0 - x / M0‖ := h
    _ = (8 * P.derivBound) * ‖(y - x) / M0‖ := by ring_nf
    _ = ((8 * P.derivBound) / M0) * ‖y - x‖ := by
      rw [norm_div, show ‖M0‖ = M0 by
        simpa [Real.norm_eq_abs] using abs_of_pos hM0]
      ring

theorem cmp95RescaledPeriodicSquareWeight_le_one
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : Fin Q) (t : ℝ) :
    cmp95RescaledPeriodicSquareWeight P Q M0 cell t ≤ 1 :=
  cmp95PeriodicSquareWeight_le_one P Q cell (t / M0)

/-- The four-dimensional periodized square cutoff has the source-scale
Lipschitz cost `8L/M0` against the `ℓ¹` coordinate distance, uniformly in
the periodic volume. -/
theorem norm_cmp95RescaledPeriodicTensorSquareWeight_sub_le
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    {M0 : ℝ} (hM0 : 0 < M0) (cell : FinBox 4 Q)
    (x y : Fin 4 → ℝ) :
    ‖cmp95RescaledPeriodicTensorSquareWeight P Q M0 cell y -
        cmp95RescaledPeriodicTensorSquareWeight P Q M0 cell x‖ ≤
      ((8 * P.derivBound) / M0) * ∑ i, ‖y i - x i‖ := by
  classical
  unfold cmp95RescaledPeriodicTensorSquareWeight
  calc
    ‖∏ i, cmp95RescaledPeriodicSquareWeight P Q M0 (cell i) (y i) -
        ∏ i, cmp95RescaledPeriodicSquareWeight P Q M0 (cell i) (x i)‖ ≤
      ∑ i, ‖cmp95RescaledPeriodicSquareWeight P Q M0 (cell i) (y i) -
        cmp95RescaledPeriodicSquareWeight P Q M0 (cell i) (x i)‖ := by
      apply CMP95SourceSmoothPartitionProfile.norm_prod_sub_prod_le_sum_norm_sub
        Finset.univ
      · intro i _hi
        rw [Real.norm_eq_abs, abs_of_nonneg
          (cmp95RescaledPeriodicSquareWeight_nonneg P Q M0 (cell i) (y i))]
        exact cmp95RescaledPeriodicSquareWeight_le_one P Q M0 (cell i) (y i)
      · intro i _hi
        rw [Real.norm_eq_abs, abs_of_nonneg
          (cmp95RescaledPeriodicSquareWeight_nonneg P Q M0 (cell i) (x i))]
        exact cmp95RescaledPeriodicSquareWeight_le_one P Q M0 (cell i) (x i)
    _ ≤ ∑ i, ((8 * P.derivBound) / M0) * ‖y i - x i‖ := by
      gcongr with i
      exact norm_cmp95RescaledPeriodicSquareWeight_sub_le
        P Q hM0 (cell i) (x i) (y i)
    _ = ((8 * P.derivBound) / M0) * ∑ i, ‖y i - x i‖ := by
      rw [Finset.mul_sum]

/-- Generated fine-lattice form of the tensor slope.  The source cell scale
is produced internally as `2*M^(depth+1)`; no scale parameter remains in the
public interface. -/
theorem norm_cmp99SourceGeneratedFineCellSquareWeight_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q)
    (x y : FinBox 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1))) :
    ‖cmp99SourceGeneratedFineCellSquareWeight P M Q depth cell y -
        cmp99SourceGeneratedFineCellSquareWeight P M Q depth cell x‖ ≤
      ((8 * P.derivBound) /
        cmp99SourceGeneratedCellCutoffScale M depth) *
        ∑ i, ‖((y i).val : ℝ) - ((x i).val : ℝ)‖ := by
  have h := norm_cmp95RescaledPeriodicTensorSquareWeight_sub_le
    P Q (cmp99SourceGeneratedCellCutoffScale_pos M depth) cell
    (cmp99SourceGeneratedFineCellCoordinate M depth fun i => (x i).val)
    (cmp99SourceGeneratedFineCellCoordinate M depth fun i => (y i).val)
  simpa [cmp99SourceGeneratedFineCellSquareWeight,
    cmp99SourceGeneratedFineCellCoordinate] using h

end

end YangMills.RG

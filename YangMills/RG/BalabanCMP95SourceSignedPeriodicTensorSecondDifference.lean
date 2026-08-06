/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95SourceSignedPeriodicCutoffSecondDifference

/-!
# Tensor second differences of the signed periodic CMP95 cutoff

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and the result has not yet been verified by the Lean compiler.

This is the canonical-torus analytic core of the cutoff-Laplacian species in
CMP99 (3.88).  It transports the sealed one-dimensional quadratic estimate
through the periodic seam, factors the tensor cutoff along the active
coordinate, and sums the four literal lattice directions.  The resulting
constant is `48 = 4 * 12` and retains the inverse-square cutoff scale before
any Green, cell-overlap, or regional-compression estimate.

No source-separated cast and no identification with the physical precision
is made in this file.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- A raw centred second-difference estimate for a period-`N` function
transports exactly to the canonical representatives of `Fin N`. -/
theorem norm_periodic_fin_centeredSecondDifference_le
    {N : ℕ} [NeZero N] (f : ℝ → ℝ) {A : ℝ}
    (hperiod : ∀ t, f (t + N) = f t)
    (hsecond : ∀ t, ‖f (t + 1) - 2 * f t + f (t - 1)‖ ≤ A)
    (x : Fin N) :
    ‖f (((x.val + 1) % N : ℕ) : ℝ) - 2 * f x.val +
        f (((x.val + N - 1) % N : ℕ) : ℝ)‖ ≤ A := by
  have hforward :
      f (((x.val + 1) % N : ℕ) : ℝ) = f ((x.val : ℝ) + 1) := by
    by_cases htop : x.val + 1 < N
    · rw [Nat.mod_eq_of_lt htop]
      norm_num
    · have heq : x.val + 1 = N := by omega
      have heqR : (x.val : ℝ) + 1 = N := by exact_mod_cast heq
      rw [heq, Nat.mod_self]
      have hp := hperiod 0
      rw [heqR]
      simpa using hp.symm
  have hback :
      f (((x.val + N - 1) % N : ℕ) : ℝ) = f ((x.val : ℝ) - 1) := by
    by_cases hx0 : x.val = 0
    · have hmod : (x.val + N - 1) % N = N - 1 := by
        rw [hx0, Nat.zero_add, Nat.mod_eq_of_lt]
        omega
      rw [hmod]
      have hx0R : (x.val : ℝ) = 0 := by exact_mod_cast hx0
      rw [hx0R]
      have hp := hperiod (-1)
      calc
        f (N - 1 : ℕ) = f (-1 + N) := by
          congr 1
          push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
          ring
        _ = f (-1) := hp
        _ = f (0 - 1) := by norm_num
    · have hnat : x.val + N - 1 = (x.val - 1) + N := by omega
      rw [hnat, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x.val - 1 < N)]
      push_cast [Nat.cast_sub (by omega : 1 ≤ x.val)]
      rfl
  rw [hforward, hback]
  exact hsecond x.val

/-- One coordinate shift of the rescaled signed tensor cutoff has the same
quadratic constant as its one-dimensional active factor.  All inactive
factors have norm at most one. -/
theorem
    norm_cmp95RescaledSourcePeriodicSignedTensorCutoff_centeredShift_le
    (P : CMP95SourceSmoothPartitionProfile)
    (M0 Q : ℕ) [NeZero M0] [NeZero Q]
    (cell : FinBox 4 Q) (offset : Fin 4 → ℝ)
    (x : FinBox 4 (M0 * Q)) (i : Fin 4) :
    ‖cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun j => ((x.shift i) j).val + offset j) -
        2 * cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun j => (x j).val + offset j) +
        cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun j => ((x.shiftBack i) j).val + offset j)‖ ≤
      (12 * P.secondDerivBound) / M0 ^ 2 := by
  classical
  let f : ℝ → ℝ := fun t =>
    cmp95RescaledSourcePeriodicSignedCutoff P Q M0 (cell i) (t + offset i)
  let rest : ℝ := ∏ j ∈ (Finset.univ.erase i),
    cmp95RescaledSourcePeriodicSignedCutoff P Q M0 (cell j)
      ((x j).val + offset j)
  have hplus :
      cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun j => ((x.shift i) j).val + offset j) =
        f ((((x i).val + 1) % (M0 * Q) : ℕ) : ℝ) * rest := by
    unfold cmp95RescaledSourcePeriodicSignedTensorCutoff
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp [f, FinBox.shift]
    · apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [FinBox.shift, hji]
  have hzero :
      cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun j => (x j).val + offset j) = f (x i).val * rest := by
    unfold cmp95RescaledSourcePeriodicSignedTensorCutoff
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hminus :
      cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun j => ((x.shiftBack i) j).val + offset j) =
        f ((((x i).val + (M0 * Q) - 1) % (M0 * Q) : ℕ) : ℝ) * rest := by
    unfold cmp95RescaledSourcePeriodicSignedTensorCutoff
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp [f, FinBox.shiftBack]
    · apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [FinBox.shiftBack, hji]
  have hrest : ‖rest‖ ≤ 1 := by
    dsimp [rest]
    change |∏ j ∈ Finset.univ.erase i,
      cmp95RescaledSourcePeriodicSignedCutoff P Q M0 (cell j)
        ((x j).val + offset j)| ≤ 1
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun j _ => by
      simpa [Real.norm_eq_abs] using
        norm_cmp95RescaledSourcePeriodicSignedCutoff_le_one
          P Q M0 (cell j) ((x j).val + offset j)
  have hactive :
      ‖f ((((x i).val + 1) % (M0 * Q) : ℕ) : ℝ) - 2 * f (x i).val +
          f ((((x i).val + (M0 * Q) - 1) % (M0 * Q) : ℕ) : ℝ)‖ ≤
        (12 * P.secondDerivBound) / M0 ^ 2 := by
    refine norm_periodic_fin_centeredSecondDifference_le f ?_ ?_ (x i)
    · intro t
      dsimp [f]
      rw [show t + (M0 * Q : ℕ) + offset i =
          (t + offset i) + (M0 : ℝ) * Q by push_cast; ring]
      exact cmp95RescaledSourcePeriodicSignedCutoff_add_period
        P Q M0 (by exact_mod_cast NeZero.ne M0) (cell i) (t + offset i)
    · intro t
      dsimp [f]
      have hM0 : (0 : ℝ) < M0 := by exact_mod_cast NeZero.pos M0
      have h :=
        norm_cmp95RescaledSourcePeriodicSignedCutoff_centeredSecondDifference_le
          P Q hM0 (cell i) (t + offset i) 1
      convert h using 1 <;> ring
  rw [hplus, hzero, hminus]
  calc
    ‖f ((((x i).val + 1) % (M0 * Q) : ℕ) : ℝ) * rest -
        2 * (f (x i).val * rest) +
        f ((((x i).val + (M0 * Q) - 1) % (M0 * Q) : ℕ) : ℝ) * rest‖ =
      ‖(f ((((x i).val + 1) % (M0 * Q) : ℕ) : ℝ) - 2 * f (x i).val +
          f ((((x i).val + (M0 * Q) - 1) % (M0 * Q) : ℕ) : ℝ)) * rest‖ := by
        congr 1
        ring
    _ = ‖f ((((x i).val + 1) % (M0 * Q) : ℕ) : ℝ) - 2 * f (x i).val +
          f ((((x i).val + (M0 * Q) - 1) % (M0 * Q) : ℕ) : ℝ)‖ * ‖rest‖ :=
      norm_mul _ _
    _ ≤ ((12 * P.secondDerivBound) / M0 ^ 2) * 1 := by
      have hbudget : 0 ≤ (12 * P.secondDerivBound) / (M0 : ℝ) ^ 2 :=
        div_nonneg (mul_nonneg (by norm_num) P.secondDerivBound_nonneg)
          (sq_nonneg (M0 : ℝ))
      exact mul_le_mul hactive hrest (norm_nonneg _)
        hbudget
    _ = (12 * P.secondDerivBound) / M0 ^ 2 := mul_one _

/-- Canonical scalar coefficient of the signed tensor cutoff Laplacian. -/
def cmp95RescaledSourcePeriodicSignedTensorCutoffLaplacianCoefficient
    (P : CMP95SourceSmoothPartitionProfile)
    (M0 Q : ℕ) [NeZero M0] [NeZero Q]
    (cell : FinBox 4 Q) (offset : Fin 4 → ℝ)
    (x : FinBox 4 (M0 * Q)) : ℝ :=
  ∑ i : Fin 4,
    ((cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun j => (x j).val + offset j) -
        cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun j => ((x.shift i) j).val + offset j)) +
      (cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun j => (x j).val + offset j) -
        cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
          (fun j => ((x.shiftBack i) j).val + offset j)))

/-- The literal four-dimensional tensor cutoff Laplacian retains the
inverse-square physical scale with explicit constant `48 = 4 * 12`. -/
theorem
    norm_cmp95RescaledSourcePeriodicSignedTensorCutoffLaplacianCoefficient_le
    (P : CMP95SourceSmoothPartitionProfile)
    (M0 Q : ℕ) [NeZero M0] [NeZero Q]
    (cell : FinBox 4 Q) (offset : Fin 4 → ℝ)
    (x : FinBox 4 (M0 * Q)) :
    ‖cmp95RescaledSourcePeriodicSignedTensorCutoffLaplacianCoefficient
        P M0 Q cell offset x‖ ≤
      (48 * P.secondDerivBound) / M0 ^ 2 := by
  unfold cmp95RescaledSourcePeriodicSignedTensorCutoffLaplacianCoefficient
  calc
    ‖∑ i : Fin 4, _‖ ≤ ∑ i : Fin 4, ‖_‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, (12 * P.secondDerivBound) / M0 ^ 2 := by
      gcongr with i
      rw [show
        (cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
              (fun j => (x j).val + offset j) -
            cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
              (fun j => ((x.shift i) j).val + offset j)) +
          (cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
              (fun j => (x j).val + offset j) -
            cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
              (fun j => ((x.shiftBack i) j).val + offset j)) =
          - (cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
              (fun j => ((x.shift i) j).val + offset j) -
            2 * cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
              (fun j => (x j).val + offset j) +
            cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell
              (fun j => ((x.shiftBack i) j).val + offset j)) by ring,
        norm_neg]
      exact
        norm_cmp95RescaledSourcePeriodicSignedTensorCutoff_centeredShift_le
          P M0 Q cell offset x i
    _ = (48 * P.secondDerivBound) / M0 ^ 2 := by
      rw [Fin.sum_univ_four]
      ring

end

end YangMills.RG

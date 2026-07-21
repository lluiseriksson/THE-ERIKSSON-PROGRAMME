/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicSquarePartition
import YangMills.RG.BalabanCMP99SourceGeneratedMassRange

/-!
# The CMP95 square partition at the literal generated source-cell scale

The normalization in CMP95 (1.118) is a translation partition whose spacing
equals its scale.  On the generated CMP99 fine lattice one physical source
cell contains two terminal large blocks, hence its side is

`M0 = 2 * M^(depth+1)`.

This file rescales the already proved periodic regrouping identity by that
literal spacing.  It deliberately does not identify this fine cutoff with
the block-sampled cutoff used in the exact coarse (3.95) algebra: the latter
is a different operator and becomes a characteristic after sampling.
-/

namespace YangMills.RG

noncomputable section

/-- Periodic one-dimensional CMP95 weight after a physical rescaling by
`M0`.  Writing it through the dimensionless coordinate `t / M0` makes the
translation spacing and the profile scale definitionally identical. -/
def cmp95RescaledPeriodicSquareWeight
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : Fin Q) (t : ℝ) : ℝ :=
  cmp95PeriodicSquareWeight P Q cell (t / M0)

/-- Exact finite square partition at every nonzero physical scale. -/
theorem sum_cmp95RescaledPeriodicSquareWeight
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (t : ℝ) :
    ∑ cell : Fin Q, cmp95RescaledPeriodicSquareWeight P Q M0 cell t = 1 := by
  exact sum_cmp95PeriodicSquareWeight P Q (t / M0)

theorem cmp95RescaledPeriodicSquareWeight_nonneg
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : Fin Q) (t : ℝ) :
    0 ≤ cmp95RescaledPeriodicSquareWeight P Q M0 cell t :=
  cmp95PeriodicSquareWeight_nonneg P Q cell (t / M0)

/-- Four-dimensional tensor product of the rescaled periodic weights. -/
def cmp95RescaledPeriodicTensorSquareWeight
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : FinBox 4 Q) (x : Fin 4 → ℝ) : ℝ :=
  ∏ i, cmp95RescaledPeriodicSquareWeight P Q M0 (cell i) (x i)

/-- The rescaled tensor weights form an exact finite square partition. -/
theorem sum_cmp95RescaledPeriodicTensorSquareWeight
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (x : Fin 4 → ℝ) :
    ∑ cell : FinBox 4 Q,
      cmp95RescaledPeriodicTensorSquareWeight P Q M0 cell x = 1 := by
  unfold cmp95RescaledPeriodicTensorSquareWeight
  rw [← Fintype.prod_sum (fun i (cell : Fin Q) =>
    cmp95RescaledPeriodicSquareWeight P Q M0 cell (x i))]
  simp [sum_cmp95RescaledPeriodicSquareWeight]

theorem cmp95RescaledPeriodicTensorSquareWeight_nonneg
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : FinBox 4 Q) (x : Fin 4 → ℝ) :
    0 ≤ cmp95RescaledPeriodicTensorSquareWeight P Q M0 cell x := by
  unfold cmp95RescaledPeriodicTensorSquareWeight
  exact Finset.prod_nonneg fun i _ =>
    cmp95RescaledPeriodicSquareWeight_nonneg P Q M0 (cell i) (x i)

/-- Nonnegative cutoff associated with the rescaled tensor weight. -/
def cmp95RescaledPeriodicTensorCutoff
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : FinBox 4 Q) (x : Fin 4 → ℝ) : ℝ :=
  Real.sqrt (cmp95RescaledPeriodicTensorSquareWeight P Q M0 cell x)

theorem cmp95RescaledPeriodicTensorCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : FinBox 4 Q) (x : Fin 4 → ℝ) :
    cmp95RescaledPeriodicTensorCutoff P Q M0 cell x ^ 2 =
      cmp95RescaledPeriodicTensorSquareWeight P Q M0 cell x :=
  Real.sq_sqrt
    (cmp95RescaledPeriodicTensorSquareWeight_nonneg P Q M0 cell x)

theorem sum_cmp95RescaledPeriodicTensorCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (x : Fin 4 → ℝ) :
    ∑ cell : FinBox 4 Q,
      cmp95RescaledPeriodicTensorCutoff P Q M0 cell x ^ 2 = 1 := by
  simp_rw [cmp95RescaledPeriodicTensorCutoff_sq]
  exact sum_cmp95RescaledPeriodicTensorSquareWeight P Q M0 x

/-- Literal generated fine-lattice side of one two-large-block source cell.
This is the only scale compatible simultaneously with `Q` translated source
cells and the fine torus of side `M^(depth+1) * (2Q)`. -/
def cmp99SourceGeneratedCellCutoffScale (M depth : ℕ) : ℝ :=
  (2 * M ^ (depth + 1) : ℕ)

theorem cmp99SourceGeneratedCellCutoffScale_pos
    (M depth : ℕ) [NeZero M] :
    0 < cmp99SourceGeneratedCellCutoffScale M depth := by
  unfold cmp99SourceGeneratedCellCutoffScale
  exact_mod_cast Nat.mul_pos (by omega) (pow_pos (NeZero.pos M) (depth + 1))

/-- The translated fine-cell spacing tiles the generated torus exactly. -/
theorem cmp99SourceGeneratedCellCutoffScale_mul_Q
    (M Q depth : ℕ) :
    2 * M ^ (depth + 1) * Q =
      cmp99RegionalLatticeSize M (2 * Q) (depth + 1) := by
  rw [cmp99RegionalLatticeSize_eq_pow_mul]
  ring

/-- The previously used one-extra-`M` scale agrees with the literal
two-large-block cell side only in the special case `M = 2`.  This arithmetic
fact is why the two scales must not be interchanged in the general source
dictionary. -/
theorem generated_extraM_scale_eq_cell_scale_iff
    (M depth : ℕ) [NeZero M] :
    M ^ (depth + 2) = 2 * M ^ (depth + 1) ↔ M = 2 := by
  have hpow : M ^ (depth + 2) = M ^ (depth + 1) * M := by
    rw [show depth + 2 = depth + 1 + 1 by omega, pow_succ]
  rw [hpow, mul_comm 2 (M ^ (depth + 1))]
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_left
      (pow_pos (NeZero.pos M) (depth + 1)) h
  · intro hM
    rw [hM]

/-- Physical coordinate centered on a two-large-block source cell.  The
`1/2` treats lattice points as unit-cell centers; the final `M0/2` shift is
the fine-lattice counterpart of the coarse convention
`block.val / 2 - 1 / 4`. -/
def cmp99SourceGeneratedFineCellCoordinate
    (M depth : ℕ) (x : Fin 4 → ℕ) : Fin 4 → ℝ :=
  fun i => (x i : ℝ) + 1 / 2 -
    cmp99SourceGeneratedCellCutoffScale M depth / 2

/-- Squared fine cutoff attached to a source cell, evaluated at the actual
fine site rather than at its terminal block owner. -/
def cmp99SourceGeneratedFineCellSquareWeight
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q)
    (x : FinBox 4 (cmp99RegionalLatticeSize M (2 * Q) (depth + 1))) : ℝ :=
  cmp95RescaledPeriodicTensorSquareWeight P Q
    (cmp99SourceGeneratedCellCutoffScale M depth) cell
    (cmp99SourceGeneratedFineCellCoordinate M depth fun i => (x i).val)

/-- Literal nonnegative fine cutoff at the corrected generated cell scale. -/
def cmp99SourceGeneratedFineCellCutoff
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q)
    (x : FinBox 4 (cmp99RegionalLatticeSize M (2 * Q) (depth + 1))) : ℝ :=
  cmp95RescaledPeriodicTensorCutoff P Q
    (cmp99SourceGeneratedCellCutoffScale M depth) cell
    (cmp99SourceGeneratedFineCellCoordinate M depth fun i => (x i).val)

theorem cmp99SourceGeneratedFineCellCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q)
    (x : FinBox 4 (cmp99RegionalLatticeSize M (2 * Q) (depth + 1))) :
    cmp99SourceGeneratedFineCellCutoff P M Q depth cell x ^ 2 =
      cmp99SourceGeneratedFineCellSquareWeight P M Q depth cell x :=
  cmp95RescaledPeriodicTensorCutoff_sq P Q
    (cmp99SourceGeneratedCellCutoffScale M depth) cell
    (cmp99SourceGeneratedFineCellCoordinate M depth fun i => (x i).val)

/-- The corrected generated fine cutoffs retain the exact CMP95 square
partition on every fine site. -/
theorem sum_cmp99SourceGeneratedFineCellSquareWeight
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (x : FinBox 4 (cmp99RegionalLatticeSize M (2 * Q) (depth + 1))) :
    ∑ cell : FinBox 4 Q,
      cmp99SourceGeneratedFineCellSquareWeight P M Q depth cell x = 1 := by
  exact sum_cmp95RescaledPeriodicTensorSquareWeight P Q
    (cmp99SourceGeneratedCellCutoffScale M depth)
    (cmp99SourceGeneratedFineCellCoordinate M depth fun i => (x i).val)

/-- Exact square partition for the corrected generated fine cutoffs. -/
theorem sum_cmp99SourceGeneratedFineCellCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (x : FinBox 4 (cmp99RegionalLatticeSize M (2 * Q) (depth + 1))) :
    ∑ cell : FinBox 4 Q,
      cmp99SourceGeneratedFineCellCutoff P M Q depth cell x ^ 2 = 1 := by
  simp_rw [cmp99SourceGeneratedFineCellCutoff_sq]
  exact sum_cmp99SourceGeneratedFineCellSquareWeight P M Q depth x

end

end YangMills.RG

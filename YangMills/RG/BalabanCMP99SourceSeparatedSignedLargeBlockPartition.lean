/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicActiveCellOverlap
import YangMills.RG.BalabanCMP95SourceSignedPeriodicCutoffSlope
import YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition

/-!
# PRE-VALIDATION: signed source-separated CMP99 large-block partition

The source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the Lean compiler.

This reinstantiates the literal source-separated regional partition with the
sign-preserving CMP95 periodization.  Its square partition is definitionally
tied to the already sealed square weight; its slope retains the inverse
independent large-block parameter before any cell sum; and its active cells
land in the same geometric sixteen-cell window as the retired square-root
cutoff.

The overlap cardinal is not accepted from the caller.  Only the implication
from a nonzero signed cutoff to membership in the pre-existing geometric
window is new, and it is derived from the exact equality of squares.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {L K Q depth : ℕ} [NeZero L] [NeZero K] [NeZero Q]

/-- A nonzero rescaled signed tensor cutoff belongs to the same geometric
active-cell window as the square-root realization of its square weight. -/
theorem mem_cmp95RescaledPeriodicTensorActiveCellWindow_of_signed_ne_zero
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : FinBox 4 Q) (x : Fin 4 → ℝ)
    (hcutoff :
      cmp95RescaledSourcePeriodicSignedTensorCutoff P Q M0 cell x ≠ 0) :
    cell ∈ cmp95RescaledPeriodicTensorActiveCellWindow Q M0 x := by
  have hweight : cmp95RescaledPeriodicTensorSquareWeight P Q M0 cell x ≠ 0 := by
    rw [← cmp95RescaledSourcePeriodicSignedTensorCutoff_sq]
    exact pow_ne_zero 2 hcutoff
  apply mem_cmp95RescaledPeriodicTensorActiveCellWindow_of_cutoff_ne_zero P Q
  intro hzero
  apply hweight
  rw [← cmp95RescaledPeriodicTensorCutoff_sq, hzero]
  norm_num

/-- Literal signed source cutoff on the separated large-block torus. -/
def cmp99SourceSeparatedSignedLargeBlockCutoff
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) : ℝ :=
  cmp95RescaledSourcePeriodicSignedTensorCutoff P Q
    (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) cell
    (cmp99SourceSeparatedLargeBlockCoordinate L K depth fun i => (x i).val)

/-- The signed source cutoffs form the same exact square partition. -/
theorem sum_cmp99SourceSeparatedSignedLargeBlockCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ∑ cell : FinBox 4 Q,
      cmp99SourceSeparatedSignedLargeBlockCutoff
        P L K Q depth cell x ^ 2 = 1 := by
  exact sum_cmp95RescaledSourcePeriodicSignedTensorCutoff_sq P Q
    (cmp99SourceSeparatedLargeBlockCutoffScale L K depth)
    (cmp99SourceSeparatedLargeBlockCoordinate L K depth fun i => (x i).val)

/-- The source-faithful signed partition consumed by the regional Dirichlet
Green algebra. -/
noncomputable def cmp99SourceSeparatedSignedLargeBlockSquarePartition
    (P : CMP95SourceSmoothPartitionProfile) :
    CMP99RegionalFineSquarePartition
      (cmp99SourceSeparatedLargeBlockSide L K depth) Q where
  value cell x :=
    cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell x
  square_sum x :=
    sum_cmp99SourceSeparatedSignedLargeBlockCutoff_sq P L K Q depth x

/-- The signed tensor slope times the generated precision range retains an
explicit inverse-`K` gain.  The literal coefficient `8` records the factor
two paid by the signed one-dimensional endpoint-window argument. -/
theorem cmp99SourceSeparatedSignedLargeBlockSlope_mul_precisionRange
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    ((16 * P.derivBound) /
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth) *
      (L ^ (depth + 1) : ℝ) =
        (8 * P.derivBound) / (K : ℝ) := by
  unfold cmp99SourceSeparatedLargeBlockCutoffScale
    cmp99SourceSeparatedLargeBlockSide
  push_cast
  have hpow : (L : ℝ) ^ (depth + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne L))
  have hK : (K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne K)
  field_simp [hpow, hK]
  ring

/-- Literal source slope of the signed separated regional partition. -/
theorem norm_cmp99SourceSeparatedSignedLargeBlockSquarePartition_value_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (cell : FinBox 4 Q)
    (x y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ‖(cmp99SourceSeparatedSignedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell y -
        (cmp99SourceSeparatedSignedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x‖ ≤
      ((16 * P.derivBound) /
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth) *
        (finBoxDist x y : ℝ) := by
  let hsize :
      cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q) =
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth * Q :=
    cmp99SourceSeparatedLargeBlockCutoffScale_mul_Q L K Q depth
  letI : NeZero (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) :=
    ⟨Nat.ne_of_gt
      (cmp99SourceSeparatedLargeBlockCutoffScale_pos L K depth)⟩
  let x' : FinBox 4
      (cmp99SourceSeparatedLargeBlockCutoffScale L K depth * Q) := hsize ▸ x
  let y' : FinBox 4
      (cmp99SourceSeparatedLargeBlockCutoffScale L K depth * Q) := hsize ▸ y
  have hxval (i : Fin 4) : (x' i).val = (x i).val :=
    finBox_cast_apply_val hsize x i
  have hyval (i : Fin 4) : (y' i).val = (y i).val :=
    finBox_cast_apply_val hsize y i
  have hdist : finBoxDist x' y' = finBoxDist x y :=
    finBoxDist_cast_size hsize x y
  have hxcoord :
      cmp99SourceSeparatedLargeBlockCoordinate L K depth
          (fun i => (x i).val) =
        fun i => (x' i).val +
          (1 / 2 -
            (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ) / 2) := by
    funext i
    rw [hxval i]
    unfold cmp99SourceSeparatedLargeBlockCoordinate
    ring
  have hycoord :
      cmp99SourceSeparatedLargeBlockCoordinate L K depth
          (fun i => (y i).val) =
        fun i => (y' i).val +
          (1 / 2 -
            (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ) / 2) := by
    funext i
    rw [hyval i]
    unfold cmp99SourceSeparatedLargeBlockCoordinate
    ring
  have h := norm_cmp95RescaledSourcePeriodicSignedTensorCutoff_finBox_sub_le
    P (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) Q cell
      (fun _ => 1 / 2 -
        (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ) / 2)
      x' y'
  change ‖cmp95RescaledSourcePeriodicSignedTensorCutoff P Q
        (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) cell
          (cmp99SourceSeparatedLargeBlockCoordinate L K depth
            fun i => (y i).val) -
      cmp95RescaledSourcePeriodicSignedTensorCutoff P Q
        (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) cell
          (cmp99SourceSeparatedLargeBlockCoordinate L K depth
            fun i => (x i).val)‖ ≤ _
  rw [hycoord, hxcoord]
  simpa [hdist] using h

/-- Signed source cells whose cutoff is nonzero at a fixed site. -/
def cmp99SourceSeparatedSignedLargeBlockActiveCells
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    Finset (FinBox 4 Q) :=
  Finset.univ.filter fun cell =>
    (cmp99SourceSeparatedSignedLargeBlockSquarePartition
      (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x ≠ 0

/-- Every active signed cell belongs to the pre-existing geometric window. -/
theorem cmp99SourceSeparatedSignedLargeBlockActiveCells_subset
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99SourceSeparatedSignedLargeBlockActiveCells P L K Q depth x ⊆
      cmp95RescaledPeriodicTensorActiveCellWindow Q
        (cmp99SourceSeparatedLargeBlockCutoffScale L K depth)
        (cmp99SourceSeparatedLargeBlockCoordinate L K depth
          fun i => (x i).val) := by
  classical
  intro cell hcell
  rw [cmp99SourceSeparatedSignedLargeBlockActiveCells,
    Finset.mem_filter] at hcell
  apply mem_cmp95RescaledPeriodicTensorActiveCellWindow_of_signed_ne_zero P Q
  simpa [cmp99SourceSeparatedSignedLargeBlockSquarePartition,
    cmp99SourceSeparatedSignedLargeBlockCutoff] using hcell.2

/-- The signed partition inherits the same literal overlap `2^4 = 16`. -/
theorem card_cmp99SourceSeparatedSignedLargeBlockActiveCells_le_sixteen
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    (cmp99SourceSeparatedSignedLargeBlockActiveCells
      P L K Q depth x).card ≤ 16 := by
  calc
    (cmp99SourceSeparatedSignedLargeBlockActiveCells
      P L K Q depth x).card ≤
        (cmp95RescaledPeriodicTensorActiveCellWindow Q
          (cmp99SourceSeparatedLargeBlockCutoffScale L K depth)
          (cmp99SourceSeparatedLargeBlockCoordinate L K depth
            fun i => (x i).val)).card :=
      Finset.card_le_card
        (cmp99SourceSeparatedSignedLargeBlockActiveCells_subset
          P L K Q depth x)
    _ ≤ 16 :=
      card_cmp95RescaledPeriodicTensorActiveCellWindow_le_sixteen _ _ _

end

end YangMills.RG

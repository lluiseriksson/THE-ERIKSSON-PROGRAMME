/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95SourceSignedPeriodicTensorSecondDifference
import YangMills.RG.BalabanCMP99SourceCovariantLaplacianCutoffIdentity
import YangMills.RG.BalabanCMP99SourceSeparatedSignedLargeBlockPartition

/-!
# Signed source-separated cutoff-Laplacian species

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and the result has not yet been verified by the Lean compiler.

This module transports the sealed canonical tensor second difference to the
literal source-separated carrier and identifies the resulting scalar
coefficient with the cutoff-Laplacian species in CMP99 (3.88).  The physical
inverse-square scale is exposed before any regional Green or cell-overlap sum.

No Green estimate, overlap factor, contraction, or CMP99 (3.89) conclusion is
proved here.
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroSignedSourceSeparatedAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- Literal scalar coefficient of the signed source-separated
cutoff-Laplacian species. -/
noncomputable def cmp99SourceSeparatedSignedCutoffLaplacianCoefficient
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) : ℝ :=
  ∑ i : Fin 4,
    ((cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell x -
        cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell (x.shift i)) +
      (cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell x -
        cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell (x.shiftBack i)))

/-- The source-separated signed cutoff-Laplacian coefficient retains the
literal inverse-square cutoff scale with constant `48`. -/
theorem norm_cmp99SourceSeparatedSignedCutoffLaplacianCoefficient_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ‖cmp99SourceSeparatedSignedCutoffLaplacianCoefficient
        (L := L) (K := K) P depth cell x‖ ≤
      (48 * P.secondDerivBound) /
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth ^ 2 := by
  let hsize :
      cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q) =
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth * Q :=
    cmp99SourceSeparatedLargeBlockCutoffScale_mul_Q L K Q depth
  letI : NeZero (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) :=
    ⟨Nat.ne_of_gt
      (cmp99SourceSeparatedLargeBlockCutoffScale_pos L K depth)⟩
  let x' : FinBox 4
      (cmp99SourceSeparatedLargeBlockCutoffScale L K depth * Q) := hsize ▸ x
  let offset : Fin 4 → ℝ := fun _ =>
    1 / 2 -
      (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ) / 2
  have hxval (j : Fin 4) : (x' j).val = (x j).val :=
    finBox_cast_apply_val hsize x j
  have hshiftCast (i : Fin 4) :
      hsize ▸ (x.shift i) = x'.shift i := by
    subst hsize
    rfl
  have hshiftBackCast (i : Fin 4) :
      hsize ▸ (x.shiftBack i) = x'.shiftBack i := by
    subst hsize
    rfl
  have hshiftVal (i j : Fin 4) :
      ((x'.shift i) j).val = ((x.shift i) j).val := by
    rw [← hshiftCast i]
    exact finBox_cast_apply_val hsize (x.shift i) j
  have hshiftBackVal (i j : Fin 4) :
      ((x'.shiftBack i) j).val = ((x.shiftBack i) j).val := by
    rw [← hshiftBackCast i]
    exact finBox_cast_apply_val hsize (x.shiftBack i) j
  have hxcoord :
      cmp99SourceSeparatedLargeBlockCoordinate L K depth
          (fun j => (x j).val) =
        fun j => (x' j).val + offset j := by
    funext j
    rw [hxval j]
    unfold cmp99SourceSeparatedLargeBlockCoordinate offset
    ring
  have hshiftCoord (i : Fin 4) :
      cmp99SourceSeparatedLargeBlockCoordinate L K depth
          (fun j => ((x.shift i) j).val) =
        fun j => ((x'.shift i) j).val + offset j := by
    funext j
    rw [hshiftVal i j]
    unfold cmp99SourceSeparatedLargeBlockCoordinate offset
    ring
  have hshiftBackCoord (i : Fin 4) :
      cmp99SourceSeparatedLargeBlockCoordinate L K depth
          (fun j => ((x.shiftBack i) j).val) =
        fun j => ((x'.shiftBack i) j).val + offset j := by
    funext j
    rw [hshiftBackVal i j]
    unfold cmp99SourceSeparatedLargeBlockCoordinate offset
    ring
  have h :=
    norm_cmp95RescaledSourcePeriodicSignedTensorCutoffLaplacianCoefficient_le
      P (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) Q
        cell offset x'
  unfold cmp95RescaledSourcePeriodicSignedTensorCutoffLaplacianCoefficient at h
  unfold cmp99SourceSeparatedSignedCutoffLaplacianCoefficient
    cmp99SourceSeparatedSignedLargeBlockCutoff
  rw [hxcoord]
  simp_rw [hshiftCoord, hshiftBackCoord]
  exact h

/-- At rescaled unit spacing, the literal scalar correction in CMP99 (3.88)
is exactly the signed source-separated coefficient acting on the field value. -/
theorem cmp99CutoffLaplacianCorrection_one_eq_sourceSeparatedSignedCoefficient
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99CutoffLaplacianCorrection (Nc := Nc) 1
        (cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell) phi x =
      cmp99SourceSeparatedSignedCutoffLaplacianCoefficient
        (L := L) (K := K) P depth cell x • phi x := by
  simp only [cmp99CutoffLaplacianCorrection, inv_one, one_smul]
  rw [← Finset.sum_smul]
  rfl

/-- Multiplying by the square of the generated precision range cancels the
RG depth scale and leaves the explicit inverse-`K^2` gain `12 / K^2`. -/
theorem cmp99SourceSeparatedSignedCutoffLaplacianBudget_mul_range_sq
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    ((48 * P.secondDerivBound) /
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth ^ 2) *
      (L ^ (depth + 1) : ℝ) ^ 2 =
        (12 * P.secondDerivBound) / (K : ℝ) ^ 2 := by
  unfold cmp99SourceSeparatedLargeBlockCutoffScale
    cmp99SourceSeparatedLargeBlockSide
  push_cast
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  field_simp [hL, hK]
  ring

end

end YangMills.RG

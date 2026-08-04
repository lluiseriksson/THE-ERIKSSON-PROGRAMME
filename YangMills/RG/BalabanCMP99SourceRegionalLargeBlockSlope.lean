/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalLargeBlockPartition

/-!
# Source-scale slope for the CMP99 regional partition

This transports the boundary-safe CMP95 estimate to the source large-block
partition.  Its denominator is `2 * M^(depth+2)`, while the generated
precision range is `M^(depth+1)`; the surviving ratio is therefore genuinely
of order `M^-1` rather than the fixed ratio of the auxiliary partition.
-/

namespace YangMills.RG

noncomputable section

variable {M Q depth : ℕ} [NeZero M] [NeZero Q]

/-- The large-block cutoff spacing tiles its ambient regional torus. -/
theorem cmp99SourceRegionalLargeBlockCutoffScale_mul_Q
    (M Q depth : ℕ) :
    cmp99SourceRegionalLargeBlockSide M depth * (2 * Q) =
      cmp99SourceRegionalLargeBlockCutoffScale M depth * Q := by
  unfold cmp99SourceRegionalLargeBlockCutoffScale
    cmp99SourceRegionalLargeBlockSide
  ac_rfl

/-- The certified generated precision range retains one inverse factor of
the source large-block parameter after division by the cutoff spacing. -/
theorem cmp99SourceGenerated_precisionRange_div_largeBlockCutoffScale
    (M depth : ℕ) [NeZero M] :
    (M ^ (depth + 1) : ℝ) /
        cmp99SourceRegionalLargeBlockCutoffScale M depth =
      1 / (2 * (M : ℝ)) := by
  unfold cmp99SourceRegionalLargeBlockCutoffScale
    cmp99SourceRegionalLargeBlockSide
  push_cast
  rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ]
  have hpow : (M : ℝ) ^ (depth + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have hM : (M : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne M)
  field_simp [hpow, hM] <;> ring_nf

/-- After one displacement through the certified precision range, the
literal cutoff slope still carries the source `M⁻¹` gain. -/
theorem cmp99SourceRegionalLargeBlockSlope_mul_precisionRange
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) [NeZero M] :
    ((8 * P.derivBound) /
        cmp99SourceRegionalLargeBlockCutoffScale M depth) *
      (M ^ (depth + 1) : ℝ) =
        (4 * P.derivBound) / (M : ℝ) := by
  unfold cmp99SourceRegionalLargeBlockCutoffScale
    cmp99SourceRegionalLargeBlockSide
  push_cast
  rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ]
  have hpow : (M : ℝ) ^ (depth + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have hM : (M : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne M)
  field_simp [hpow, hM] <;> ring_nf

/-- Literal source `M^-1` slope of the regional partition value field. -/
theorem norm_cmp99SourceRegionalLargeBlockSquarePartition_value_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (cell : FinBox 4 Q)
    (x y : FinBox 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))) :
    ‖(cmp99SourceRegionalLargeBlockSquarePartition
          (M := M) (Q := Q) (depth := depth) P).value cell y -
        (cmp99SourceRegionalLargeBlockSquarePartition
          (M := M) (Q := Q) (depth := depth) P).value cell x‖ ≤
      ((8 * P.derivBound) /
        cmp99SourceRegionalLargeBlockCutoffScale M depth) *
        (finBoxDist x y : ℝ) := by
  let hsize :
      cmp99SourceRegionalLargeBlockSide M depth * (2 * Q) =
        cmp99SourceRegionalLargeBlockCutoffScale M depth * Q :=
    cmp99SourceRegionalLargeBlockCutoffScale_mul_Q M Q depth
  letI : NeZero (cmp99SourceRegionalLargeBlockCutoffScale M depth) :=
    ⟨Nat.ne_of_gt (cmp99SourceRegionalLargeBlockCutoffScale_pos M depth)⟩
  let x' : FinBox 4
      (cmp99SourceRegionalLargeBlockCutoffScale M depth * Q) := hsize ▸ x
  let y' : FinBox 4
      (cmp99SourceRegionalLargeBlockCutoffScale M depth * Q) := hsize ▸ y
  have hxval (i : Fin 4) : (x' i).val = (x i).val := by
    exact finBox_cast_apply_val hsize x i
  have hyval (i : Fin 4) : (y' i).val = (y i).val := by
    exact finBox_cast_apply_val hsize y i
  have hdist : finBoxDist x' y' = finBoxDist x y := by
    exact finBoxDist_cast_size hsize x y
  have hxcoord :
      cmp99SourceRegionalLargeBlockCoordinate M depth
          (fun i => (x i).val) =
        fun i => (x' i).val +
          (1 / 2 -
            (cmp99SourceRegionalLargeBlockCutoffScale M depth : ℝ) / 2) := by
    funext i
    rw [hxval i]
    unfold cmp99SourceRegionalLargeBlockCoordinate
    ring
  have hycoord :
      cmp99SourceRegionalLargeBlockCoordinate M depth
          (fun i => (y i).val) =
        fun i => (y' i).val +
          (1 / 2 -
            (cmp99SourceRegionalLargeBlockCutoffScale M depth : ℝ) / 2) := by
    funext i
    rw [hyval i]
    unfold cmp99SourceRegionalLargeBlockCoordinate
    ring
  have h := norm_cmp95RescaledPeriodicTensorCutoff_finBox_sub_le
    P (cmp99SourceRegionalLargeBlockCutoffScale M depth) Q cell
      (fun _ => 1 / 2 -
        (cmp99SourceRegionalLargeBlockCutoffScale M depth : ℝ) / 2)
      x' y'
  change ‖cmp95RescaledPeriodicTensorCutoff P Q
        (cmp99SourceRegionalLargeBlockCutoffScale M depth) cell
          (cmp99SourceRegionalLargeBlockCoordinate M depth
            fun i => (y i).val) -
      cmp95RescaledPeriodicTensorCutoff P Q
        (cmp99SourceRegionalLargeBlockCutoffScale M depth) cell
          (cmp99SourceRegionalLargeBlockCoordinate M depth
            fun i => (x i).val)‖ ≤ _
  rw [hycoord, hxcoord]
  simpa [hdist] using h

end

end YangMills.RG

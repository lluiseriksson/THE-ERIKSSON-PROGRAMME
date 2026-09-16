/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCovariantLaplacianCutoffIdentity
import YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition
import YangMills.RG.PhysicalShellLocalityDiv

/-!
# The cutoff-Laplacian species in CMP96 (2.40)

CMP96 (2.40), printed p. 230, bounds the second displayed species by applying
the localized Green value estimate (2.43) to the scalar discrete Laplacian of
the same square-partition cutoff.  No new profile constant is required: that
discrete Laplacian is the sum of the two incident first differences in each
of four directions.  The already sealed slope therefore gives an explicit
inverse-`K` factor after multiplication by the generated range, before any
cell or layer sum.

This file proves only that cutoff-side statement and identifies its scalar
coefficient with the literal `cmp99CutoffLaplacianCorrection` at the rescaled
unit lattice spacing.  It does not supply the regional Green estimate (2.43),
combine the three species, prove (2.44)/(3.89), or attain `norm R' < 1`.

Cold GitHub Actions run `31047332477` verified exact source checkpoint
`972e8d115517c6f1f9bea97ec348bd0e31e1368d` without restoring the project
`.lake/build` cache.  The focal built 8,517 jobs and the six-declaration audit
used exactly `[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroSourceSeparatedLargeBlockSide
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth) :=
  ⟨by
    unfold cmp99SourceSeparatedLargeBlockSide
    exact (Nat.mul_pos (NeZero.pos K)
      (pow_pos (NeZero.pos L) (depth + 1))).ne'⟩

private instance instNeZeroSourceSeparatedAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- The one-step cutoff budget on the separated physical partition. -/
noncomputable def cmp96SourceSeparatedCutoffDifferenceBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) : ℝ :=
  (8 * P.derivBound) /
    cmp99SourceSeparatedLargeBlockCutoffScale L K depth

theorem cmp96SourceSeparatedCutoffDifferenceBudget_nonneg
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) :
    0 ≤ cmp96SourceSeparatedCutoffDifferenceBudget P L K depth := by
  unfold cmp96SourceSeparatedCutoffDifferenceBudget
  exact div_nonneg
    (mul_nonneg (by norm_num) P.derivBound_nonneg) (Nat.cast_nonneg _)

/-- One positive incident difference has the source-separated inverse-scale
bound. -/
theorem norm_cmp96SourceSeparatedCutoff_sub_shift_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (i : Fin 4) :
    ‖(cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x -
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell
            (x.shift i)‖ ≤
      cmp96SourceSeparatedCutoffDifferenceBudget P L K depth := by
  let A := cmp96SourceSeparatedCutoffDifferenceBudget P L K depth
  have hA : 0 ≤ A :=
    cmp96SourceSeparatedCutoffDifferenceBudget_nonneg P L K depth
  have h := norm_cmp99SourceSeparatedLargeBlockSquarePartition_value_sub_le
    (L := L) (K := K) (Q := Q) (depth := depth) P cell x (x.shift i)
  change ‖_ - _‖ ≤ A
  calc
    ‖_ - _‖ = ‖(cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell
            (x.shift i) -
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x‖ :=
      norm_sub_rev _ _
    _ ≤ A * (finBoxDist x (x.shift i) : ℝ) := h
    _ ≤ A * 1 := by
      gcongr
      exact_mod_cast finBoxDist_shift_le x i
    _ = A := mul_one A

/-- One negative incident difference has the same source-separated bound. -/
theorem norm_cmp96SourceSeparatedCutoff_sub_shiftBack_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (i : Fin 4) :
    ‖(cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x -
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell
            (x.shiftBack i)‖ ≤
      cmp96SourceSeparatedCutoffDifferenceBudget P L K depth := by
  let A := cmp96SourceSeparatedCutoffDifferenceBudget P L K depth
  have hA : 0 ≤ A :=
    cmp96SourceSeparatedCutoffDifferenceBudget_nonneg P L K depth
  have h := norm_cmp99SourceSeparatedLargeBlockSquarePartition_value_sub_le
    (L := L) (K := K) (Q := Q) (depth := depth) P cell x (x.shiftBack i)
  change ‖_ - _‖ ≤ A
  calc
    ‖_ - _‖ = ‖(cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell
            (x.shiftBack i) -
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x‖ :=
      norm_sub_rev _ _
    _ ≤ A * (finBoxDist x (x.shiftBack i) : ℝ) := h
    _ ≤ A * 1 := by
      gcongr
      exact_mod_cast finBoxDist_shiftBack_le x i
    _ = A := mul_one A

/-- Scalar coefficient of the cutoff-Laplacian species in (2.40)/(3.88). -/
noncomputable def cmp96SourceSeparatedCutoffLaplacianCoefficient
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) : ℝ :=
  ∑ i : Fin 4,
    (((cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x -
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell
            (x.shift i)) +
      ((cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x -
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell
            (x.shiftBack i)))

/-- The four-dimensional discrete Laplacian pays eight copies of the one-step
budget and no cell-count or Green/coercivity factor. -/
theorem norm_cmp96SourceSeparatedCutoffLaplacianCoefficient_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ‖cmp96SourceSeparatedCutoffLaplacianCoefficient
        (L := L) (K := K) P depth cell x‖ ≤
      8 * cmp96SourceSeparatedCutoffDifferenceBudget P L K depth := by
  unfold cmp96SourceSeparatedCutoffLaplacianCoefficient
  calc
    ‖∑ i : Fin 4, _‖ ≤ ∑ i : Fin 4, ‖_‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4,
        (cmp96SourceSeparatedCutoffDifferenceBudget P L K depth +
          cmp96SourceSeparatedCutoffDifferenceBudget P L K depth) := by
      gcongr with i
      exact (norm_add_le _ _).trans (add_le_add
        (norm_cmp96SourceSeparatedCutoff_sub_shift_le
          (L := L) (K := K) P depth cell x i)
        (norm_cmp96SourceSeparatedCutoff_sub_shiftBack_le
          (L := L) (K := K) P depth cell x i))
    _ = 8 * cmp96SourceSeparatedCutoffDifferenceBudget P L K depth := by
      rw [Fin.sum_univ_four]
      ring

/-- At rescaled unit spacing, the literal scalar correction in (3.88) is
exactly the discrete coefficient above acting on the field value. -/
theorem cmp99CutoffLaplacianCorrection_one_eq_cmp96SourceSeparatedCoefficient
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99CutoffLaplacianCorrection (Nc := Nc) 1
        (fun y => (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell y)
        phi x =
      cmp96SourceSeparatedCutoffLaplacianCoefficient
        (L := L) (K := K) P depth cell x • phi x := by
  simp only [cmp99CutoffLaplacianCorrection, inv_one, one_smul]
  rw [← Finset.sum_smul]
  rfl

/-- The inverse-`K` factor is present before any sum over cells: multiplying
the cutoff-Laplacian coefficient budget by the generated range cancels the
RG scale and leaves `32 * derivBound / K`. -/
theorem cmp96SourceSeparatedCutoffLaplacianBudget_mul_generatedRange
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    (8 * cmp96SourceSeparatedCutoffDifferenceBudget P L K depth) *
        (L ^ (depth + 1) : ℝ) =
      (32 * P.derivBound) / (K : ℝ) := by
  unfold cmp96SourceSeparatedCutoffDifferenceBudget
  rw [show
      (8 * ((8 * P.derivBound) /
          (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ))) *
          (L ^ (depth + 1) : ℝ) =
        8 * (((8 * P.derivBound) /
          (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ)) *
            (L ^ (depth + 1) : ℝ)) by ring]
  rw [cmp99SourceSeparatedLargeBlockSlope_mul_precisionRange P L K depth]
  ring

end

end YangMills.RG

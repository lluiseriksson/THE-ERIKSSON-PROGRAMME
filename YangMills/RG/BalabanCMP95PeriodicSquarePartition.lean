/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePartitionCutoffs
import YangMills.RG.BalabanCMP95SourceSmoothPartitionProfile
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Periodic square partition induced by CMP95 (1.118)

The source profile is normalized on the line by

`sum_{n : Z} h(t-n)^2 = 1`.

On a periodic lattice with `Q` source cells, the contribution assigned to a
cell is the sum over all integer translates in that residue class modulo
`Q`.  Regrouping the absolutely summable nonnegative series gives an exact
finite square partition.  This is the source-faithful object needed by the
commutator `[G',(h')^2]`: no square root or synthetic normalization is used.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The squared cutoff weight of one periodic residue class. -/
def cmp95PeriodicSquareWeight
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) : ℝ :=
  ∑' k : ℤ, P.value
    (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2

/-- The source normalization is genuinely summable, since a nonsummable
real `tsum` would be zero whereas (1.118) says it is one. -/
theorem summable_cmp95SourceSquareTranslate
    (P : CMP95SourceSmoothPartitionProfile) (t : ℝ) :
    Summable (fun n : ℤ => P.value (t - (n : ℝ)) ^ 2) := by
  by_contra h
  have hz := tsum_eq_zero_of_not_summable h
  rw [P.square_tsum t] at hz
  norm_num at hz

/-- Exact finite periodic square partition obtained by regrouping the
integer translates into residue classes modulo `Q`. -/
theorem sum_cmp95PeriodicSquareWeight
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q] (t : ℝ) :
    ∑ cell : Fin Q, cmp95PeriodicSquareWeight P Q cell t = 1 := by
  let f : ℤ → ℝ := fun n => P.value (t - (n : ℝ)) ^ 2
  let e : ℤ ≃ Fin Q × ℤ :=
    (Int.divModEquiv Q).trans (Equiv.prodComm ℤ (Fin Q))
  have hf : Summable f := summable_cmp95SourceSquareTranslate P t
  rw [← P.square_tsum t]
  change (∑ cell : Fin Q, ∑' k : ℤ,
      f (k * (Q : ℤ) + (cell.val : ℤ))) = ∑' n : ℤ, f n
  rw [← e.symm.tsum_eq f, Summable.tsum_prod, tsum_fintype]
  · rfl
  · exact hf.comp_injective e.symm.injective

/-- Every residue-class weight is nonnegative. -/
theorem cmp95PeriodicSquareWeight_nonneg
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    0 ≤ cmp95PeriodicSquareWeight P Q cell t := by
  unfold cmp95PeriodicSquareWeight
  exact tsum_nonneg fun _ => sq_nonneg _

/-- Four-dimensional tensor product of the periodic residue-class weights. -/
def cmp95PeriodicTensorSquareWeight
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin 4 → Fin Q) (x : Fin 4 → ℝ) : ℝ :=
  ∏ i, cmp95PeriodicSquareWeight P Q (cell i) (x i)

/-- Tensor weights remain nonnegative. -/
theorem cmp95PeriodicTensorSquareWeight_nonneg
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin 4 → Fin Q) (x : Fin 4 → ℝ) :
    0 ≤ cmp95PeriodicTensorSquareWeight P Q cell x := by
  unfold cmp95PeriodicTensorSquareWeight
  exact Finset.prod_nonneg fun i _ =>
    cmp95PeriodicSquareWeight_nonneg P Q (cell i) (x i)

/-- Exact finite square partition on the four-dimensional periodic cell
lattice.  The proof is the tensor product of the one-dimensional residue-
class regroupings. -/
theorem sum_cmp95PeriodicTensorSquareWeight
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (x : Fin 4 → ℝ) :
    ∑ cell : Fin 4 → Fin Q,
      cmp95PeriodicTensorSquareWeight P Q cell x = 1 := by
  unfold cmp95PeriodicTensorSquareWeight
  rw [← Fintype.prod_sum (fun i (cell : Fin Q) =>
    cmp95PeriodicSquareWeight P Q cell (x i))]
  simp [sum_cmp95PeriodicSquareWeight]

/-- Nonnegative square root representing the periodic tensor cutoff itself. -/
def cmp95PeriodicTensorCutoff
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin 4 → Fin Q) (x : Fin 4 → ℝ) : ℝ :=
  Real.sqrt (cmp95PeriodicTensorSquareWeight P Q cell x)

/-- Squaring the periodic cutoff recovers its source-derived residue-class
weight exactly. -/
theorem cmp95PeriodicTensorCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin 4 → Fin Q) (x : Fin 4 → ℝ) :
    cmp95PeriodicTensorCutoff P Q cell x ^ 2 =
      cmp95PeriodicTensorSquareWeight P Q cell x := by
  exact Real.sq_sqrt (cmp95PeriodicTensorSquareWeight_nonneg P Q cell x)

/-- Concrete periodic source square partition on the CMP99 large-block
torus.  A source cell has side two large blocks, hence the coordinate
`block.val / 2` in cell units. -/
noncomputable def cmp95SourcePeriodicCoarseSquarePartition
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q] :
    CMP99SourceSquarePartition Q where
  value cell block := cmp95PeriodicTensorCutoff P Q cell
    (fun i => ((block i).val : ℝ) / 2)
  square_sum block := by
    simp_rw [cmp95PeriodicTensorCutoff_sq]
    exact sum_cmp95PeriodicTensorSquareWeight P Q
      (fun i => ((block i).val : ℝ) / 2)

end

end YangMills.RG

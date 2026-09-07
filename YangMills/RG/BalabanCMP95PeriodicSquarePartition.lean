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

/-- Translating the physical coordinate by one complete source period does
not change a residue-class weight.  This exact identity is the mechanism
that removes the apparent coordinate jump at the periodic boundary before
any Lipschitz estimate is applied. -/
theorem cmp95PeriodicSquareWeight_add_period
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    cmp95PeriodicSquareWeight P Q cell (t + Q) =
      cmp95PeriodicSquareWeight P Q cell t := by
  unfold cmp95PeriodicSquareWeight
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  apply tsum_congr
  intro k
  congr 2
  simp only [Equiv.coe_addRight]
  push_cast
  ring

/-- Exact support condition for one periodized coordinate.  It records that
one integer representative of the residue class lies in the source support
interval `(-2/3, 2/3)` from CMP95 (1.118). -/
def cmp95PeriodicCoordinateSupport
    (Q : ℕ) (cell : Fin Q) (t : ℝ) : Prop :=
  ∃ k : ℤ,
    t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ) ∈
      Set.Ioo (-(2 / 3 : ℝ)) (2 / 3)

/-- Compact support survives periodization: if no representative of the
residue class reaches the source interval, its whole square weight is zero. -/
theorem cmp95PeriodicSquareWeight_eq_zero_of_not_support
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ)
    (houtside : ¬ cmp95PeriodicCoordinateSupport Q cell t) :
    cmp95PeriodicSquareWeight P Q cell t = 0 := by
  unfold cmp95PeriodicSquareWeight
  calc
    (∑' k : ℤ, P.value
        (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2) =
        ∑' _k : ℤ, 0 := by
      apply tsum_congr
      intro k
      have hvalue : P.value
          (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) = 0 := by
        by_contra hne
        have hmem :
            t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ) ∈
              Function.support P.value :=
          Function.mem_support.mpr hne
        exact houtside ⟨k, P.support_subset hmem⟩
      rw [hvalue]
      norm_num
    _ = 0 := tsum_zero

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

/-- Tensor support of the periodized four-dimensional source cutoff. -/
def cmp95PeriodicTensorSupport
    (Q : ℕ) (cell : Fin 4 → Fin Q) (x : Fin 4 → ℝ) : Prop :=
  ∀ i, cmp95PeriodicCoordinateSupport Q (cell i) (x i)

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

/-- The literal periodized tensor cutoff vanishes outside its tensor support. -/
theorem cmp95PeriodicTensorCutoff_eq_zero_of_not_support
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin 4 → Fin Q) (x : Fin 4 → ℝ)
    (houtside : ¬ cmp95PeriodicTensorSupport Q cell x) :
  cmp95PeriodicTensorCutoff P Q cell x = 0 := by
  classical
  unfold cmp95PeriodicTensorSupport at houtside
  simp only [not_forall] at houtside
  obtain ⟨i, hi⟩ := houtside
  unfold cmp95PeriodicTensorCutoff
  have hsquare : cmp95PeriodicTensorSquareWeight P Q cell x = 0 := by
    unfold cmp95PeriodicTensorSquareWeight
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (cmp95PeriodicSquareWeight_eq_zero_of_not_support P Q (cell i) (x i) hi)
  rw [hsquare, Real.sqrt_zero]

/-- Squaring the periodic cutoff recovers its source-derived residue-class
weight exactly. -/
theorem cmp95PeriodicTensorCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin 4 → Fin Q) (x : Fin 4 → ℝ) :
    cmp95PeriodicTensorCutoff P Q cell x ^ 2 =
      cmp95PeriodicTensorSquareWeight P Q cell x := by
  exact Real.sq_sqrt (cmp95PeriodicTensorSquareWeight_nonneg P Q cell x)

/-- Concrete periodic source square partition on the CMP99 large-block
torus.  A source cell has side two large blocks.  Its geometric centre is
halfway between the two integer block coordinates, hence the source
coordinate is `block.val / 2 - 1 / 4` in cell units.  This quarter-cell
shift is essential: together with the printed support `(-2/3,2/3)` it puts
the cutoff support inside the literal two-block source cell `Pi`. -/
noncomputable def cmp95SourcePeriodicCoarseSquarePartition
  (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q] :
    CMP99SourceSquarePartition Q where
  value cell block := cmp95PeriodicTensorCutoff P Q cell
    (fun i => ((block i).val : ℝ) / 2 - 1 / 4)
  square_sum block := by
    simp_rw [cmp95PeriodicTensorCutoff_sq]
    exact sum_cmp95PeriodicTensorSquareWeight P Q
      (fun i => ((block i).val : ℝ) / 2 - 1 / 4)

/-- Source support predicate for a coarse large block.  The coordinate
`block.val / 2 - 1 / 4` is exactly the centred cell-unit convention used by
the periodic partition above. -/
def cmp95SourcePeriodicCoarseCellSupport
    (Q : ℕ) (cell : FinBox 4 Q) (block : FinBox 4 (2 * Q)) : Prop :=
  cmp95PeriodicTensorSupport Q cell
    (fun i => ((block i).val : ℝ) / 2 - 1 / 4)

/-- The generated CMP95 cutoff is exactly zero on every coarse block outside
the source cell support. -/
theorem cmp95SourcePeriodicCoarseSquarePartition_value_eq_zero_of_not_support
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : FinBox 4 Q) (block : FinBox 4 (2 * Q))
    (houtside : ¬ cmp95SourcePeriodicCoarseCellSupport Q cell block) :
    (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block = 0 := by
  exact cmp95PeriodicTensorCutoff_eq_zero_of_not_support P Q cell
    (fun i => ((block i).val : ℝ) / 2 - 1 / 4) houtside

end

end YangMills.RG

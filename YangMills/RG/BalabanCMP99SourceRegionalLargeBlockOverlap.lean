/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicActiveCellOverlap
import YangMills.RG.BalabanCMP99SourceRegionalLargeBlockPartition

/-!
# Pointwise overlap of the CMP99 source large-block partition

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

The large-block source cutoffs use the same one-dimensional CMP95 profile as
the auxiliary terminal-scale partition.  Hence their pointwise overlap is
derived from the same two-residue active window: there is no second overlap
constant and no overlap hypothesis supplied by the caller.
-/

namespace YangMills.RG

noncomputable section

/-- Source large-block cells whose literal cutoff is nonzero at a fixed site. -/
def cmp99SourceRegionalLargeBlockActiveCells
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))) :
    Finset (FinBox 4 Q) :=
  Finset.univ.filter fun cell =>
    (cmp99SourceRegionalLargeBlockSquarePartition
      (M := M) (Q := Q) (depth := depth) P).value cell x ≠ 0

/-- Every active source large-block cell belongs to the product of the four
two-residue windows derived from the same CMP95 support interval. -/
theorem cmp99SourceRegionalLargeBlockActiveCells_subset
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))) :
    cmp99SourceRegionalLargeBlockActiveCells P M Q depth x ⊆
      cmp95RescaledPeriodicTensorActiveCellWindow Q
        (cmp99SourceRegionalLargeBlockCutoffScale M depth)
        (cmp99SourceRegionalLargeBlockCoordinate M depth
          fun i => (x i).val) := by
  classical
  intro cell hcell
  rw [cmp99SourceRegionalLargeBlockActiveCells, Finset.mem_filter] at hcell
  apply mem_cmp95RescaledPeriodicTensorActiveCellWindow_of_cutoff_ne_zero P Q
  simpa [cmp99SourceRegionalLargeBlockSquarePartition,
    cmp99SourceRegionalLargeBlockCutoff] using hcell.2

/-- Literal pointwise overlap of the physical source large-block partition.
The bound is the same `2^4 = 16` obtained from its defining profile. -/
theorem card_cmp99SourceRegionalLargeBlockActiveCells_le_sixteen
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))) :
    (cmp99SourceRegionalLargeBlockActiveCells P M Q depth x).card ≤ 16 := by
  calc
    (cmp99SourceRegionalLargeBlockActiveCells P M Q depth x).card ≤
        (cmp95RescaledPeriodicTensorActiveCellWindow Q
          (cmp99SourceRegionalLargeBlockCutoffScale M depth)
          (cmp99SourceRegionalLargeBlockCoordinate M depth
            fun i => (x i).val)).card :=
      Finset.card_le_card
        (cmp99SourceRegionalLargeBlockActiveCells_subset P M Q depth x)
    _ ≤ 16 :=
      card_cmp95RescaledPeriodicTensorActiveCellWindow_le_sixteen _ _ _

end

end YangMills.RG

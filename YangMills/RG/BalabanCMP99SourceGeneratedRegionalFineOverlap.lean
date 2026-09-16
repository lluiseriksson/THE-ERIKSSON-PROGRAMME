/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicActiveCellOverlap
import YangMills.RG.BalabanCMP99SourceGeneratedRegionalFinePartition

/-!
# Pointwise overlap of the generated regional CMP99 partition

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

This specializes the transposed CMP95 support geometry to the exact regional
partition used by the Dirichlet Green parametrix.  The bound `16 = 2^4` is a
theorem about that partition, not a second overlap hypothesis.
-/

namespace YangMills.RG

noncomputable section

/-- Source cells whose literal fine cutoff is nonzero at one factored fine
site. -/
def cmp99SourceGeneratedRegionalFineActiveCells
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (x : FinBox 4 (M ^ (depth + 1) * (2 * Q))) : Finset (FinBox 4 Q) :=
  Finset.univ.filter fun cell =>
    (cmp99SourceGeneratedRegionalFineSquarePartition
      (M := M) (Q := Q) (depth := depth) P).value cell x ≠ 0

/-- Every generated active source cell belongs to the product of the four
two-residue windows obtained from the same CMP95 support interval. -/
theorem cmp99SourceGeneratedRegionalFineActiveCells_subset
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (x : FinBox 4 (M ^ (depth + 1) * (2 * Q))) :
    cmp99SourceGeneratedRegionalFineActiveCells P M Q depth x ⊆
      cmp95PeriodicTensorActiveCellWindow Q
        (cmp99SourceGeneratedFineCellCoordinate M depth fun i =>
          ((cmp99RegionalFactoredToGeneratedFineSite
            (M := M) (Q := Q) (depth := depth) x i).val : ℝ)) := by
  classical
  intro cell hcell
  rw [cmp99SourceGeneratedRegionalFineActiveCells, Finset.mem_filter] at hcell
  apply mem_cmp95PeriodicTensorActiveCellWindow_of_cutoff_ne_zero P Q
  simpa [cmp99SourceGeneratedRegionalFineSquarePartition,
    cmp99SourceGeneratedFineCellCutoff] using hcell.2

/-- Literal pointwise overlap bound for the physical regional partition.
It is independent of `Q`, the volume, and the regional carrier. -/
theorem card_cmp99SourceGeneratedRegionalFineActiveCells_le_sixteen
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (x : FinBox 4 (M ^ (depth + 1) * (2 * Q))) :
    (cmp99SourceGeneratedRegionalFineActiveCells P M Q depth x).card ≤ 16 := by
  calc
    (cmp99SourceGeneratedRegionalFineActiveCells P M Q depth x).card ≤
        (cmp95PeriodicTensorActiveCellWindow Q
          (cmp99SourceGeneratedFineCellCoordinate M depth fun i =>
            ((cmp99RegionalFactoredToGeneratedFineSite
              (M := M) (Q := Q) (depth := depth) x i).val : ℝ))).card :=
      Finset.card_le_card
        (cmp99SourceGeneratedRegionalFineActiveCells_subset P M Q depth x)
    _ ≤ 16 := card_cmp95PeriodicTensorActiveCellWindow_le_sixteen _ _

end

end YangMills.RG

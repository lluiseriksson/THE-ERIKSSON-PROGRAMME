/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicCutoffSlope
import YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann

/-!
# The CMP99 regional partition at the source large-block scale

CMP99 printed p. 408 separates the terminal operator scale `L^(j eta)` from
the large-block scale `M * L^(j eta)`.  This module records the algebraically
valid diagonal specialization in which the repository RG ratio and the
source's independent large-block parameter are both named `M`; its two scales
therefore have the shapes `M^(depth+1)` and `M^(depth+2)`.  A partition cell
contains two large blocks, so its cutoff spacing is `2 * M^(depth+2)`.

The diagonal specialization is not the source's full sufficiently-large-`M`
freedom.  It remains useful as an exact comparison object, but physical
smallness must keep the RG ratio and the independent large-block parameter
separate.
-/

namespace YangMills.RG

noncomputable section

variable {M Q depth : ℕ} [NeZero M] [NeZero Q]

/-- Side of one source large block on the generated fine lattice. -/
def cmp99SourceRegionalLargeBlockSide (M depth : ℕ) : ℕ :=
  M ^ (depth + 2)

/-- Translation spacing of the disjoint two-large-block source cells. -/
def cmp99SourceRegionalLargeBlockCutoffScale (M depth : ℕ) : ℕ :=
  2 * cmp99SourceRegionalLargeBlockSide M depth

theorem cmp99SourceRegionalLargeBlockCutoffScale_pos
    (M depth : ℕ) [NeZero M] :
    0 < cmp99SourceRegionalLargeBlockCutoffScale M depth := by
  unfold cmp99SourceRegionalLargeBlockCutoffScale
    cmp99SourceRegionalLargeBlockSide
  exact Nat.mul_pos (by omega) (pow_pos (NeZero.pos M) (depth + 2))

/-- The source large-block carrier is the generated fine lattice obtained by
starting the Section-C tower on `2 * (M * Q)` coarse sites.  This equality is
the ambient-carrier dictionary needed to place the generated precision and
the large-block partition on the same torus. -/
theorem cmp99RegionalLatticeSize_sourceLargeBlockCarrier
    (M Q depth : ℕ) :
    cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1) =
      cmp99SourceRegionalLargeBlockSide M depth * (2 * Q) := by
  rw [cmp99RegionalLatticeSize_eq_pow_mul]
  unfold cmp99SourceRegionalLargeBlockSide
  rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ]
  ring

/-- Physical coordinate centered on one two-large-block source cell. -/
def cmp99SourceRegionalLargeBlockCoordinate
    (M depth : ℕ)
    (x : Fin 4 → ℕ) : Fin 4 → ℝ :=
  fun i => (x i : ℝ) + 1 / 2 -
    (cmp99SourceRegionalLargeBlockCutoffScale M depth : ℝ) / 2

/-- Literal nonnegative source cutoff on the large-block regional torus. -/
def cmp99SourceRegionalLargeBlockCutoff
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q)
    (x : FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))) : ℝ :=
  cmp95RescaledPeriodicTensorCutoff P Q
    (cmp99SourceRegionalLargeBlockCutoffScale M depth) cell
    (cmp99SourceRegionalLargeBlockCoordinate M depth fun i => (x i).val)

/-- The source-scale cutoffs form an exact square partition at every site. -/
theorem sum_cmp99SourceRegionalLargeBlockCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile)
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (x : FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))) :
    ∑ cell : FinBox 4 Q,
      cmp99SourceRegionalLargeBlockCutoff P M Q depth cell x ^ 2 = 1 := by
  exact sum_cmp95RescaledPeriodicTensorCutoff_sq P Q
    (cmp99SourceRegionalLargeBlockCutoffScale M depth)
    (cmp99SourceRegionalLargeBlockCoordinate M depth fun i => (x i).val)

/-- The literal source-scale partition consumed by the regional Dirichlet
Green algebra.  Its ambient side is `2 Q` large blocks. -/
noncomputable def cmp99SourceRegionalLargeBlockSquarePartition
    (P : CMP95SourceSmoothPartitionProfile) :
    CMP99RegionalFineSquarePartition
      (cmp99SourceRegionalLargeBlockSide M depth) Q where
  value cell x := cmp99SourceRegionalLargeBlockCutoff P M Q depth cell x
  square_sum x := sum_cmp99SourceRegionalLargeBlockCutoff_sq P M Q depth x

end

end YangMills.RG

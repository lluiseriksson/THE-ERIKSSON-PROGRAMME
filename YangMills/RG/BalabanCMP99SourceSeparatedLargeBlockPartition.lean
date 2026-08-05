/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicActiveCellOverlap
import YangMills.RG.BalabanCMP95PeriodicCutoffSlope
import YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann
import YangMills.RG.BalabanCMP99SourceRegionalLargeBlockPartition

/-!
# PRE-VALIDATION: source-separated CMP99 large-block partition

The source below is present, but its `.olean` has not yet been materialized
and its results have not yet been verified by the Lean compiler.

CMP99 printed p. 408 uses two independent scales: the RG block ratio `L`,
which fixes the terminal operator range `L^(depth+1)`, and a sufficiently
large regional factor `K`, which fixes the large-block side
`K * L^(depth+1)`.  Here `K` is the Lean name for the source's independent
large-block parameter (also printed as `M`); it is renamed so it cannot be
confused with the repository's existing RG-ratio argument.  The earlier
generated specialization set `K = L`; that
identification is algebraically valid but destroys the intended smallness
because its Poincare cost then grows with the same parameter that should make
the defect small.

This module constructs the exact periodic square partition with `L` and `K`
separate.  It proves the ambient-carrier dictionary, the square partition,
the source overlap `16`, and the literal

`slope * generatedRange = 4 * derivBound / K`.

No regional Green estimate or contraction is claimed here.
-/

namespace YangMills.RG

noncomputable section

variable {L K Q depth : ℕ} [NeZero L] [NeZero K] [NeZero Q]

/-- Side of one source large block when the RG ratio and large-block factor
are kept independent. -/
def cmp99SourceSeparatedLargeBlockSide
    (L K depth : ℕ) : ℕ :=
  K * L ^ (depth + 1)

/-- Translation spacing of the disjoint two-large-block cells. -/
def cmp99SourceSeparatedLargeBlockCutoffScale
    (L K depth : ℕ) : ℕ :=
  2 * cmp99SourceSeparatedLargeBlockSide L K depth

/-- The earlier generated large-block side is exactly the diagonal
specialization `K = L`. -/
theorem cmp99SourceSeparatedLargeBlockSide_self
    (L depth : ℕ) :
    cmp99SourceSeparatedLargeBlockSide L L depth =
      cmp99SourceRegionalLargeBlockSide L depth := by
  unfold cmp99SourceSeparatedLargeBlockSide
    cmp99SourceRegionalLargeBlockSide
  rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ]
  ac_rfl

/-- The same diagonal specialization holds for the cutoff spacing. -/
theorem cmp99SourceSeparatedLargeBlockCutoffScale_self
    (L depth : ℕ) :
    cmp99SourceSeparatedLargeBlockCutoffScale L L depth =
      cmp99SourceRegionalLargeBlockCutoffScale L depth := by
  unfold cmp99SourceSeparatedLargeBlockCutoffScale
    cmp99SourceRegionalLargeBlockCutoffScale
  rw [cmp99SourceSeparatedLargeBlockSide_self]

theorem cmp99SourceSeparatedLargeBlockCutoffScale_pos
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    0 < cmp99SourceSeparatedLargeBlockCutoffScale L K depth := by
  unfold cmp99SourceSeparatedLargeBlockCutoffScale
    cmp99SourceSeparatedLargeBlockSide
  exact Nat.mul_pos (by omega)
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))

/-- The generated precision with RG ratio `L`, based on `2 * (K * Q)` coarse
sites, lives on exactly the separated large-block torus. -/
theorem cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier
    (L K Q depth : ℕ) :
    cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1) =
      cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q) := by
  rw [cmp99RegionalLatticeSize_eq_pow_mul]
  unfold cmp99SourceSeparatedLargeBlockSide
  ring

/-- Physical coordinate centered on one separated two-large-block cell. -/
def cmp99SourceSeparatedLargeBlockCoordinate
    (L K depth : ℕ) (x : Fin 4 → ℕ) : Fin 4 → ℝ :=
  fun i => (x i : ℝ) + 1 / 2 -
    (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ) / 2

/-- Literal nonnegative source cutoff on the separated large-block torus. -/
def cmp99SourceSeparatedLargeBlockCutoff
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) : ℝ :=
  cmp95RescaledPeriodicTensorCutoff P Q
    (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) cell
    (cmp99SourceSeparatedLargeBlockCoordinate L K depth fun i => (x i).val)

/-- The separated source cutoffs form an exact square partition. -/
theorem sum_cmp99SourceSeparatedLargeBlockCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ∑ cell : FinBox 4 Q,
      cmp99SourceSeparatedLargeBlockCutoff P L K Q depth cell x ^ 2 = 1 := by
  exact sum_cmp95RescaledPeriodicTensorCutoff_sq P Q
    (cmp99SourceSeparatedLargeBlockCutoffScale L K depth)
    (cmp99SourceSeparatedLargeBlockCoordinate L K depth fun i => (x i).val)

/-- The separated partition consumed by the regional Dirichlet Green
algebra. -/
noncomputable def cmp99SourceSeparatedLargeBlockSquarePartition
    (P : CMP95SourceSmoothPartitionProfile) :
    CMP99RegionalFineSquarePartition
      (cmp99SourceSeparatedLargeBlockSide L K depth) Q where
  value cell x :=
    cmp99SourceSeparatedLargeBlockCutoff P L K Q depth cell x
  square_sum x :=
    sum_cmp99SourceSeparatedLargeBlockCutoff_sq P L K Q depth x

/-- The cutoff spacing tiles its ambient separated regional torus. -/
theorem cmp99SourceSeparatedLargeBlockCutoffScale_mul_Q
    (L K Q depth : ℕ) :
    cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q) =
      cmp99SourceSeparatedLargeBlockCutoffScale L K depth * Q := by
  unfold cmp99SourceSeparatedLargeBlockCutoffScale
    cmp99SourceSeparatedLargeBlockSide
  ac_rfl

/-- Dividing the generated precision range by the independent cutoff spacing
leaves `1 / (2*K)`, with no Poincare dependence on `K`. -/
theorem cmp99SourceGenerated_precisionRange_div_separatedLargeBlockCutoffScale
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    (L ^ (depth + 1) : ℝ) /
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth =
      1 / (2 * (K : ℝ)) := by
  unfold cmp99SourceSeparatedLargeBlockCutoffScale
    cmp99SourceSeparatedLargeBlockSide
  push_cast
  have hpow : (L : ℝ) ^ (depth + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne L))
  have hK : (K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne K)
  field_simp [hpow, hK] <;> ring

/-- The source slope times the generated operator range retains the literal
independent `K⁻¹` gain. -/
theorem cmp99SourceSeparatedLargeBlockSlope_mul_precisionRange
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    ((8 * P.derivBound) /
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth) *
      (L ^ (depth + 1) : ℝ) =
        (4 * P.derivBound) / (K : ℝ) := by
  unfold cmp99SourceSeparatedLargeBlockCutoffScale
    cmp99SourceSeparatedLargeBlockSide
  push_cast
  have hpow : (L : ℝ) ^ (depth + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne L))
  have hK : (K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne K)
  field_simp [hpow, hK]
  ring

/-- Literal source slope of the separated regional partition value field. -/
theorem norm_cmp99SourceSeparatedLargeBlockSquarePartition_value_sub_le
    (P : CMP95SourceSmoothPartitionProfile)
    (cell : FinBox 4 Q)
    (x y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ‖(cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell y -
        (cmp99SourceSeparatedLargeBlockSquarePartition
          (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x‖ ≤
      ((8 * P.derivBound) /
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
  have hxval (i : Fin 4) : (x' i).val = (x i).val := by
    exact finBox_cast_apply_val hsize x i
  have hyval (i : Fin 4) : (y' i).val = (y i).val := by
    exact finBox_cast_apply_val hsize y i
  have hdist : finBoxDist x' y' = finBoxDist x y := by
    exact finBoxDist_cast_size hsize x y
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
  have h := norm_cmp95RescaledPeriodicTensorCutoff_finBox_sub_le
    P (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) Q cell
      (fun _ => 1 / 2 -
        (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ) / 2)
      x' y'
  change ‖cmp95RescaledPeriodicTensorCutoff P Q
        (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) cell
          (cmp99SourceSeparatedLargeBlockCoordinate L K depth
            fun i => (y i).val) -
      cmp95RescaledPeriodicTensorCutoff P Q
        (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) cell
          (cmp99SourceSeparatedLargeBlockCoordinate L K depth
            fun i => (x i).val)‖ ≤ _
  rw [hycoord, hxcoord]
  simpa [hdist] using h

/-- Separated large-block cells whose cutoff is nonzero at a fixed site. -/
def cmp99SourceSeparatedLargeBlockActiveCells
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    Finset (FinBox 4 Q) :=
  Finset.univ.filter fun cell =>
    (cmp99SourceSeparatedLargeBlockSquarePartition
      (L := L) (K := K) (Q := Q) (depth := depth) P).value cell x ≠ 0

/-- Every active separated cell belongs to the same four two-residue windows
derived from the single CMP95 source profile. -/
theorem cmp99SourceSeparatedLargeBlockActiveCells_subset
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99SourceSeparatedLargeBlockActiveCells P L K Q depth x ⊆
      cmp95RescaledPeriodicTensorActiveCellWindow Q
        (cmp99SourceSeparatedLargeBlockCutoffScale L K depth)
        (cmp99SourceSeparatedLargeBlockCoordinate L K depth
          fun i => (x i).val) := by
  classical
  intro cell hcell
  rw [cmp99SourceSeparatedLargeBlockActiveCells, Finset.mem_filter] at hcell
  apply mem_cmp95RescaledPeriodicTensorActiveCellWindow_of_cutoff_ne_zero P Q
  simpa [cmp99SourceSeparatedLargeBlockSquarePartition,
    cmp99SourceSeparatedLargeBlockCutoff] using hcell.2

/-- The pointwise overlap remains the unique source constant `2^4 = 16`. -/
theorem card_cmp99SourceSeparatedLargeBlockActiveCells_le_sixteen
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    (cmp99SourceSeparatedLargeBlockActiveCells
      P L K Q depth x).card ≤ 16 := by
  calc
    (cmp99SourceSeparatedLargeBlockActiveCells P L K Q depth x).card ≤
        (cmp95RescaledPeriodicTensorActiveCellWindow Q
          (cmp99SourceSeparatedLargeBlockCutoffScale L K depth)
          (cmp99SourceSeparatedLargeBlockCoordinate L K depth
            fun i => (x i).val)).card :=
      Finset.card_le_card
        (cmp99SourceSeparatedLargeBlockActiveCells_subset
          P L K Q depth x)
    _ ≤ 16 :=
      card_cmp95RescaledPeriodicTensorActiveCellWindow_le_sixteen _ _ _

end

end YangMills.RG

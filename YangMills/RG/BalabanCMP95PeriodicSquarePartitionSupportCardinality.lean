/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicSquarePartition

/-!
# Cardinality of the exact CMP95 periodic cutoff support

The source profile in CMP95 (1.118) is supported in `(-2/3,2/3)`.  A CMP99
source cell contains two large blocks in each coordinate, and its centre is
halfway between their integer block coordinates.  Thus the source argument is
`block/2 - 1/4 - cell`, so a nonzero coordinate has displacement exactly `0`
or `1` from `2 * cell`, modulo the period.  Consequently the tensor cutoff is
supported inside the literal `2^4`-block source cell `Pi`.  The older `3^4`
carrier and its bound are retained below as compatible weaker corollaries.
-/

namespace YangMills.RG

open YangMills

noncomputable section

set_option maxHeartbeats 500000

/-- The three-point source carrier in each coordinate, represented without
choosing integer lifts of the periodic torus. -/
def cmp95SourcePeriodicCoarseOffsetBlock {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (offset : Fin 4 → Fin 3) : FinBox 4 (2 * Q) :=
  fun i =>
    ⟨(2 * ((cell i).val : ZMod (2 * Q)) +
        ((offset i).val : ZMod (2 * Q)) - 1).val,
      ZMod.val_lt _⟩

/-- Finite carrier of the exact periodized CMP95 cutoff. -/
noncomputable def cmp95SourcePeriodicCoarseCellCarrier {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) : Finset (FinBox 4 (2 * Q)) :=
  Finset.univ.image (cmp95SourcePeriodicCoarseOffsetBlock cell)

/-- The exact carrier has at most three choices in each of four coordinates. -/
theorem card_cmp95SourcePeriodicCoarseCellCarrier_le {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    (cmp95SourcePeriodicCoarseCellCarrier cell).card ≤ 81 := by
  calc
    (cmp95SourcePeriodicCoarseCellCarrier cell).card ≤
        (Finset.univ : Finset (Fin 4 → Fin 3)).card := Finset.card_image_le
    _ = 81 := by norm_num

/-- One supported centred coordinate differs from `2 * cell` by an integer
in `{0,1}`, modulo the period `2Q`. -/
theorem cmp95PeriodicCoordinateSupport_displacement01
    {Q : ℕ} [NeZero Q] (cell : Fin Q) (block : Fin (2 * Q))
    (hsupport : cmp95PeriodicCoordinateSupport Q cell
      (((block.val : ℕ) : ℝ) / 2 - 1 / 4)) :
    ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
      ((block.val : ℕ) : ZMod (2 * Q)) =
        2 * (cell.val : ZMod (2 * Q)) + (z : ZMod (2 * Q)) := by
  obtain ⟨k, hk⟩ := hsupport
  let z : ℤ := (block.val : ℤ) - 2 * (k * (Q : ℤ) + (cell.val : ℤ))
  have hzReal : (z : ℝ) =
      2 * ((((block.val : ℕ) : ℝ) / 2 - 1 / 4) -
        ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) + 1 / 2 := by
    dsimp [z]
    push_cast
    ring
  have hzLowerReal : (-(5 : ℝ) / 6) < (z : ℝ) := by
    rw [hzReal]
    linarith [hk.1]
  have hzUpperReal : (z : ℝ) < (11 : ℝ) / 6 := by
    rw [hzReal]
    linarith [hk.2]
  have hzLower : (0 : ℤ) ≤ z := by
    by_contra h
    have hzle : z ≤ -1 := by omega
    have hzleReal : (z : ℝ) ≤ -1 := by exact_mod_cast hzle
    linarith
  have hzUpper : z ≤ (1 : ℤ) := by
    by_contra h
    have hzge : 2 ≤ z := by omega
    have hzgeReal : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzge
    linarith
  refine ⟨z, hzLower, hzUpper, ?_⟩
  have hzDef : (block.val : ℤ) =
      2 * (k * (Q : ℤ) + (cell.val : ℤ)) + z := by
    dsimp [z]
    ring
  rw [← Int.cast_natCast block.val]
  rw [hzDef]
  push_cast
  have hperiod :
      (Q : ZMod (2 * Q)) * (2 : ZMod (2 * Q)) = 0 := by
    calc
      (Q : ZMod (2 * Q)) * (2 : ZMod (2 * Q)) =
          ((Q * 2 : ℕ) : ZMod (2 * Q)) := by norm_num
      _ = ((2 * Q : ℕ) : ZMod (2 * Q)) := by rw [Nat.mul_comm]
      _ = 0 := ZMod.natCast_self (2 * Q)
  calc
    2 * ((k : ZMod (2 * Q)) * (Q : ZMod (2 * Q)) +
          (cell.val : ZMod (2 * Q))) + (z : ZMod (2 * Q)) =
        (k : ZMod (2 * Q)) * ((Q : ZMod (2 * Q)) * 2) +
          2 * (cell.val : ZMod (2 * Q)) + (z : ZMod (2 * Q)) := by ring
    _ = 2 * (cell.val : ZMod (2 * Q)) + (z : ZMod (2 * Q)) := by
      rw [hperiod, mul_zero, zero_add]

/-- Compatibility form of the displacement theorem used by the older
three-point carrier. -/
theorem cmp95PeriodicCoordinateSupport_displacement
    {Q : ℕ} [NeZero Q] (cell : Fin Q) (block : Fin (2 * Q))
    (hsupport : cmp95PeriodicCoordinateSupport Q cell
      (((block.val : ℕ) : ℝ) / 2 - 1 / 4)) :
    ∃ z : ℤ, -1 ≤ z ∧ z ≤ 1 ∧
      ((block.val : ℕ) : ZMod (2 * Q)) =
        2 * (cell.val : ZMod (2 * Q)) + (z : ZMod (2 * Q)) := by
  obtain ⟨z, hz0, hz1, hz⟩ :=
    cmp95PeriodicCoordinateSupport_displacement01 cell block hsupport
  exact ⟨z, by omega, hz1, hz⟩

/-- Every supported coarse block is in the explicit `3^4` carrier. -/
theorem cmp95SourcePeriodicCoarseCellSupport_mem_carrier
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q)
    (block : FinBox 4 (2 * Q))
    (hsupport : cmp95SourcePeriodicCoarseCellSupport Q cell block) :
    block ∈ cmp95SourcePeriodicCoarseCellCarrier cell := by
  classical
  have hcoord : ∀ i, ∃ z : ℤ, -1 ≤ z ∧ z ≤ 1 ∧
      ((block i).val : ℕ) =
        (2 * ((cell i).val : ZMod (2 * Q)) +
          (z : ZMod (2 * Q))).val := by
    intro i
    obtain ⟨z, hzLower, hzUpper, hz⟩ :=
      cmp95PeriodicCoordinateSupport_displacement (cell i) (block i)
        (hsupport i)
    have hzval := congrArg ZMod.val hz
    rw [ZMod.val_cast_of_lt (block i).isLt] at hzval
    exact ⟨z, hzLower, hzUpper, hzval⟩
  choose z hzLower hzUpper hzEq using hcoord
  let offset : Fin 4 → Fin 3 := fun i =>
    ⟨Int.toNat (z i + 1), by
      have hzLowerI := hzLower i
      have hzUpperI := hzUpper i
      have hnonneg : 0 ≤ z i + 1 := by omega
      have hle : z i + 1 ≤ 2 := by omega
      have hcast : (Int.toNat (z i + 1) : ℤ) = z i + 1 :=
        Int.toNat_of_nonneg hnonneg
      omega⟩
  rw [cmp95SourcePeriodicCoarseCellCarrier, Finset.mem_image]
  refine ⟨offset, Finset.mem_univ _, ?_⟩
  funext i
  apply Fin.ext
  dsimp [cmp95SourcePeriodicCoarseOffsetBlock, offset]
  have hzLowerI := hzLower i
  have hzUpperI := hzUpper i
  have hnonneg : 0 ≤ z i + 1 := by omega
  have hcast : (Int.toNat (z i + 1) : ℤ) = z i + 1 :=
    Int.toNat_of_nonneg hnonneg
  rw [hzEq i]
  apply congrArg ZMod.val
  have hoffset :
      (((Int.toNat (z i + 1) : ℕ) : ZMod (2 * Q))) =
        ((z i + 1 : ℤ) : ZMod (2 * Q)) := by
    rw [← Int.cast_natCast]
    exact congrArg (fun w : ℤ => (w : ZMod (2 * Q))) hcast
  rw [hoffset]
  push_cast
  ring

/-- Source-faithful support statement needed in CMP99 (3.95): every block on
which `h_Pi` can be nonzero belongs to the literal two-block-per-coordinate
cell `Pi`. -/
theorem cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q)
    (block : FinBox 4 (2 * Q))
    (hsupport : cmp95SourcePeriodicCoarseCellSupport Q cell block) :
    block ∈ cmp99SourceBaseCell cell := by
  classical
  have hcoord : ∀ i, ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
      ((block i).val : ℕ) =
        (2 * ((cell i).val : ZMod (2 * Q)) +
          (z : ZMod (2 * Q))).val := by
    intro i
    obtain ⟨z, hz0, hz1, hz⟩ :=
      cmp95PeriodicCoordinateSupport_displacement01 (cell i) (block i)
        (hsupport i)
    have hzval := congrArg ZMod.val hz
    rw [ZMod.val_cast_of_lt (block i).isLt] at hzval
    exact ⟨z, hz0, hz1, hzval⟩
  choose z hz0 hz1 hzEq using hcoord
  let offset : Fin 4 → Fin 2 := fun i =>
    ⟨Int.toNat (z i), by
      have hcast : (Int.toNat (z i) : ℤ) = z i :=
        Int.toNat_of_nonneg (hz0 i)
      have := hz1 i
      omega⟩
  rw [← cmp99SourceTildePiLargeBlocks_zero cell,
    mem_cmp99SourceTildePiLargeBlocks_iff]
  refine ⟨offset, ?_⟩
  funext i
  apply Fin.ext
  simp only [cmp99SourceTildePiOffsetBlock, Nat.cast_zero, sub_zero]
  rw [← ZMod.val_cast_of_lt (block i).isLt]
  apply congrArg ZMod.val
  have hcast :
      (((Int.toNat (z i) : ℕ) : ZMod (2 * Q))) =
        ((z i : ℤ) : ZMod (2 * Q)) := by
    rw [← Int.cast_natCast]
    exact congrArg (fun w : ℤ => (w : ZMod (2 * Q)))
      (Int.toNat_of_nonneg (hz0 i))
  rw [hcast]
  have hzmod :
      ((block i).val : ZMod (2 * Q)) =
        2 * ((cell i).val : ZMod (2 * Q)) +
          (z i : ZMod (2 * Q)) := by
    apply ZMod.val_injective (2 * Q)
    rw [ZMod.val_cast_of_lt (block i).isLt]
    exact hzEq i
  simpa [Nat.cast_ofNat] using hzmod.symm

/-- Finset of all coarse blocks satisfying the exact source support
predicate. -/
noncomputable def cmp95SourcePeriodicCoarseCellSupportFinset
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) :
    Finset (FinBox 4 (2 * Q)) := by
  classical
  exact Finset.univ.filter (cmp95SourcePeriodicCoarseCellSupport Q cell)

@[simp] theorem mem_cmp95SourcePeriodicCoarseCellSupportFinset_iff
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q)
    (block : FinBox 4 (2 * Q)) :
    block ∈ cmp95SourcePeriodicCoarseCellSupportFinset cell ↔
      cmp95SourcePeriodicCoarseCellSupport Q cell block := by
  classical
  simp [cmp95SourcePeriodicCoarseCellSupportFinset]

/-- Sharp physical support cardinality: the centred cutoff is supported on
the literal `2^4 = 16` large blocks of its source cell. -/
theorem card_cmp95SourcePeriodicCoarseCellSupportFinset_le_sixteen
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) :
    (cmp95SourcePeriodicCoarseCellSupportFinset cell).card ≤ 16 := by
  classical
  calc
    (cmp95SourcePeriodicCoarseCellSupportFinset cell).card ≤
        (cmp99SourceBaseCell cell).card := by
      apply Finset.card_le_card
      intro block hblock
      exact cmp95SourcePeriodicCoarseCellSupport_mem_sourceBaseCell cell block
        ((mem_cmp95SourcePeriodicCoarseCellSupportFinset_iff cell block).mp
          hblock)
    _ = 16 := card_cmp99SourceBaseCell cell

/-- Uniform volume-independent cardinality of the exact support predicate. -/
theorem card_filter_cmp95SourcePeriodicCoarseCellSupport_le
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) :
    (cmp95SourcePeriodicCoarseCellSupportFinset cell).card ≤ 81 := by
  classical
  apply le_trans (Finset.card_le_card ?_)
    (card_cmp95SourcePeriodicCoarseCellCarrier_le cell)
  intro block hblock
  exact cmp95SourcePeriodicCoarseCellSupport_mem_carrier cell block
    ((mem_cmp95SourcePeriodicCoarseCellSupportFinset_iff cell block).mp hblock)

end

end YangMills.RG

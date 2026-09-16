/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceBasePartition

/-!
# The literal concentric CMP99 cubes `tilde Pi^n`

CMP99 Sect. C (printed p. 408) starts from a partition cube `Pi` made of
`2^4` large blocks and defines `tilde Pi^n` to be the concentric cube with
`2 + 2n` large blocks per coordinate.  This file constructs that family on
the periodic large-block torus itself.  In particular it also covers the
odd, source-cell-misaligned cube `tilde Pi^5`; it is not simulated by a
collar of whole source cells.

The construction is an image of the literal offset box
`Fin 4 -> Fin (2 + 2n)`.  Consequently its cardinality is always at most
`(2 + 2n)^4`, with equality whenever that side fits inside the torus.  No
propagator, boundary-value problem, or identification with the CMP99
operators `G'_Pi` and `C_Pi` is made here.
-/

namespace YangMills.RG

noncomputable section

/-- The large block at offset `offset` in the concentric cube
`tilde Pi^n`.  The lower corner is the lower corner of `Pi` shifted by `n`
large blocks in every negative coordinate direction. -/
def cmp99SourceTildePiOffsetBlock {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (n : ℕ)
    (offset : Fin 4 → Fin (2 + 2 * n)) : FinBox 4 (2 * Q) :=
  fun i =>
    ⟨(((2 * (cell i).val : ℕ) : ZMod (2 * Q)) +
        ((offset i).val : ZMod (2 * Q)) - (n : ZMod (2 * Q))).val,
      ZMod.val_lt _⟩

/-- Literal periodic large-block carrier of the printed cube
`tilde Pi^n`. -/
noncomputable def cmp99SourceTildePiLargeBlocks {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (n : ℕ) : Finset (FinBox 4 (2 * Q)) :=
  Finset.univ.image (cmp99SourceTildePiOffsetBlock cell n)

@[simp] theorem mem_cmp99SourceTildePiLargeBlocks_iff {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (n : ℕ) (block : FinBox 4 (2 * Q)) :
    block ∈ cmp99SourceTildePiLargeBlocks cell n ↔
      ∃ offset : Fin 4 → Fin (2 + 2 * n),
        cmp99SourceTildePiOffsetBlock cell n offset = block := by
  simp [cmp99SourceTildePiLargeBlocks]

/-- The source cube has at most its printed number `(2+2n)^4` of large
blocks, including on small periodic tori where nominal offsets can collide. -/
theorem card_cmp99SourceTildePiLargeBlocks_le {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (n : ℕ) :
    (cmp99SourceTildePiLargeBlocks cell n).card ≤ (2 + 2 * n) ^ 4 := by
  classical
  calc
    (cmp99SourceTildePiLargeBlocks cell n).card ≤
        (Finset.univ : Finset (Fin 4 → Fin (2 + 2 * n))).card :=
      Finset.card_image_le
    _ = (2 + 2 * n) ^ 4 := by
      simp

/-- If the printed side `2+2n` fits inside the large-block torus, distinct
offsets remain distinct after periodic embedding. -/
theorem cmp99SourceTildePiOffsetBlock_injective {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (n : ℕ) (hfit : 2 + 2 * n ≤ 2 * Q) :
    Function.Injective (cmp99SourceTildePiOffsetBlock cell n) := by
  intro left right h
  funext i
  have hiFin := congrFun h i
  have hiVal :
      (((2 * (cell i).val : ℕ) : ZMod (2 * Q)) +
          ((left i).val : ZMod (2 * Q)) - (n : ZMod (2 * Q))).val =
        (((2 * (cell i).val : ℕ) : ZMod (2 * Q)) +
          ((right i).val : ZMod (2 * Q)) - (n : ZMod (2 * Q))).val :=
    congrArg Fin.val hiFin
  have hiZ :
      ((2 * (cell i).val : ℕ) : ZMod (2 * Q)) +
          ((left i).val : ZMod (2 * Q)) - (n : ZMod (2 * Q)) =
        ((2 * (cell i).val : ℕ) : ZMod (2 * Q)) +
          ((right i).val : ZMod (2 * Q)) - (n : ZMod (2 * Q)) :=
    ZMod.val_injective (2 * Q) hiVal
  have hcast : ((left i).val : ZMod (2 * Q)) =
      ((right i).val : ZMod (2 * Q)) := by
    exact add_left_cancel (sub_left_inj.mp hiZ)
  have hleftLt : (left i).val < 2 * Q :=
    (left i).isLt.trans_le hfit
  have hrightLt : (right i).val < 2 * Q :=
    (right i).isLt.trans_le hfit
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_cast_of_lt hleftLt, ZMod.val_cast_of_lt hrightLt] at hval
  exact Fin.ext hval

/-- Exact printed cardinality when the concentric cube does not wrap around
the periodic large-block torus. -/
theorem card_cmp99SourceTildePiLargeBlocks_eq {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (n : ℕ) (hfit : 2 + 2 * n ≤ 2 * Q) :
    (cmp99SourceTildePiLargeBlocks cell n).card = (2 + 2 * n) ^ 4 := by
  classical
  rw [cmp99SourceTildePiLargeBlocks,
    Finset.card_image_of_injective _
      (cmp99SourceTildePiOffsetBlock_injective cell n hfit)]
  simp

/-- The literal family is monotone in its enlargement index. -/
theorem cmp99SourceTildePiLargeBlocks_mono {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) {n m : ℕ} (hnm : n ≤ m) :
    cmp99SourceTildePiLargeBlocks cell n ⊆
      cmp99SourceTildePiLargeBlocks cell m := by
  classical
  intro block hblock
  rw [mem_cmp99SourceTildePiLargeBlocks_iff] at hblock ⊢
  obtain ⟨offset, rfl⟩ := hblock
  let shift : ℕ := m - n
  let enlargedOffset : Fin 4 → Fin (2 + 2 * m) := fun i =>
    ⟨(offset i).val + shift, by
      have hoff := (offset i).isLt
      dsimp only [shift]
      omega⟩
  refine ⟨enlargedOffset, ?_⟩
  funext i
  apply Fin.ext
  apply congrArg ZMod.val
  change
    ((2 * (cell i).val : ℕ) : ZMod (2 * Q)) +
          ((enlargedOffset i).val : ZMod (2 * Q)) -
            (m : ZMod (2 * Q)) =
      ((2 * (cell i).val : ℕ) : ZMod (2 * Q)) +
          ((offset i).val : ZMod (2 * Q)) -
            (n : ZMod (2 * Q))
  dsimp only [enlargedOffset, shift]
  have hmnZ : (m : ZMod (2 * Q)) =
      ((m - n : ℕ) : ZMod (2 * Q)) + (n : ZMod (2 * Q)) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hnm]
  rw [hmnZ]
  push_cast
  ring

/-- At enlargement index zero the parametric construction is exactly the
literal source partition cell `Pi`, not merely a set of the same size. -/
theorem cmp99SourceTildePiLargeBlocks_zero {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    cmp99SourceTildePiLargeBlocks cell 0 = cmp99SourceBaseCell cell := by
  classical
  ext block
  rw [mem_cmp99SourceTildePiLargeBlocks_iff,
    mem_cmp99SourceBaseCell_iff]
  constructor
  · rintro ⟨offset, rfl⟩
    change blockSite 2 Q
      (cmp99SourceTildePiOffsetBlock cell 0 offset) = cell
    rw [blockSite_eq_iff]
    intro i
    have hlt : 2 * (cell i).val + (offset i).val < 2 * Q := by
      have hc := (cell i).isLt
      have hoff := (offset i).isLt
      omega
    simp only [cmp99SourceTildePiOffsetBlock, Nat.cast_zero]
    have hz :
        ((2 * (cell i).val : ℕ) : ZMod (2 * Q)) +
              ((offset i).val : ZMod (2 * Q)) - (0 : ZMod (2 * Q)) =
            ((2 * (cell i).val + (offset i).val : ℕ) : ZMod (2 * Q)) := by
      push_cast
      ring
    rw [hz, ZMod.val_cast_of_lt hlt]
    omega
  · intro hblock
    have hcube := (blockSite_eq_iff_cube 2 Q block cell).mp hblock
    let offset : Fin 4 → Fin 2 := fun i =>
      ⟨(block i).val - 2 * (cell i).val, by
        have hi := hcube i
        omega⟩
    refine ⟨offset, ?_⟩
    funext i
    apply Fin.ext
    simp only [cmp99SourceTildePiOffsetBlock]
    rw [← ZMod.val_cast_of_lt (block i).isLt]
    apply congrArg ZMod.val
    have hi := hcube i
    dsimp only [offset]
    rw [Nat.cast_sub hi.1]
    push_cast
    ring

/-- The three concentric cubes used explicitly in Sect. C have the printed
volume-independent cardinality bounds. -/
theorem card_cmp99SourceTildePi4LargeBlocks_le {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    (cmp99SourceTildePiLargeBlocks cell 4).card ≤ 10000 := by
  simpa using card_cmp99SourceTildePiLargeBlocks_le cell 4

theorem card_cmp99SourceTildePi5LargeBlocks_le {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    (cmp99SourceTildePiLargeBlocks cell 5).card ≤ 20736 := by
  simpa using card_cmp99SourceTildePiLargeBlocks_le cell 5

theorem card_cmp99SourceTildePi8LargeBlocks_le {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) :
    (cmp99SourceTildePiLargeBlocks cell 8).card ≤ 104976 := by
  simpa using card_cmp99SourceTildePiLargeBlocks_le cell 8

end

end YangMills.RG

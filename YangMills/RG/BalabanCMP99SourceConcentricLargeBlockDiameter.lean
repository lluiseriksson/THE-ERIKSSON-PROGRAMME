/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceConcentricLargeBlockCube
import YangMills.RG.PhysicalShellLocalityQ

/-!
# Uniform diameter of the literal CMP99 concentric cubes

The printed region `tilde Pi^n` is an interval of `2+2n` consecutive large
blocks in every periodic coordinate.  Hence its Chebyshev diameter is at most
`1+2n`, independently of the ambient torus size.  This is the source-specific
diameter needed to turn terminal operator-norm bounds into physical kernel
bounds without a volume factor.
-/

namespace YangMills.RG

noncomputable section

/-- Circular distance is invariant under a common affine translation. -/
theorem zmodCircDist_add_sub_common {N : ℕ}
    (base shift x y : ZMod N) :
    zmodCircDist (base + x - shift) (base + y - shift) =
      zmodCircDist x y := by
  unfold zmodCircDist
  congr 1 <;> ring

/-- Two natural residues in a symmetric window of width `W` have circular
distance at most `W`; no assumption that the window fits in the torus is
needed. -/
theorem zmodCircDist_natCast_le_of_window {N : ℕ} [NeZero N]
    (a b W : ℕ) (hab : a ≤ b + W) (hba : b ≤ a + W) :
    zmodCircDist (a : ZMod N) (b : ZMod N) ≤ W := by
  rcases le_total b a with h | h
  · unfold zmodCircDist
    calc
      zmodCircVal ((a : ZMod N) - (b : ZMod N))
          ≤ (((a : ZMod N) - (b : ZMod N))).val := zmodCircVal_le_val _
      _ = (a - b) % N := by rw [← Nat.cast_sub h, ZMod.val_natCast]
      _ ≤ a - b := Nat.mod_le _ _
      _ ≤ W := by omega
  · rw [zmodCircDist_comm]
    unfold zmodCircDist
    calc
      zmodCircVal ((b : ZMod N) - (a : ZMod N))
          ≤ (((b : ZMod N) - (a : ZMod N))).val := zmodCircVal_le_val _
      _ = (b - a) % N := by rw [← Nat.cast_sub h, ZMod.val_natCast]
      _ ≤ b - a := Nat.mod_le _ _
      _ ≤ W := by omega

/-- Coordinatewise diameter of the literal periodic offset box. -/
theorem finTorusDist_cmp99SourceTildePiOffsetBlock_le
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) (n : ℕ)
    (left right : Fin 4 → Fin (2 + 2 * n)) (i : Fin 4) :
    finTorusDist
        (cmp99SourceTildePiOffsetBlock cell n left i)
        (cmp99SourceTildePiOffsetBlock cell n right i) ≤ 1 + 2 * n := by
  let base : ZMod (2 * Q) := (2 * (cell i).val : ℕ)
  have hleft :
      ((cmp99SourceTildePiOffsetBlock cell n left i).val : ZMod (2 * Q)) =
        base + (left i).val - n := by
    apply ZMod.val_injective
    rw [ZMod.val_cast_of_lt
      (cmp99SourceTildePiOffsetBlock cell n left i).isLt]
    rfl
  have hright :
      ((cmp99SourceTildePiOffsetBlock cell n right i).val : ZMod (2 * Q)) =
        base + (right i).val - n := by
    apply ZMod.val_injective
    rw [ZMod.val_cast_of_lt
      (cmp99SourceTildePiOffsetBlock cell n right i).isLt]
    rfl
  unfold finTorusDist
  rw [hleft, hright, zmodCircDist_add_sub_common]
  exact zmodCircDist_natCast_le_of_window (left i).val (right i).val
    (1 + 2 * n) (by omega) (by omega)

/-- The literal `tilde Pi^n` has volume-independent Chebyshev diameter
`1+2n`, including when periodic wraparound identifies nominal offsets. -/
theorem finBoxDist_le_of_mem_cmp99SourceTildePiLargeBlocks
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q) (n : ℕ)
    {left right : FinBox 4 (2 * Q)}
    (hleft : left ∈ cmp99SourceTildePiLargeBlocks cell n)
    (hright : right ∈ cmp99SourceTildePiLargeBlocks cell n) :
    finBoxDist left right ≤ 1 + 2 * n := by
  rw [mem_cmp99SourceTildePiLargeBlocks_iff] at hleft hright
  obtain ⟨leftOffset, rfl⟩ := hleft
  obtain ⟨rightOffset, rfl⟩ := hright
  unfold finBoxDist
  apply Finset.sup_le
  intro i _
  exact finTorusDist_cmp99SourceTildePiOffsetBlock_le
    cell n leftOffset rightOffset i

end

end YangMills.RG

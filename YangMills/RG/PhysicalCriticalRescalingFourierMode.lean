/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCriticalRescalingFourierNoGo

/-!
# The block-periodic Fourier transverse mode

This module lifts the primitive-cycle Fourier phase from
`PhysicalCriticalRescalingFourierNoGo` to every fine block and embeds it in a
real two-plane of `SUNLieCoord Nc`.
-/

namespace YangMills.RG

open Matrix Module

/-! ## The Lie-valued Fourier profile -/

/-- Offset of a fine coordinate inside its block of side `L`. -/
def periodicBlockOffset (L N' : ℕ) [NeZero L]
    (m : Fin (L * N')) : Fin L :=
  ⟨m.val % L, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))⟩

@[simp]
theorem periodicBlockOffset_blockOffsetSite
    {d L N' : ℕ} [NeZero L] (y : FinBox d N')
    (r : Fin d → Fin L) (j : Fin d) :
    periodicBlockOffset L N' (blockOffsetSite L N' y r j) = r j := by
  apply Fin.ext
  simp only [periodicBlockOffset, blockOffsetSite_val]
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (r j).isLt]

/-- First Fourier phase in the chosen real Lie-coordinate two-plane. -/
noncomputable def blockFourierProfile
    (L N' Nc : ℕ) [NeZero L] (hNc : 2 ≤ Nc)
    (m : Fin (L * N')) : SUNLieCoord Nc :=
  complexLiePlaneEmbedding Nc hNc
    (blockFourierRoot L ^ (periodicBlockOffset L N' m).val)

theorem norm_sq_blockFourierProfile
    (L N' Nc : ℕ) [NeZero L] (hNc : 2 ≤ Nc)
    (m : Fin (L * N')) :
    ‖blockFourierProfile L N' Nc hNc m‖ ^ 2 = 1 := by
  rw [blockFourierProfile, norm_sq_complexLiePlaneEmbedding,
    norm_pow, norm_blockFourierRoot, one_pow, one_pow]

theorem sum_blockFourierProfile_block_eq_zero
    {d L N' Nc : ℕ} [NeZero L] (hL : 2 ≤ L) (hNc : 2 ≤ Nc)
    (y : FinBox d N') (j : Fin d) :
    ∑ x ∈ blockOf (d := d) L N' y,
      blockFourierProfile L N' Nc hNc (x j) = 0 := by
  rw [sum_blockOf_eq_sum_offsets]
  simp only [blockFourierProfile, periodicBlockOffset_blockOffsetSite]
  have hsplit :
      (∑ r : Fin d → Fin L,
          complexLiePlaneEmbedding Nc hNc (blockFourierRoot L ^ (r j).val)) =
        ∑ p : Fin L × ({k : Fin d // k ≠ j} → Fin L),
          complexLiePlaneEmbedding Nc hNc (blockFourierRoot L ^ p.1.val) := by
    rw [← Equiv.sum_comp
      (Equiv.piSplitAt j (fun _ : Fin d => Fin L))
      (fun p => complexLiePlaneEmbedding Nc hNc
        (blockFourierRoot L ^ p.1.val))]
    rfl
  rw [hsplit, Fintype.sum_prod_type]
  simp only [Finset.sum_const]
  rw [← Finset.smul_sum]
  have hmap :
      (∑ r : Fin L,
          complexLiePlaneEmbedding Nc hNc (blockFourierRoot L ^ r.val)) = 0 := by
    rw [← map_sum, sum_blockFourierRoot_pow_eq_zero L hL, map_zero]
  rw [hmap, smul_zero]

theorem blockFourierProfile_iterate_shift_other
    {d L N' Nc : ℕ} [NeZero L] [NeZero N']
    (hNc : 2 ≤ Nc) (x : FinBox d (L * N'))
    (i j : Fin d) (hij : i ≠ j) (k : ℕ) :
    blockFourierProfile L N' Nc hNc
        (((fun z => FinBox.shift z i)^[k] x) j) =
      blockFourierProfile L N' Nc hNc (x j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hcoord : (FinBox.shift ((fun z => FinBox.shift z i)^[k] x) i) j =
          ((fun z => FinBox.shift z i)^[k] x) j := by
        simp [FinBox.shift, Ne.symm hij]
      rw [hcoord, ih]

end YangMills.RG

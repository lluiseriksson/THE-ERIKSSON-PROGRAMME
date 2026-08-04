/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCriticalRescalingFourierMode

/-!
# Exact energy of the block-periodic Fourier profile
-/

namespace YangMills.RG

open Matrix Module

/-- Successor on a cycle of arbitrary positive side. -/
def blockCycleSucc (L : ℕ) [NeZero L] (r : Fin L) : Fin L :=
  ⟨(r.val + 1) % L, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))⟩

theorem blockFourierRoot_pow_blockCycleSucc
    (L : ℕ) [NeZero L] (r : Fin L) :
    blockFourierRoot L ^ (blockCycleSucc L r).val =
      blockFourierRoot L ^ r.val * blockFourierRoot L := by
  by_cases h : r.val + 1 < L
  · rw [show (blockCycleSucc L r).val = r.val + 1 by
      simp [blockCycleSucc, Nat.mod_eq_of_lt h]]
    exact pow_succ _ _
  · have heq : r.val + 1 = L := by omega
    rw [show (blockCycleSucc L r).val = 0 by simp [blockCycleSucc, heq]]
    rw [pow_zero, ← pow_succ, heq, blockFourierRoot_pow_eq_one]

/-- Successor on the complete fine coordinate cycle. -/
def periodicCycleSuccL (L N' : ℕ) [NeZero L] [NeZero N']
    (m : Fin (L * N')) : Fin (L * N') :=
  ⟨(m.val + 1) % (L * N'), Nat.mod_lt _
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L))
      (Nat.pos_of_ne_zero (NeZero.ne N')))⟩

theorem periodicBlockOffset_periodicCycleSuccL
    (L N' : ℕ) [NeZero L] [NeZero N'] (hL : 2 ≤ L)
    (m : Fin (L * N')) :
    periodicBlockOffset L N' (periodicCycleSuccL L N' m) =
      blockCycleSucc L (periodicBlockOffset L N' m) := by
  apply Fin.ext
  simp only [periodicBlockOffset, periodicCycleSuccL, blockCycleSucc]
  have hdvd : L ∣ L * N' := dvd_mul_right _ _
  have hone : 1 % L = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod, hone]

theorem periodicCycleSuccL_eq_shift_coord
    {d L N' : ℕ} [NeZero L] [NeZero N']
    (x : FinBox d (L * N')) (j : Fin d) :
    periodicCycleSuccL L N' (x j) = (x.shift j) j := by
  apply Fin.ext
  simp [periodicCycleSuccL, FinBox.shift]

/-- The exact first-cycle eigenvalue. -/
noncomputable def blockFourierEigenvalue (L : ℕ) : ℝ :=
  ‖blockFourierRoot L - 1‖ ^ 2

theorem blockFourierEigenvalue_nonneg (L : ℕ) :
    0 ≤ blockFourierEigenvalue L := by
  exact sq_nonneg _

theorem blockFourierEigenvalue_le
    (L : ℕ) [NeZero L] :
    blockFourierEigenvalue L ≤ (2 * Real.pi / L) ^ 2 := by
  unfold blockFourierEigenvalue
  have h := norm_blockFourierRoot_sub_one_le L
  have hn : 0 ≤ ‖blockFourierRoot L - 1‖ := norm_nonneg _
  have hb : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity
  nlinarith

theorem norm_sq_blockFourierProfile_cycleSucc
    (L N' Nc : ℕ) [NeZero L] [NeZero N']
    (hL : 2 ≤ L) (hNc : 2 ≤ Nc) (m : Fin (L * N')) :
    ‖blockFourierProfile L N' Nc hNc m -
        blockFourierProfile L N' Nc hNc (periodicCycleSuccL L N' m)‖ ^ 2 =
      blockFourierEigenvalue L := by
  rw [blockFourierProfile, blockFourierProfile, ← map_sub,
    norm_sq_complexLiePlaneEmbedding]
  rw [periodicBlockOffset_periodicCycleSuccL L N' hL,
    blockFourierRoot_pow_blockCycleSucc]
  unfold blockFourierEigenvalue
  have hz : ‖blockFourierRoot L ^ (periodicBlockOffset L N' m).val‖ = 1 := by
    rw [norm_pow, norm_blockFourierRoot, one_pow]
  calc
    ‖blockFourierRoot L ^ (periodicBlockOffset L N' m).val -
        blockFourierRoot L ^ (periodicBlockOffset L N' m).val *
          blockFourierRoot L‖ ^ 2 =
        ‖blockFourierRoot L ^ (periodicBlockOffset L N' m).val *
          (1 - blockFourierRoot L)‖ ^ 2 := by ring_nf
    _ = ‖1 - blockFourierRoot L‖ ^ 2 := by rw [norm_mul, hz, one_mul]
    _ = ‖blockFourierRoot L - 1‖ ^ 2 := by
      rw [← norm_neg (1 - blockFourierRoot L)]
      congr 2
      ring

theorem sum_finBox_blockFourierProfile_shift_diff_norm_sq
    (d L N' Nc : ℕ) [NeZero L] [NeZero N']
    (hL : 2 ≤ L) (hNc : 2 ≤ Nc) (j : Fin d) :
    (∑ x : FinBox d (L * N'),
      ‖blockFourierProfile L N' Nc hNc (x j) -
        blockFourierProfile L N' Nc hNc ((x.shift j) j)‖ ^ 2) =
      ((((L * N' : ℕ) : ℝ) ^ d) * blockFourierEigenvalue L) := by
  rw [Finset.sum_congr rfl (fun x _ => by
    rw [← periodicCycleSuccL_eq_shift_coord x j,
      norm_sq_blockFourierProfile_cycleSucc L N' Nc hL hNc (x j)])]
  rw [Finset.sum_const, Finset.card_univ, card_finBox, nsmul_eq_mul]
  push_cast
  rfl

end YangMills.RG

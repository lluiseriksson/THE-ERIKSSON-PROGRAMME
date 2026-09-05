import YangMills.RG.BlockLattice
import Mathlib.Tactic.Omega

/-!
PRE-VALIDATION: geometry draft; source present, no .olean materialized,
not compiler verified. Coordinatewise Fin.rev represents -n-1 modulo the
finite side. The coarse map is the literal blockSite, not a free owner map.
Only the half-cell reflection/block dictionary is studied. This does not
construct even extension, a regional inverse, Q intertwining or a Green bound.
-/

namespace YangMills.RG

private theorem reflected_block_div
    (M N x : ℕ) (hM : 0 < M) (hx : x < M * N) :
    (M * N - 1 - x) / M = N - 1 - x / M := by
  have hq : x / M < N := Nat.div_lt_of_lt_mul hx
  have hr : x % M < M := Nat.mod_lt x hM
  have hsplit := Nat.div_add_mod x M
  have hcoarse : N - 1 - x / M + x / M + 1 = N := by omega
  have hblocks := congrArg (fun n : ℕ => M * n) hcoarse
  simp only [Nat.mul_add, Nat.mul_one] at hblocks
  have hreflect : M * N - 1 - x + x + 1 = M * N := by omega
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm]
    omega
  · rw [Nat.succ_mul, Nat.mul_comm (N - 1 - x / M) M]
    omega

def neumannBlockReflectionDraft {d N : ℕ}
    (branch : Fin d → Bool) (x : FinBox d N) : FinBox d N :=
  fun mu => if branch mu then (x mu).rev else x mu

theorem neumannBlockReflectionDraft_involutive {d N : ℕ}
    (branch : Fin d → Bool) :
    Function.Involutive (neumannBlockReflectionDraft (N := N) branch) := by
  intro x
  funext mu
  cases h : branch mu <;> simp [neumannBlockReflectionDraft, h]

theorem blockSite_neumannBlockReflectionDraft {d M N : ℕ} [NeZero M]
    (branch : Fin d → Bool) (x : FinBox d (M * N)) :
    blockSite M N (neumannBlockReflectionDraft branch x) =
      neumannBlockReflectionDraft branch (blockSite M N x) := by
  funext mu
  apply Fin.ext
  cases h : branch mu
  · simp [neumannBlockReflectionDraft, h, blockSite_val]
  · simp only [neumannBlockReflectionDraft, h, Bool.true_eq, if_true,
      blockSite_val, Fin.val_rev]
    exact reflected_block_div M N (x mu).val
      (Nat.pos_of_ne_zero (NeZero.ne M)) (x mu).isLt

theorem neumannBlockReflectionDraft_sameOwner_iff
    {d M N : ℕ} [NeZero M] (branch : Fin d → Bool)
    (x y : FinBox d (M * N)) :
    blockSite M N (neumannBlockReflectionDraft branch x) =
        blockSite M N (neumannBlockReflectionDraft branch y) ↔
      blockSite M N x = blockSite M N y := by
  rw [blockSite_neumannBlockReflectionDraft, blockSite_neumannBlockReflectionDraft]
  exact (neumannBlockReflectionDraft_involutive branch).injective.eq_iff

end YangMills.RG

#print axioms YangMills.RG.neumannBlockReflectionDraft_involutive
#print axioms YangMills.RG.blockSite_neumannBlockReflectionDraft
#print axioms YangMills.RG.neumannBlockReflectionDraft_sameOwner_iff

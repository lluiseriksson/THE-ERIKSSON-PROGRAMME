import YangMills.RG.BlockLattice

/-!
# Half-cell reflection and the literal block-owner map

Cold-verified at source59160603dda023d9f577ea7edc96f24995de1ac5: all16
stages, the production focal and exact three-name audit passed. Downloaded
archives and production .olean were independently verified; see ledger1126.
The earlier scratch HOT diagnostic remains separately recorded in ledger1125.

Coordinatewise Fin.rev is the half-cell reflection -n-1 modulo the side.
Only geometry is proved: involution, blockSite intertwining, same-owner
invariance. No physical Q*Q intertwining, regional inverse, derivative B0
or window15 attainment is claimed. Counters20/41,TermSource0 unchanged.
-/

namespace YangMills.RG

private theorem neumannHalfCell_block_div
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

def neumannHalfCellReflection {d N : ℕ}
    (branch : Fin d → Bool) (x : FinBox d N) : FinBox d N :=
  fun mu => if branch mu then (x mu).rev else x mu

theorem neumannHalfCellReflection_involutive {d N : ℕ}
    (branch : Fin d → Bool) :
    Function.Involutive (neumannHalfCellReflection (N := N) branch) := by
  intro x
  funext mu
  cases h : branch mu <;> simp [neumannHalfCellReflection, h]

theorem blockSite_neumannHalfCellReflection {d M N : ℕ} [NeZero M]
    (branch : Fin d → Bool) (x : FinBox d (M * N)) :
    blockSite M N (neumannHalfCellReflection branch x) =
      neumannHalfCellReflection branch (blockSite M N x) := by
  funext mu
  apply Fin.ext
  cases h : branch mu
  · simp [neumannHalfCellReflection, h, blockSite_val]
  · simp only [neumannHalfCellReflection, h, if_true,
      blockSite_val, Fin.val_rev]
    simpa only [Nat.sub_sub, Nat.add_comm] using neumannHalfCell_block_div M N (x mu).val
      (Nat.pos_of_ne_zero (NeZero.ne M)) (x mu).isLt

theorem neumannHalfCellReflection_sameOwner_iff
    {d M N : ℕ} [NeZero M] (branch : Fin d → Bool)
    (x y : FinBox d (M * N)) :
    blockSite M N (neumannHalfCellReflection branch x) =
        blockSite M N (neumannHalfCellReflection branch y) ↔
      blockSite M N x = blockSite M N y := by
  rw [blockSite_neumannHalfCellReflection, blockSite_neumannHalfCellReflection]
  exact (neumannHalfCellReflection_involutive branch).injective.eq_iff

end YangMills.RG

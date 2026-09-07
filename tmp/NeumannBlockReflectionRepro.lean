import Mathlib.Data.Fin.Basic

/-!
PRE-VALIDATION: arithmetic reproducer; source present, no .olean materialized,
not compiler verified. This isolates the half-cell reflection/block-division
identity before any project bootstrap. No regional inverse is asserted.
-/

theorem neumannBlockReflection_div_repro
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

theorem neumannBlockReflection_finrev_repro
    (M N x : ℕ) (hM : 0 < M) (hx : x < M * N) :
    (M * N - (x + 1)) / M = N - (x / M + 1) := by
  simpa only [Nat.sub_sub, Nat.add_comm] using
    neumannBlockReflection_div_repro M N x hM hx

#print axioms neumannBlockReflection_div_repro
#print axioms neumannBlockReflection_finrev_repro

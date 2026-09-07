import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

/-!
Cold compiler-verified at source29a48ac4bb1058cd71b74f65029e918d49e74b60,
2026-09-07, ledger1231; output and exact audits independently preserved.
Proof body unchanged from that cold source and HOT ledger1229.
Mathlib-only endpoint/mask algebra. These endpoint hypotheses
must later be supplied by the literal physical mixed seam producer; this
file supplies no kernel, inverse or physical operator identification.
Non-strict h <= N and the FULL branch are retained.
-/

namespace YangMills.RG

variable {E : Type*} [AddGroup E]

theorem neumannMaskedForwardDifference
    (N h k : ℕ) (hN : 0 < N) (hk : k < h) (hfit : h ≤ N)
    (F : ℤ → E)
    (hperiod : h = N → ∀ z : ℤ, F (z + (N : ℤ)) = F z)
    (hupper : h ≠ N → F (h : ℤ) = F ((h - 1 : ℕ) : ℤ)) :
    (if h = N ∨ k + 1 < h then
      F (k : ℤ) - F (((k + 1) % N : ℕ) : ℤ) else 0) =
      F (k : ℤ) - F ((k + 1 : ℕ) : ℤ) := by
  by_cases hh : h = N
  · rw [if_pos (Or.inl hh)]
    by_cases hn : k + 1 < N
    · rw [Nat.mod_eq_of_lt hn]
    · have heq : k + 1 = N := by omega
      have hp := hperiod hh 0
      simp only [zero_add] at hp
      rw [heq, Nat.mod_self, Nat.cast_zero, hp]
  · by_cases hi : k + 1 < h
    · rw [if_pos (Or.inr hi), Nat.mod_eq_of_lt (by omega : k + 1 < N)]
    · rw [if_neg (by simp [hh, hi])]
      have heq : k + 1 = h := by omega
      have hprev : h - 1 = k := by omega
      rw [heq, hupper hh, hprev, sub_self]

theorem neumannMaskedBackwardDifference
    (N h k : ℕ) (hN : 0 < N) (hk : k < h) (hfit : h ≤ N)
    (F : ℤ → E)
    (hperiod : h = N → ∀ z : ℤ, F (z + (N : ℤ)) = F z)
    (hlower : h ≠ N → F (-1) = F 0) :
    (if h = N ∨ 0 < k then
      F (((k + N - 1) % N : ℕ) : ℤ) - F (k : ℤ) else 0) =
      F ((k : ℤ) - 1) - F (k : ℤ) := by
  by_cases hk0 : k = 0
  · subst k
    by_cases hh : h = N
    · rw [if_pos (Or.inl hh)]
      have hlt : N - 1 < N := by omega
      have heq : ((N - 1 : ℕ) : ℤ) = -1 + (N : ℤ) := by omega
      simp only [Nat.zero_add, Nat.cast_zero, zero_sub]
      rw [Nat.mod_eq_of_lt hlt, heq, hperiod hh (-1)]
    · simp [hh, hlower hh]
  · rw [if_pos (Or.inr (by omega : 0 < k))]
    have heq : k + N - 1 = (k - 1) + N := by omega
    have hlt : k - 1 < N := by omega
    have hcast : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt, hcast]

end YangMills.RG

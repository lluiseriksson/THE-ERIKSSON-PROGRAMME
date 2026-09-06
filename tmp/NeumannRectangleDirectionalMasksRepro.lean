import Mathlib

/-!
# PRE-VALIDATION: directional rectangle-mask arithmetic

Source present; .olean not materialized; not compiler-verified.
This Mathlib-only repro must pass before elaborating the physical draft.
Full-period sides are retained, including N=1; no strict-fit assumption added.
-/

namespace YangMills.RG

theorem rectangleForwardMask_nat
    (k h N : ℕ) (hN : 0 < N) (hk : k < h) (hfit : h ≤ N) :
    (k + 1) % N < h ↔ h = N ∨ k + 1 < h := by
  by_cases hh : h = N
  · subst h
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact Nat.mod_lt _ hN
  · rw [Nat.mod_eq_of_lt (by omega : k + 1 < N)]
    omega

theorem rectangleBackwardMask_nat
    (k h N : ℕ) (hN : 0 < N) (hk : k < h) (hfit : h ≤ N) :
    (k + N - 1) % N < h ↔ h = N ∨ 0 < k := by
  by_cases hh : h = N
  · subst h
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact Nat.mod_lt _ hN
  · by_cases hk0 : k = 0
    · subst k
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : N - 1 < N)]
      omega
    · rw [show k + N - 1 = (k - 1) + N by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : k - 1 < N)]
      omega

#print axioms rectangleForwardMask_nat
#print axioms rectangleBackwardMask_nat

end YangMills.RG

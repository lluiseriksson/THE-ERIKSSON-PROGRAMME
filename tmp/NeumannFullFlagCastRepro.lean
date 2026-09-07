import Mathlib.Data.Int.Basic

/-!
PRE-VALIDATION: source present; compiler result not verified.
Mathlib-only repro for the physical FULL flag's scale/cast cancellation.
-/

theorem fullFlagScaleCastRepro (B N : ℕ) (m : ℤ)
    (hB : 0 < B) (hm : 0 ≤ m) :
    Int.toNat ((B : ℤ) * m) = B * N ↔ Int.toNat m = N := by
  have hc : ((B * Int.toNat m : ℕ) : ℤ) = (B : ℤ) * m := by
    simp only [Nat.cast_mul, Int.toNat_of_nonneg hm]
  have hmul : Int.toNat ((B : ℤ) * m) = B * Int.toNat m := by
    rw [← hc]
    exact Int.toNat_natCast _
  rw [hmul]
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_left hB h
  · intro h
    exact congrArg (fun n : ℕ => B * n) h

#print axioms fullFlagScaleCastRepro


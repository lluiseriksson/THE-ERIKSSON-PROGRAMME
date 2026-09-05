import Mathlib

/-!
PRE-VALIDATION: source present, .olean not materialized and result not yet
compiler-verified. Project-free reproduction of the uniform draft's natural
power lower bound. The qualified name follows Mathlib's namespace Left.
-/

theorem fullGreenUniformPowerRepro {L j : ℕ} (hL : 2 ≤ L) :
    1 ≤ L ^ (j + 1) := by
  exact Left.one_le_pow_of_le (by omega) _

#print axioms fullGreenUniformPowerRepro

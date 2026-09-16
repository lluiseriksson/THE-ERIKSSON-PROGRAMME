import Mathlib.Data.Real.Basic

/-!
# PRE-VALIDATION: explicit common summand in the F4 inequality

Source present; `.olean` not materialized, result not compiler-verified.
Project-free reproduction of the first F4 hot error. The formerly anonymous
common summand is named S. No physical theorem or scalar budget is changed.
-/

theorem fullGreenHybridIntermediateInequalityRepro
    (Pcurrent Pfloor S current upper T row : ℝ)
    (hmoment : Pcurrent ≤ Pfloor)
    (hcoef : current * Pcurrent ≤ upper * Pfloor)
    (hT : 0 ≤ T) (hrow : 0 ≤ row) :
    row * (Pcurrent + S + (current * Pcurrent) * T) ≤
      row * (Pfloor + S + (upper * Pfloor) * T) := by
  have hcentral := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hmoment (le_refl S))
      (mul_le_mul_of_nonneg_right hcoef hT)) hrow
  exact hcentral

#print axioms fullGreenHybridIntermediateInequalityRepro

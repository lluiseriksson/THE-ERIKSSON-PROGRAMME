import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
PRE-VALIDATION: source present, .olean not materialized, not compiler-verified.
Mathlib-only reproducer for the actual integer image orbit, including negative
coordinates. B is the fine-site block side; m is the coarse rectangle side.
This is not a permutation of the original half-open rectangle and not a
Neumann inverse, physical Q dictionary or bound. Run only after the active
promoted cold gate finishes, in its retained runtime, without another bootstrap.
-/

theorem neumannIntegerHalfCellOwner_repro (B n : ℤ) (hB : 0 < B) :
    (-n - 1) / B = -(n / B) - 1 := by
  rw [Int.ediv_eq_iff_of_pos hB]
  have hr0 := Int.emod_nonneg n (ne_of_gt hB)
  have hr1 := Int.emod_lt_of_pos n hB
  have hsplit := Int.ediv_mul_add_emod n B
  constructor <;> nlinarith

theorem neumannIntegerTranslatedOwner_repro
    (B m n k : ℤ) (hB : 0 < B) :
    (2 * k * (B * m) + n) / B = 2 * k * m + n / B := by
  have halgebra : 2 * k * (B * m) + n = n + B * (2 * k * m) := by ring
  rw [halgebra, Int.add_mul_ediv_left _ _ (ne_of_gt hB)]
  ring

theorem neumannIntegerReflectedOwner_repro
    (B m n k : ℤ) (hB : 0 < B) :
    (2 * k * (B * m) - n - 1) / B = 2 * k * m - n / B - 1 := by
  have halgebra : 2 * k * (B * m) - n - 1 =
      (-n - 1) + B * (2 * k * m) := by ring
  rw [halgebra, Int.add_mul_ediv_left _ _ (ne_of_gt hB),
    neumannIntegerHalfCellOwner_repro B n hB]
  ring

#print axioms neumannIntegerHalfCellOwner_repro
#print axioms neumannIntegerTranslatedOwner_repro
#print axioms neumannIntegerReflectedOwner_repro

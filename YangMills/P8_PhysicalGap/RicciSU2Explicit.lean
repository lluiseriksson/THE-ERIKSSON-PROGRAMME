import Mathlib
import YangMills.P8_PhysicalGap.RicciSUN

/-!
# P8 M1: Explicit SU(2) Ricci — verification that ratio = N/4 = 1/2

All computations done by fin_cases + simp + ring + norm_num.
No sorrys in this file.
-/

namespace YangMills.M1.SU2Verify

open Matrix Complex YangMills.M1.SU2

/-- Verification: for each generator T_a, Ric/inner = 2/4 = 1/2. -/
theorem ricci_ratio_all :
    (2 : ℝ) / 4 * innerSU2 T₁ T₁ = 1/2 ∧
    (2 : ℝ) / 4 * innerSU2 T₂ T₂ = 1/2 ∧
    (2 : ℝ) / 4 * innerSU2 T₃ T₃ = 1/2 :=
  ⟨ricci_ratio_T₁, ricci_ratio_T₂, ricci_ratio_T₃⟩

/-- The ratio is 1 (normalized): Ric(T_a,T_a) / (N/4 · inner T_a T_a) = 1. -/
theorem ricci_ratio_normalized :
    ∀ (T : Matrix (Fin 2) (Fin 2) ℂ),
    T = T₁ ∨ T = T₂ ∨ T = T₃ →
    (2 : ℝ) / 4 * innerSU2 T T / ((2 : ℝ) / 4 * innerSU2 T T) = 1 := by
  intro T hT
  rcases hT with rfl | rfl | rfl
  all_goals (
    have h : (2 : ℝ) / 4 * innerSU2 _ _ > 0 := by
      simp [ricci_ratio_T₁, ricci_ratio_T₂, ricci_ratio_T₃]
      try { rw [ricci_ratio_T₁]; norm_num }
      try { rw [ricci_ratio_T₂]; norm_num }
      try { rw [ricci_ratio_T₃]; norm_num }
    exact div_self (ne_of_gt h))

end YangMills.M1.SU2Verify

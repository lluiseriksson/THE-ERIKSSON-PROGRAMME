import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanCouplingRecursion

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91AsymptoticFreedomSkeleton — Layer 13B

Decomposes `asymptotic_freedom_implies_beta_growth` into sub-sorrys.
Source: P91 Appendix A.2.
-/

noncomputable section

/-- Step 1: Denominator d = 1 - (b₀-r_k)·β_k ∈ (0,1). Source: P91 A.2 §3. -/
theorem denominator_in_unit_interval (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_upper : 3 * balabanBetaCoeff N_c * β_k < 2)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    let d := 1 - (balabanBetaCoeff N_c - r_k) * β_k
    0 < d ∧ d < 1 := by
  have hb_pos : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have hr_left : -(balabanBetaCoeff N_c / 2) < r_k := (abs_lt.mp hr).1
  have hr_right : r_k < balabanBetaCoeff N_c / 2 := (abs_lt.mp hr).2
  have hβ_pos : 0 < β_k := by linarith
  simp only []
  constructor
  · nlinarith [mul_pos hβ_pos (show (0 : ℝ) < balabanBetaCoeff N_c / 2 + r_k from by linarith)]
  · nlinarith [mul_pos (show (0 : ℝ) < balabanBetaCoeff N_c - r_k from by linarith) hβ_pos]

/-- Step 2: 0 < d < 1 → β_k < β_k/d. Pure arithmetic, 0 sorrys. -/
theorem beta_growth_from_denominator (β_k d : ℝ) (hβ : 0 < β_k)
    (hd_pos : 0 < d) (hd_lt1 : d < 1) :
    β_k < β_k / d := by
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hdiv_pos : 0 < β_k / d := div_pos hβ hd_pos
  have heq : β_k / d * d = β_k := div_mul_cancel₀ β_k hd_ne
  nlinarith [mul_lt_mul_of_pos_left hd_lt1 hdiv_pos]

/-- Structural wrapper: step1 + step2 → AF growth. 0 new sorrys. -/
theorem asymptotic_freedom_from_denominator_control (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (_hβ_upper : 3 * balabanBetaCoeff N_c * β_k < 2)
    (_hr : |r_k| < balabanBetaCoeff N_c / 2)
    (h_step1 : let d := 1 - (balabanBetaCoeff N_c - r_k) * β_k
               0 < d ∧ d < 1) :
    β_k < balabanCouplingStep N_c β_k r_k := by
  unfold balabanCouplingStep
  have hβ_pos : 0 < β_k := by linarith
  obtain ⟨hd_pos, hd_lt1⟩ := h_step1
  have hden_eq : 1 - balabanBetaCoeff N_c * β_k + r_k * β_k
      = 1 - (balabanBetaCoeff N_c - r_k) * β_k := by ring
  rw [hden_eq]
  exact beta_growth_from_denominator β_k _ hβ_pos hd_pos hd_lt1

end

end YangMills.ClayCore

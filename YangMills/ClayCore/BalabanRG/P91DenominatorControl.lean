import Mathlib
import YangMills.ClayCore.BalabanRG.P91AsymptoticFreedomSkeleton

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91DenominatorControl — Layer 13C

Decomposes `denominator_in_unit_interval` into two sub-claims.
Source: P91 A.2 §3.
-/

noncomputable section

/-- d < 1: algebraically immediate. 0 sorrys. -/
theorem denominator_lt_one (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    1 - (balabanBetaCoeff N_c - r_k) * β_k < 1 := by
  have hb0_pos : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have hr_right : r_k < balabanBetaCoeff N_c / 2 := (abs_lt.mp hr).2
  have hβ_pos : 0 < β_k := by linarith
  have hcoeff_pos : 0 < balabanBetaCoeff N_c - r_k := by linarith
  nlinarith [mul_pos hcoeff_pos hβ_pos]

/-- d > 0: requires weak-coupling window bound. Source: P91 A.2 §3. -/
theorem denominator_pos (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
  (hβ_upper : 3 * balabanBetaCoeff N_c * β_k < 2)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    0 < 1 - (balabanBetaCoeff N_c - r_k) * β_k := by
  have hb_pos : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have hr_left : -(balabanBetaCoeff N_c / 2) < r_k := (abs_lt.mp hr).1
  have hβ_pos : 0 < β_k := by linarith
  nlinarith [mul_pos hβ_pos (show (0 : ℝ) < balabanBetaCoeff N_c / 2 + r_k from by linarith)]

/-- Combined: d ∈ (0,1). Uses dsimp to unfold the let-binding. -/
theorem denominator_in_unit_interval_v2 (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
  (hβ_upper : 3 * balabanBetaCoeff N_c * β_k < 2)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    let d := 1 - (balabanBetaCoeff N_c - r_k) * β_k
    0 < d ∧ d < 1 := by
  simp only []
  exact ⟨denominator_pos N_c β_k r_k hβ hβ_upper hr,
         denominator_lt_one N_c β_k r_k hβ hr⟩

end

end YangMills.ClayCore

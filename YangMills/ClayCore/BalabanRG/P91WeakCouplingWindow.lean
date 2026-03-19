import Mathlib
import YangMills.ClayCore.BalabanRG.P91DenominatorControl

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91WeakCouplingWindow — Layer 13D
Source: P91 A.2 §3.
-/

noncomputable section

/-- b₀ - r_k ≤ b₀ + |r_k|. -/
theorem coeff_bound (N_c : ℕ) [NeZero N_c] (r_k : ℝ) :
    balabanBetaCoeff N_c - r_k ≤ balabanBetaCoeff N_c + |r_k| := by
  have := neg_abs_le r_k   -- -|r_k| ≤ r_k
  linarith [abs_nonneg r_k]

/-- Tight window → denominator positive. 0 sorrys. -/
theorem denominator_pos_tight (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_tight : β_k < 1 / (balabanBetaCoeff N_c + |r_k|))
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    0 < 1 - (balabanBetaCoeff N_c - r_k) * β_k := by
  have hb0 : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have habs : 0 ≤ |r_k| := abs_nonneg r_k
  have hsum : 0 < balabanBetaCoeff N_c + |r_k| := by linarith
  have hβ_pos : 0 ≤ β_k := by linarith
  -- (b₀ + |r_k|) · β_k < 1  from β_k < 1/(b₀+|r_k|)
  have hprod : (balabanBetaCoeff N_c + |r_k|) * β_k < 1 := by
    have h := mul_lt_mul_of_pos_left hβ_tight hsum
    rwa [mul_div_cancel₀ 1 (ne_of_gt hsum)] at h
  -- (b₀ - r_k) · β_k ≤ (b₀ + |r_k|) · β_k
  have hle : (balabanBetaCoeff N_c - r_k) * β_k
      ≤ (balabanBetaCoeff N_c + |r_k|) * β_k :=
    mul_le_mul_of_nonneg_right (coeff_bound N_c r_k) hβ_pos
  linarith

/-- Structural wrapper. 0 new sorrys. -/
theorem denominator_pos_from_tight (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_tight : β_k < 1 / (balabanBetaCoeff N_c + |r_k|))
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    0 < 1 - (balabanBetaCoeff N_c - r_k) * β_k :=
  denominator_pos_tight N_c β_k r_k hβ hβ_tight hr

/-- The actual P91 A.2 §3 quantitative hypothesis. -/
axiom p91_tight_weak_coupling_window (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < 1 / (balabanBetaCoeff N_c + |r_k|)

end

end YangMills.ClayCore

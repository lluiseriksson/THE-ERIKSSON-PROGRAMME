import Mathlib
import YangMills.ClayCore.BalabanRG.P91WeakCouplingWindow

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91WindowFromRecursion — Layer 14A (pure algebra)

Direction: window → remainder. No P91RecursionData import.
-/

noncomputable section

/-- The remainder bound constant: C_rem = 1. -/
def remainderBoundConst : ℝ := 1

/-- If β_k is in the tight window, then |r_k| ≤ 1/β_k. 0 sorrys. -/
theorem remainder_small_P91 (N_c : ℕ) [NeZero N_c]
    (k : ℕ) (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_tight : β_k < 1 / (balabanBetaCoeff N_c + |r_k|)) :
    |r_k| ≤ remainderBoundConst / β_k := by
  unfold remainderBoundConst
  have hb0 : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have hβ_pos : 0 < β_k := by linarith
  have habs : 0 ≤ |r_k| := abs_nonneg r_k
  have hs_pos : 0 < balabanBetaCoeff N_c + |r_k| := by linarith
  have hs_ne : balabanBetaCoeff N_c + |r_k| ≠ 0 := ne_of_gt hs_pos
  have hβ_ne : β_k ≠ 0 := ne_of_gt hβ_pos
  have hprod : β_k * (balabanBetaCoeff N_c + |r_k|) < 1 := by
    have h := mul_lt_mul_of_pos_right hβ_tight hs_pos
    have hsimp : 1 / (balabanBetaCoeff N_c + |r_k|) *
        (balabanBetaCoeff N_c + |r_k|) = 1 := by field_simp [hs_ne]
    linarith [h, hsimp]
  have hprod2 : β_k * |r_k| < 1 := by nlinarith
  have hmul_le : |r_k| * β_k ≤ 1 := by linarith [hprod2]
  have hle : |r_k| ≤ 1 / β_k := by
    field_simp [hβ_ne]
    simpa [mul_comm] using hmul_le
  exact hle

/-- Algebraic lemma: β_k · (b₀ + |r_k|) < 1 → β_k < 1/(b₀ + |r_k|). 0 sorrys. -/
theorem window_from_product_small (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ_pos : 0 < β_k)
    (hprod : β_k * (balabanBetaCoeff N_c + |r_k|) < 1) :
    β_k < 1 / (balabanBetaCoeff N_c + |r_k|) := by
  have habs : 0 ≤ |r_k| := abs_nonneg r_k
  have hb0 : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have hsum_pos : 0 < balabanBetaCoeff N_c + |r_k| := by linarith
  have hsum_ne : balabanBetaCoeff N_c + |r_k| ≠ 0 := ne_of_gt hsum_pos
  have hsimp : 1 / (balabanBetaCoeff N_c + |r_k|) * (balabanBetaCoeff N_c + |r_k|) = 1 := by
    field_simp [hsum_ne]
  nlinarith [mul_pos hβ_pos hsum_pos, hsimp]


end

end YangMills.ClayCore

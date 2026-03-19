import Mathlib

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# P91BetaDriftDecomposition — Layer 14E (pure analysis)

Contains only generic analysis on sequences.
No P91 data. No sorrys. Ghost `beta_linear_drift_P91` moved to P91BetaDriftClosed.
-/

noncomputable section

/-- Pure analysis: linear drift → atTop. 0 sorrys. -/
theorem tendsto_atTop_of_linear_drift
    (β : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hdrift : ∀ k, β k + δ ≤ β (k + 1)) :
    Tendsto β atTop atTop := by
  have hmono_step : ∀ n, β n ≤ β (n + 1) :=
    fun n => le_trans (le_add_of_nonneg_right hδ.le) (hdrift n)
  have hmono : Monotone β := monotone_nat_of_le_succ hmono_step
  have hgrow : ∀ n : ℕ, β 0 + n • δ ≤ β n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [succ_nsmul]
        have haux : β 0 + n • δ + δ ≤ β (n + 1) := by linarith [ih, hdrift n]
        simpa [add_assoc] using haux
  refine hmono.tendsto_atTop_atTop ?_
  intro b
  obtain ⟨N, hN⟩ := exists_lt_nsmul hδ (b - β 0)
  exact ⟨N, le_of_lt (lt_of_lt_of_le (by linarith) (hgrow N))⟩

end

end YangMills.ClayCore

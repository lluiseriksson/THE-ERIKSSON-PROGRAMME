import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-! # P91BetaDriftDecomposition — Layer 14E -/

noncomputable section

/-- P91 A.2 §3: β grows by at least δ > 0. 1 sorry. -/
theorem beta_linear_drift_P91 (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  sorry -- P91 A.2 §3

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

/-- Structural wrapper. -/
theorem beta_tendsto_top_from_drift (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2) :
    Tendsto β atTop atTop := by
  obtain ⟨δ, hδ, hdrift⟩ := beta_linear_drift_P91 N_c data β r hβ0 hstep hr
  exact tendsto_atTop_of_linear_drift β δ hδ hdrift

end

end YangMills.ClayCore

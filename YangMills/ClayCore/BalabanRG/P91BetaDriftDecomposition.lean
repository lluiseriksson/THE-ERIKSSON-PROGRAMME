import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-! # P91BetaDriftDecomposition — Layer 14E -/

noncomputable section

/-- P91 A.2 §3: β grows by at least δ > 0 at each step. 1 sorry. -/
theorem beta_linear_drift_P91 (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  sorry -- P91 A.2 §3

/-- Linear growth lemma: β 0 + n*δ ≤ β n. -/
private lemma beta_ge_linear (β : ℕ → ℝ) (δ : ℝ)
    (hstep : ∀ k, β k + δ ≤ β (k + 1)) (n : ℕ) :
    β 0 + (n : ℝ) * δ ≤ β n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs : β n + δ ≤ β (n + 1) := hstep n
      have : β 0 + (n : ℝ) * δ + δ ≤ β (n + 1) := by nlinarith
      push_cast [Nat.cast_succ]
      linarith

/-- Pure analysis: linear drift → atTop. 0 sorrys. -/
theorem tendsto_atTop_of_linear_drift
    (β : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hstep : ∀ k, β k + δ ≤ β (k + 1)) :
    Tendsto β atTop atTop := by
  have hsucc : ∀ k, β k ≤ β (k + 1) := fun k => by linarith [hstep k]
  have hmono : Monotone β := monotone_nat_of_le_succ hsucc
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - β 0) / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hβN : β 0 + (N : ℝ) * δ ≤ β N := beta_ge_linear β δ hstep N
  have hβn : β N ≤ β n := hmono hn
  have hN' : b - β 0 < (N : ℝ) * δ := by
    have := mul_comm ((b - β 0) / δ) δ
    rw [div_mul_cancel₀] at this
    · nlinarith
    · linarith
  nlinarith

/-- Structural wrapper. 0 new sorrys. -/
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

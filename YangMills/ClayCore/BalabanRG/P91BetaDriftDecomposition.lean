import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.P91UniformDrift

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-! # P91BetaDriftDecomposition — Layer 14E -/

noncomputable section

/-- P91 A.2 §3: β grows by at least δ=b₀/2 at each step.
    Delegates to uniform_drift_from_beta0. -/
theorem beta_linear_drift_P91 (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  sorry -- Needs hβ_upper from P91RecursionData to apply uniform_drift_from_beta0

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
  have hgrow : ∀ n : ℕ, β 0 + (n : ℝ) * δ ≤ β n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => nlinarith [hstep n]
  have hβN : β 0 + (N : ℝ) * δ ≤ β N := hgrow N
  have hβn : β N ≤ β n := hmono hn
  have hN' : b - β 0 < (N : ℝ) * δ := by
    rw [div_lt_iff hδ] at hN; linarith
  nlinarith

/-- Structural wrapper: P91RecursionData → β → +∞. -/
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

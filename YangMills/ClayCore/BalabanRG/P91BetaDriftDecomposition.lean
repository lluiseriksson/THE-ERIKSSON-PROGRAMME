import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# P91BetaDriftDecomposition — Layer 14E

Separates local window control from global β divergence.

## The architecture

Local control (window): β_k < 2/b₀  ← stays in P91RecursionData theorems
Global divergence: β_k → +∞         ← needs drift, NOT the upper bound

## Two ingredients

1. beta_linear_drift_P91: β_{k+1} ≥ β_k + δ for some δ > 0 (1 sorry, P91 A.2 §3)
2. tendsto_atTop_of_linear_drift: linear drift → atTop (0 sorrys, pure analysis)
-/

noncomputable section

/-- P91 A.2 §3: The coupling β grows by at least δ > 0 at each step.
    Physical content: b₀ drives linear drift in inverse coupling. -/
theorem beta_linear_drift_P91 (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  sorry -- P91 A.2 §3: quantitative drift from AF recursion

/-- Pure analysis: linear drift → atTop. 0 sorrys. -/
theorem tendsto_atTop_of_linear_drift
    (β : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hstep : ∀ k, β k + δ ≤ β (k + 1)) :
    Tendsto β atTop atTop := by
  apply Filter.tendsto_atTop_atTop_of_monotone
  · intro m n hmn
    induction hmn with
    | refl => le_refl _
    | step h ih => linarith [hstep _]
  · intro b
    obtain ⟨n, hn⟩ := exists_nat_gt ((b - β 0) / δ)
    use n
    have hgrow : ∀ k, β 0 + k * δ ≤ β k := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk => linarith [hstep k]
    linarith [hgrow n, mul_comm (n : ℝ) δ]

/-- Structural wrapper: P91RecursionData → β → +∞. 0 new sorrys. -/
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

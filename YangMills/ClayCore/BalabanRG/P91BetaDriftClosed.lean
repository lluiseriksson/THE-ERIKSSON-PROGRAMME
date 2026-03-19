import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.P91UniformDrift
import YangMills.ClayCore.BalabanRG.P91BetaDriftDecomposition

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# P91BetaDriftClosed — Layer 14J

Closed drift/divergence path: imports P91UniformDrift (cycle-free)
and reuses tendsto_atTop_of_linear_drift from P91BetaDriftDecomposition.
-/

noncomputable section

/-- Closed drift from data + hβ_upper. 0 sorrys. -/
theorem beta_linear_drift_from_data (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) :=
  uniform_drift_from_data N_c β r hβ0 hβ_upper hr hstep

/-- Closed divergence. Reuses tendsto_atTop_of_linear_drift. 0 sorrys. -/
theorem beta_tendsto_top_from_data_closed (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c) :
    Tendsto β atTop atTop := by
  obtain ⟨δ, hδ, hdrift⟩ :=
    beta_linear_drift_from_data N_c data β r hβ0 hstep hr hβ_upper
  exact tendsto_atTop_of_linear_drift β δ hδ hdrift

end

end YangMills.ClayCore

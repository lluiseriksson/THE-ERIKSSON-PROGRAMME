import Mathlib
import YangMills.ClayCore.BalabanRG.P91BetaDriftClosed
import YangMills.ClayCore.BalabanRG.CauchyDecayFromAFWindow

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter
noncomputable section

/-!
# P91BetaDriftClosedWindow

Third downstream consumer of the analytic correction proved in
`BalabanCouplingRecursionWindow.lean`.

This file does not introduce a new hub.
It reroutes the closed drift/divergence layer so that the drift and divergence theorems
can now be invoked directly from the multiplicative weak-coupling window

  β * (3 * b₀) < 2

instead of the older explicit upper-bound interface

  β < 2 / b₀.
-/

/-- Closed drift from data + multiplicative weak-coupling window. -/
theorem beta_linear_drift_from_data_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  exact
    beta_linear_drift_from_data N_c data β r hβ0 hstep hr
      (fun k => beta_upper_of_window_mul N_c (β k) (hβ_window_mul k))

/-- Alias: `beta_linear_drift_P91` rerouted to the multiplicative weak-coupling window. -/
theorem beta_linear_drift_P91_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  exact
    beta_linear_drift_P91 N_c data β r hβ0 hstep hr
      (fun k => beta_upper_of_window_mul N_c (β k) (hβ_window_mul k))

/-- Closed divergence from data + multiplicative weak-coupling window. -/
theorem beta_tendsto_top_from_data_closed_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    Tendsto β atTop atTop := by
  exact
    beta_tendsto_top_from_data_closed N_c data β r hβ0 hstep hr
      (fun k => beta_upper_of_window_mul N_c (β k) (hβ_window_mul k))

end

end YangMills.ClayCore

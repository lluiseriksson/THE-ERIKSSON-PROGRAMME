import Mathlib
import YangMills.ClayCore.BalabanRG.P91BetaDivergence
import YangMills.ClayCore.BalabanRG.CauchyDecayFromAFWindow

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter
noncomputable section

/-!
# P91BetaDivergenceWindow

Second downstream consumer of the analytic correction proved in
`BalabanCouplingRecursionWindow.lean`.

This file does not introduce a new hub.
It reroutes the existing `P91BetaDivergence` consumer so that the rate-to-zero theorem
can now be invoked directly from the multiplicative weak-coupling window

  β * (3 * b₀) < 2

instead of the older explicit upper-bound interface

  β < 2 / b₀.
-/

/-- Full chain: data + multiplicative weak-coupling window → β diverges → rate → 0. -/
theorem rate_to_zero_from_p91_data_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  exact
    rate_to_zero_from_p91_data N_c data β r hβ0 hstep hr
      (fun k => beta_upper_of_window_mul N_c (β k) (hβ_window_mul k))

end

end YangMills.ClayCore

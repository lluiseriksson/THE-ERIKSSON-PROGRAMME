import Mathlib
import YangMills.ClayCore.BalabanRG.P91UniformDriftWindowDirect
import YangMills.ClayCore.BalabanRG.P91RecursionData

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

noncomputable section

/-!
# P91BetaDriftClosedWindow

Legacy compatibility layer for downstream consumers still importing the old
closed-window P91 theorem names.

This file no longer rebuilds drift/divergence through the older closed route.
It preserves the old exported theorem names, but the actual theorem payload now
comes directly from the corrected multiplicative weak-coupling window route

  β * (3 * b₀) < 2

implemented in `P91UniformDriftWindowDirect.lean`.

The `P91RecursionData` argument is intentionally preserved only for API stability
during migration of downstream consumers.
-/

/-- Compatibility theorem: keep the old name, route the payload directly. -/
theorem beta_linear_drift_from_data_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (_data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  simpa using
    beta_linear_drift_in_window_mul_direct
      N_c β r hβ0 hstep hr hβ_window_mul

/-- Compatibility alias for legacy downstream theorem consumers. -/
theorem beta_linear_drift_P91_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (_data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  simpa using
    beta_linear_drift_in_window_mul_direct
      N_c β r hβ0 hstep hr hβ_window_mul

/-- Compatibility theorem: keep divergence API stable while using the direct route. -/
theorem beta_tendsto_top_from_data_closed_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (_data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    Tendsto β atTop atTop := by
  simpa using
    beta_tendsto_top_in_window_mul_direct
      N_c β r hβ0 hstep hr hβ_window_mul

end

end YangMills.ClayCore

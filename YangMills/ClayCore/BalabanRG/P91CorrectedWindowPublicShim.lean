import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanCouplingRecursionWindow
import YangMills.ClayCore.BalabanRG.P91DenominatorControlWindow
import YangMills.ClayCore.BalabanRG.P91BetaDriftClosedWindow
import YangMills.ClayCore.BalabanRG.P91LegacyRouteCounterexample

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

noncomputable section

/-!
# P91CorrectedWindowPublicShim

This file does not introduce a new hub.
It exposes a single public theorem-side surface for the corrected multiplicative-window
P91 lane

  β * (3 * b₀) < 2

after the old-route hypothesis package

  β < 2 / b₀

has been explicitly audited as too weak by `P91LegacyRouteCounterexample.lean`.
-/

/-- Preferred corrected asymptotic-freedom theorem-side entrypoint. -/
theorem asymptotic_freedom_implies_beta_growth_corrected_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    β_k < balabanCouplingStep N_c β_k r_k := by
  exact
    asymptotic_freedom_implies_beta_growth_in_window_mul
      N_c β_k r_k hβ hr hβ_window_mul

/-- Preferred corrected denominator-control theorem-side entrypoint. -/
theorem denominator_in_unit_interval_corrected_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    let d := 1 - (balabanBetaCoeff N_c - r_k) * β_k
    0 < d ∧ d < 1 := by
  exact
    denominator_in_unit_interval_v2_in_window_mul
      N_c β_k r_k hβ hr hβ_window_mul

/-- Preferred corrected drift theorem-side entrypoint. -/
theorem beta_linear_drift_P91_corrected_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  exact
    beta_linear_drift_P91_in_window_mul
      N_c data β r hβ0 hstep hr hβ_window_mul

/-- Preferred corrected divergence theorem-side entrypoint. -/
theorem beta_tendsto_top_P91_corrected_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    Tendsto β atTop atTop := by
  exact
    beta_tendsto_top_from_data_closed_in_window_mul
      N_c data β r hβ0 hstep hr hβ_window_mul

/-- Audit surface: the corrected public shim is intentionally aligned with the explicit
legacy-route counterexample. -/
theorem corrected_public_shim_avoids_legacy_gap :
    let b0 := balabanBetaCoeff 1
    let β_k : ℝ := 3 / (2 * b0)
    β_k < 2 / b0 ∧ ¬ β_k * ((3 : ℝ) * b0) < 2 := by
  exact corrected_window_avoids_the_legacy_gap

end

end YangMills.ClayCore

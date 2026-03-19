import Mathlib
import YangMills.ClayCore.BalabanRG.P91DriftPositivityControl

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91UniformDrift — Layer 14I

Closes the uniform drift using only P91DriftPositivityControl.
No import of P91OnestepDriftSkeleton to avoid cycles.
-/

noncomputable section

/-- β_k ≥ 1 preserved by drift. 0 sorrys. -/
theorem beta_ge_one_all (N_c : ℕ) [NeZero N_c]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c)
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)) :
    ∀ k, 1 ≤ β k := by
  intro k
  induction k with
  | zero => exact hβ0
  | succ k ih =>
      have hden_pos : 0 < betaStepDenom N_c (β k) (r k) :=
        denominator_pos N_c (β k) (r k) ih (hβ_upper k) (hr k)
      have hdrift := one_step_beta_drift_from_controls N_c (β k) (r k) ih hden_pos (hr k)
      have hb0 : 0 < balabanBetaCoeff N_c / 2 := half_pos (balabanBetaCoeff_pos N_c)
      linarith [hstep k]

/-- Uniform drift: δ = b₀/2, using positivity controls. 0 sorrys. -/
theorem uniform_drift_from_data (N_c : ℕ) [NeZero N_c]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c)
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  refine ⟨balabanBetaCoeff N_c / 2, half_pos (balabanBetaCoeff_pos N_c), ?_⟩
  intro k
  have hβ_lower := beta_ge_one_all N_c β r hβ0 hβ_upper hr hstep k
  have hden_pos : 0 < betaStepDenom N_c (β k) (r k) :=
    denominator_pos N_c (β k) (r k) hβ_lower (hβ_upper k) (hr k)
  have hdrift := one_step_beta_drift_from_controls N_c (β k) (r k) hβ_lower hden_pos (hr k)
  linarith [hstep k]

end

end YangMills.ClayCore

import Mathlib
import YangMills.ClayCore.BalabanRG.P91OnestepDriftSkeleton

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91UniformDrift — Layer 14I

Closes `uniform_drift_lower_bound_P91` and derives β_k ≥ 1 by induction.
-/

noncomputable section

/-- β_k ≥ 1 preserved by drift. 0 sorrys. -/
theorem beta_ge_one_of_drift
    (β : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hβ0 : 1 ≤ β 0)
    (hdrift : ∀ k, β k + δ ≤ β (k + 1)) :
    ∀ k, 1 ≤ β k := by
  intro k
  induction k with
  | zero => exact hβ0
  | succ k ih => linarith [hdrift k]

/-- Uniform drift: δ = b₀/2 works for all k. 0 sorrys. -/
theorem uniform_drift_lower_bound_from_onestep (N_c : ℕ) [NeZero N_c]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ_lower : ∀ k, 1 ≤ β k)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c)
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  refine ⟨balabanBetaCoeff N_c / 2, half_pos (balabanBetaCoeff_pos N_c), ?_⟩
  intro k
  simpa [hstep k] using
    one_step_beta_drift_P91 N_c (β k) (r k) (hβ_lower k) (hβ_upper k) (hr k)

/-- Full uniform drift requiring only β 0 ≥ 1 and hβ_upper.
    Combines beta_ge_one_of_drift + uniform_drift_lower_bound_from_onestep. -/
theorem uniform_drift_from_beta0 (N_c : ℕ) [NeZero N_c]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c)
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  -- First derive β_k ≥ 1 by induction using the preliminary drift
  have hdrift_prelim : ∀ k, β k + balabanBetaCoeff N_c / 2 ≤ β (k + 1) := by
    intro k
    simp only [hstep k]
    apply one_step_beta_drift_P91
    · -- β_k ≥ 1: bootstrap by induction
      induction k with
      | zero => exact hβ0
      | succ k ih =>
          have := hstep k
          have hstep1 := one_step_beta_drift_P91 N_c (β k) (r k) ih (hβ_upper k) (hr k)
          linarith [hstep1.symm ▸ hstep k]
    · exact hβ_upper k
    · exact hr k
  exact uniform_drift_lower_bound_from_onestep N_c β r
    (beta_ge_one_of_drift β _ (half_pos (balabanBetaCoeff_pos N_c)) hβ0
      (fun k => by simpa [hstep k] using
        one_step_beta_drift_P91 N_c (β k) (r k)
          (beta_ge_one_of_drift β _ (half_pos (balabanBetaCoeff_pos N_c)) hβ0
            hdrift_prelim k)
          (hβ_upper k) (hr k)))
    hβ_upper hr hstep

end

end YangMills.ClayCore

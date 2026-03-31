import Mathlib
import YangMills.ClayCore.BalabanRG.P91DriftPositivityControl
import YangMills.ClayCore.BalabanRG.P91RecursionData

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91 Uniform Drift via Recursion Data

Proves that the Bałaban coupling sequence {β k} is monotone increasing
with uniform lower drift δ = b₀/2, using `P91RecursionData` to supply
the tight window bound required by `denominator_pos`.
-/

noncomputable section

/-- Every iterate β k satisfies β k ≥ 1, proved by induction. -/
theorem beta_ge_one_all (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)) :
    ∀ k, 1 ≤ β k := by
  intro k
  induction k with
  | zero => exact hβ0
  | succ k ih =>
      have hb0 : 0 < balabanBetaCoeff N_c / 2 := half_pos (balabanBetaCoeff_pos N_c)
      have htight : 3 * balabanBetaCoeff N_c * β k < 2 := by
        have hws := data.remainder_window_small k (β k) (balabanBetaCoeff N_c / 2) ih
        have habs : |balabanBetaCoeff N_c / 2| = balabanBetaCoeff N_c / 2 :=
          abs_of_pos hb0
        nlinarith [balabanBetaCoeff_pos N_c]
      have hden_pos : 0 < betaStepDenom N_c (β k) (r k) := by
        unfold betaStepDenom
        exact denominator_pos N_c (β k) (r k) ih htight (hr k)
      have hdrift := one_step_beta_drift_from_controls N_c (β k) (r k) ih hden_pos (hr k)
      linarith [hstep k]

/-- The coupling sequence has a uniform drift of δ = b₀/2 per step. -/
theorem uniform_drift_from_data (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  refine ⟨balabanBetaCoeff N_c / 2, half_pos (balabanBetaCoeff_pos N_c), ?_⟩
  intro k
  have hβ_lower := beta_ge_one_all N_c data β r hβ0 hr hstep k
  have hb0 : 0 < balabanBetaCoeff N_c / 2 := half_pos (balabanBetaCoeff_pos N_c)
  have htight : 3 * balabanBetaCoeff N_c * β k < 2 := by
    have hws := data.remainder_window_small k (β k) (balabanBetaCoeff N_c / 2) hβ_lower
    have habs : |balabanBetaCoeff N_c / 2| = balabanBetaCoeff N_c / 2 :=
      abs_of_pos hb0
    nlinarith [balabanBetaCoeff_pos N_c]
  have hden_pos : 0 < betaStepDenom N_c (β k) (r k) := by
    unfold betaStepDenom
    exact denominator_pos N_c (β k) (r k) hβ_lower htight (hr k)
  have hdrift := one_step_beta_drift_from_controls N_c (β k) (r k) hβ_lower hden_pos (hr k)
  linarith [hstep k]

end

end YangMills.ClayCore

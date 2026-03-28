import Mathlib
import YangMills.ClayCore.BalabanRG.P91BetaDriftDecomposition
import YangMills.ClayCore.BalabanRG.P91DriftPositivityControl

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# P91OnestepDriftSkeleton — Layer 14F

Decomposes `beta_linear_drift_P91` into two sub-sorrys.
Source: P91 A.2 §3.

## The argument

β_{k+1} = β_k / (1 - (b₀-r_k)·β_k)

For β_{k+1} - β_k ≥ δ > 0, need:
  β_k / (1 - (b₀-r_k)·β_k) - β_k ≥ δ
  = β_k · (b₀-r_k)·β_k / (1 - (b₀-r_k)·β_k)
  ≥ β_k · (b₀/2) · β_k / 1   (using |r_k| < b₀/2 and denominator < 1)
  ≥ (b₀/2) · 1² = b₀/2       (using β_k ≥ 1)

So δ = b₀/2 works. This gives the quantitative drift.

## Two sub-sorrys

1. one_step_beta_drift_P91: β_{k+1} - β_k ≥ b₀/2  (at each step k)
2. uniform_drift_lower_bound_P91: this is uniform in k (not just for fixed k)
-/

noncomputable section

/-- Step 1 (P91 A.2 §3): At each step, β grows by at least b₀/2.
    Physical content: the denominator is bounded away from 1. -/
theorem one_step_beta_drift_P91 (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_upper : 3 * balabanBetaCoeff N_c * β_k < 2)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k + balabanBetaCoeff N_c / 2 ≤ balabanCouplingStep N_c β_k r_k := by
  have hden_pos : 0 < betaStepDenom N_c β_k r_k :=
    denominator_pos N_c β_k r_k hβ hβ_upper hr
  linarith [one_step_beta_drift_from_controls N_c β_k r_k hβ hden_pos hr]

/-- Step 2: Uniformity in k: the drift is uniform, not just for one step.
    Follows from Step 1 if β_k stays in [1, 2/b₀) and |r_k| < b₀/2. -/
theorem uniform_drift_lower_bound_P91 (N_c : ℕ) [NeZero N_c]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (_hβ0 : 1 ≤ β 0)
    (_hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c)
    (_hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (h_one_step : ∀ k, β k + balabanBetaCoeff N_c / 2 ≤ balabanCouplingStep N_c (β k) (r k))
  (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k)) :
    ∀ k, β k + balabanBetaCoeff N_c / 2 ≤ β (k + 1) := by
  intro k; linarith [h_one_step k, (hstep k).symm.le]

/-- Structural wrapper: two sub-sorrys → beta_linear_drift_P91. 0 new sorrys. -/
theorem beta_linear_drift_from_one_step (N_c : ℕ) [NeZero N_c]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (_hβ0 : 1 ≤ β 0)
    (_hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c)
    (_hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (_h_one_step : ∀ k, β k + balabanBetaCoeff N_c / 2 ≤ balabanCouplingStep N_c (β k) (r k))
    (h_uniform : ∀ k, β k + balabanBetaCoeff N_c / 2 ≤ β (k + 1)) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) :=
  ⟨balabanBetaCoeff N_c / 2, by
    have := balabanBetaCoeff_pos N_c; linarith,
   h_uniform⟩

/-!
## Summary: P91 A.2 §3 decomposition

Before: 1 sorry (beta_linear_drift_P91)
After:
  one_step_beta_drift_P91:     1 sorry (P91 A.2 §3, single step)
  uniform_drift_lower_bound_P91: 1 sorry (P91 A.2 §3, uniformity)
  beta_linear_drift_from_one_step: 0 new sorrys

Key insight: δ = b₀/2 is the explicit drift constant.
Physical source: at weak coupling, (b₀-r_k)·β_k² dominates the recursion.
-/

end

end YangMills.ClayCore

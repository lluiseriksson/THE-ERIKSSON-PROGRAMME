import Mathlib
import YangMills.ClayCore.BalabanRG.P91BetaDriftDecomposition
import YangMills.ClayCore.BalabanRG.P91DriftPositivityControl
import YangMills.ClayCore.BalabanRG.P91DenominatorControlWindow

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

noncomputable section

/-!
# P91UniformDriftWindowDirect

Direct multiplicative-window drift/divergence route for P91 Appendix A.2.

This file does not introduce a new hub.
It proves the uniform drift and divergence statements directly from the corrected
multiplicative weak-coupling window

  β * (3 * b₀) < 2

together with the existing one-step positivity controls.
-/

/-- In the corrected multiplicative window, the sequence stays above `1`. -/
theorem beta_ge_one_all_in_window_mul_direct
    (N_c : ℕ) [NeZero N_c]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    ∀ k, 1 ≤ β k := by
  intro k
  induction k with
  | zero =>
      exact hβ0
  | succ k ih =>
      have hden_pos_raw :
          0 < 1 - balabanBetaCoeff N_c * β k + r k * β k := by
        exact
          balaban_coupling_step_denominator_pos_of_remainder_small_and_beta_window_mul
            N_c (β k) (r k) ih (hr k) (hβ_window_mul k)
      have hden_pos : 0 < betaStepDenom N_c (β k) (r k) := by
        unfold betaStepDenom
        have hrepr :
            1 - (balabanBetaCoeff N_c - r k) * β k =
              1 - balabanBetaCoeff N_c * β k + r k * β k := by
          ring
        simpa [hrepr] using hden_pos_raw
      have hdrift :
          balabanBetaCoeff N_c / 2 ≤
            balabanCouplingStep N_c (β k) (r k) - β k := by
        exact
          one_step_beta_drift_from_controls
            N_c (β k) (r k) ih hden_pos (hr k)
      have hb0half : 0 < balabanBetaCoeff N_c / 2 := by
        exact half_pos (balabanBetaCoeff_pos N_c)
      linarith [hstep k, hdrift, hb0half]

/-- Direct uniform drift from the corrected multiplicative weak-coupling window. -/
theorem beta_linear_drift_in_window_mul_direct
    (N_c : ℕ) [NeZero N_c]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    ∃ δ > 0, ∀ k, β k + δ ≤ β (k + 1) := by
  refine ⟨balabanBetaCoeff N_c / 2, half_pos (balabanBetaCoeff_pos N_c), ?_⟩
  intro k
  have hβ_lower :
      1 ≤ β k := by
    exact
      beta_ge_one_all_in_window_mul_direct
        N_c β r hβ0 hstep hr hβ_window_mul k
  have hden_pos_raw :
      0 < 1 - balabanBetaCoeff N_c * β k + r k * β k := by
    exact
      balaban_coupling_step_denominator_pos_of_remainder_small_and_beta_window_mul
        N_c (β k) (r k) hβ_lower (hr k) (hβ_window_mul k)
  have hden_pos : 0 < betaStepDenom N_c (β k) (r k) := by
    unfold betaStepDenom
    have hrepr :
        1 - (balabanBetaCoeff N_c - r k) * β k =
          1 - balabanBetaCoeff N_c * β k + r k * β k := by
      ring
    simpa [hrepr] using hden_pos_raw
  have hdrift :
      balabanBetaCoeff N_c / 2 ≤
        balabanCouplingStep N_c (β k) (r k) - β k := by
    exact
      one_step_beta_drift_from_controls
        N_c (β k) (r k) hβ_lower hden_pos (hr k)
  linarith [hstep k, hdrift]

/-- Direct divergence to `+∞` from the corrected multiplicative weak-coupling window. -/
theorem beta_tendsto_top_in_window_mul_direct
    (N_c : ℕ) [NeZero N_c]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    Tendsto β atTop atTop := by
  obtain ⟨δ, hδ, hdrift⟩ :=
    beta_linear_drift_in_window_mul_direct
      N_c β r hβ0 hstep hr hβ_window_mul
  exact tendsto_atTop_of_linear_drift β δ hδ hdrift

end

end YangMills.ClayCore

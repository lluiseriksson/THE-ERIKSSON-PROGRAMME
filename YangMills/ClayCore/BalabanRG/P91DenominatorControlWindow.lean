import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanCouplingRecursionWindow

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# P91DenominatorControlWindow

Clean denominator-control bridge for the corrected P91 Appendix A.2
weak-coupling window.

This file does not introduce a new hub.
It packages the denominator positivity / unit-interval step directly in the
multiplicative weak-coupling window

  β * (3 * b₀) < 2

so higher-level P91 consumers can use the corrected analytic lane without
inheriting the legacy `β < 2 / b₀` denominator route.
-/

/-- In the multiplicative weak-coupling window, the coupling-step denominator lies in `(0,1)`. -/
theorem denominator_in_unit_interval_v2_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    let d := 1 - (balabanBetaCoeff N_c - r_k) * β_k
    0 < d ∧ d < 1 := by
  simp only []
  constructor
  ·
    have hpos :
        0 < 1 - balabanBetaCoeff N_c * β_k + r_k * β_k :=
      balaban_coupling_step_denominator_pos_of_remainder_small_and_beta_window_mul
        N_c β_k r_k hβ hr hβ_window_mul
    have hrepr :
        1 - balabanBetaCoeff N_c * β_k + r_k * β_k =
          1 - (balabanBetaCoeff N_c - r_k) * β_k := by
      ring
    simpa [hrepr] using hpos
  ·
    have hlt :
        1 - balabanBetaCoeff N_c * β_k + r_k * β_k < 1 :=
      balaban_coupling_step_denominator_lt_one_of_remainder_small
        N_c β_k r_k hβ hr
    have hrepr :
        1 - balabanBetaCoeff N_c * β_k + r_k * β_k =
          1 - (balabanBetaCoeff N_c - r_k) * β_k := by
      ring
    simpa [hrepr] using hlt

/-- Asymptotic freedom from the clean multiplicative denominator-control window. -/
theorem asymptotic_freedom_from_denominator_control_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    β_k < balabanCouplingStep N_c β_k r_k := by
  exact
    asymptotic_freedom_implies_beta_growth_in_window_mul
      N_c β_k r_k hβ hr hβ_window_mul

end

end YangMills.ClayCore

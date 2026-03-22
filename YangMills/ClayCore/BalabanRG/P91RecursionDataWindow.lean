import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.P91DenominatorControlWindow

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# P91RecursionDataWindow

Core interface reroute for the analytic correction proved in
`BalabanCouplingRecursionWindow.lean`.

This file does not introduce a new hub.
It reroutes the `P91RecursionData` AF / rate-decrease layer so that its theorems
can now be invoked directly from the multiplicative weak-coupling window

  β * (3 * b₀) < 2

and, in this version, the reroute is carried by the clean denominator-control
window rather than by the legacy explicit upper-bound route

  β < 2 / b₀.
-/

/-- AF from data + clean multiplicative weak-coupling denominator-control window. -/
theorem af_of_data_in_window_mul
    {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < balabanCouplingStep N_c β_k r_k := by
  exact
    asymptotic_freedom_from_denominator_control_in_window_mul
      N_c β_k r_k hβ hr hβ_window_mul

/-- Rate decreases from data + clean multiplicative weak-coupling denominator-control window. -/
theorem rate_decreases_of_data_in_window_mul
    {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    physicalContractionRate (balabanCouplingStep N_c β_k r_k) < physicalContractionRate β_k := by
  exact
    contraction_rate_decreases_under_recursion_in_window_mul
      N_c β_k r_k hβ hr hβ_window_mul

end

end YangMills.ClayCore

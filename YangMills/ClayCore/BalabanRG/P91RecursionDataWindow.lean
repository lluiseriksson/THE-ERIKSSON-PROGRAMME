import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.CauchyDecayFromAFWindow

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

instead of the older explicit upper-bound interface

  β < 2 / b₀.
-/

/-- AF from data + multiplicative weak-coupling window. -/
theorem af_of_data_in_window_mul
    {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < balabanCouplingStep N_c β_k r_k := by
  exact
    af_of_data data k β_k r_k hβ
      (beta_upper_of_window_mul N_c β_k hβ_window_mul)
      hr

/-- Rate decreases from data + multiplicative weak-coupling window. -/
theorem rate_decreases_of_data_in_window_mul
    {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    physicalContractionRate (balabanCouplingStep N_c β_k r_k) < physicalContractionRate β_k := by
  exact
    rate_decreases_of_data data k β_k r_k hβ
      (beta_upper_of_window_mul N_c β_k hβ_window_mul)
      hr

end

end YangMills.ClayCore

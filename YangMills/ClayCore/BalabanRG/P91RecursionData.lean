import Mathlib
import YangMills.ClayCore.BalabanRG.P91WindowFromRecursion
import YangMills.ClayCore.BalabanRG.P91DenominatorControl

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91RecursionData — Layer 14B

Packages the P91 A.2 hypotheses.
p91_tight_window_of_data moved to P91WindowClosed (14K) to avoid cycle.
-/

noncomputable section

/-- The two quantitative P91 A.2 hypotheses. -/
structure P91RecursionData (N_c : ℕ) [NeZero N_c] where
  remainder_small :
    ∀ (k : ℕ) (β_k r_k : ℝ), 1 ≤ β_k →
      |r_k| ≤ remainderBoundConst / β_k
  remainder_window_small :
    ∀ (k : ℕ) (β_k r_k : ℝ), 1 ≤ β_k →
      |r_k| ≤ remainderBoundConst / β_k →
      remainderBoundConst < balabanBetaCoeff N_c * β_k *
        (1 - balabanBetaCoeff N_c * β_k) / β_k

/-- AF from data. -/
theorem af_of_data {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_upper : β_k < 2 / balabanBetaCoeff N_c)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < balabanCouplingStep N_c β_k r_k :=
  asymptotic_freedom_from_denominator_control N_c β_k r_k hβ hβ_upper hr
    (denominator_in_unit_interval_v2 N_c β_k r_k hβ hβ_upper hr)

/-- Rate decreases from data. -/
theorem rate_decreases_of_data {N_c : ℕ} [NeZero N_c]
    (data : P91RecursionData N_c)
    (k : ℕ) (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_upper : β_k < 2 / balabanBetaCoeff N_c)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    physicalContractionRate (balabanCouplingStep N_c β_k r_k)
      < physicalContractionRate β_k :=
  rate_decreases_with_beta β_k _
    (af_of_data data k β_k r_k hβ hβ_upper hr)

end

end YangMills.ClayCore

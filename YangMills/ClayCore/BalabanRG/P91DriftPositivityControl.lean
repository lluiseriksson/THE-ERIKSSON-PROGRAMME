import Mathlib
import YangMills.ClayCore.BalabanRG.P91OnestepDriftAlgebra
import YangMills.ClayCore.BalabanRG.P91DenominatorControl

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91DriftPositivityControl — Layer 14H

Proves coeff ≥ b₀/2 and denom ≤ 1. Both 0 sorrys.
These are the two physical triggers for `beta_step_drift_lb`.
-/

noncomputable section

/-- From |r_k| < b₀/2, the effective coefficient ≥ b₀/2. 0 sorrys. -/
theorem coeff_ge_half_betaCoeff (N_c : ℕ) [NeZero N_c]
    (r_k : ℝ) (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    balabanBetaCoeff N_c / 2 ≤ balabanBetaCoeff N_c - r_k := by
  have hr_right : r_k < balabanBetaCoeff N_c / 2 := (abs_lt.mp hr).2
  linarith

/-- betaStepDenom ≤ 1 always. 0 sorrys. -/
theorem denom_le_one_always (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    betaStepDenom N_c β_k r_k ≤ 1 := by
  unfold betaStepDenom
  have hr_right : r_k < balabanBetaCoeff N_c / 2 := (abs_lt.mp hr).2
  have hb0 : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have hcoeff : 0 < balabanBetaCoeff N_c - r_k := by linarith
  nlinarith [mul_pos hcoeff (by linarith : (0:ℝ) < β_k)]

/-- One-step drift ≥ b₀/2 from positivity controls. 0 sorrys. -/
theorem one_step_beta_drift_from_controls (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hden_pos : 0 < betaStepDenom N_c β_k r_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    balabanBetaCoeff N_c / 2 ≤ balabanCouplingStep N_c β_k r_k - β_k :=
  beta_step_drift_lb N_c β_k r_k (balabanBetaCoeff N_c / 2) hβ
    (coeff_ge_half_betaCoeff N_c r_k hr)
    (half_pos (balabanBetaCoeff_pos N_c))
    hden_pos
    (denom_le_one_always N_c β_k r_k hβ hr)

end

end YangMills.ClayCore

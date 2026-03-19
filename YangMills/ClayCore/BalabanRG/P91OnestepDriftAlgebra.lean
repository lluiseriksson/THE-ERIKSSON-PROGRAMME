import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanCouplingRecursion

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91OnestepDriftAlgebra — Layer 14G

Pure algebra for the one-step drift in P91 A.2.
No physics. No sorrys.

## Key identity

β_{k+1} - β_k = β_k² · (b₀ - r_k) / (1 - (b₀-r_k)·β_k)

This converts `one_step_beta_drift_P91` into:
  prove denom > 0 and coeff > 0
-/

noncomputable section

/-- The recursion denominator. -/
def betaStepDenom (N_c : ℕ) (β_k r_k : ℝ) : ℝ :=
  1 - (balabanBetaCoeff N_c - r_k) * β_k

/-- balabanCouplingStep in terms of betaStepDenom. -/
theorem balabanCouplingStep_eq_div_denom (N_c : ℕ) (β_k r_k : ℝ) :
    balabanCouplingStep N_c β_k r_k = β_k / betaStepDenom N_c β_k r_k := by
  unfold balabanCouplingStep betaStepDenom
  ring_nf

/-- Exact one-step drift identity:
    β_{k+1} - β_k = β_k² · (b₀-r_k) / denom. -/
theorem beta_step_sub_eq (N_c : ℕ) (β_k r_k : ℝ)
    (hden : betaStepDenom N_c β_k r_k ≠ 0) :
    balabanCouplingStep N_c β_k r_k - β_k
      = β_k ^ 2 * (balabanBetaCoeff N_c - r_k) / betaStepDenom N_c β_k r_k := by
  rw [balabanCouplingStep_eq_div_denom]
  field_simp [hden]
  unfold betaStepDenom
  ring

/-- If β_k>0, coeff>0, denom>0 → drift is positive. 0 sorrys. -/
theorem beta_step_sub_pos (N_c : ℕ) (β_k r_k : ℝ)
    (hβ : 0 < β_k)
    (hcoeff : 0 < balabanBetaCoeff N_c - r_k)
    (hden : 0 < betaStepDenom N_c β_k r_k) :
    0 < balabanCouplingStep N_c β_k r_k - β_k := by
  rw [beta_step_sub_eq N_c β_k r_k (ne_of_gt hden)]
  exact div_pos (mul_pos (by nlinarith) hcoeff) hden

/-- β_{k+1} > β_k under positivity. 0 sorrys. -/
theorem beta_step_gt_self (N_c : ℕ) (β_k r_k : ℝ)
    (hβ : 0 < β_k)
    (hcoeff : 0 < balabanBetaCoeff N_c - r_k)
    (hden : 0 < betaStepDenom N_c β_k r_k) :
    β_k < balabanCouplingStep N_c β_k r_k :=
  by linarith [beta_step_sub_pos N_c β_k r_k hβ hcoeff hden]

/-- Drift lower bound: if drift = β_k²·coeff/denom, and β_k≥1, coeff≥c, denom≤1,
    then drift ≥ c. 0 sorrys. -/
theorem beta_step_drift_lb (N_c : ℕ) (β_k r_k c : ℝ)
    (hβ : 1 ≤ β_k)
    (hcoeff : c ≤ balabanBetaCoeff N_c - r_k)
    (hc : 0 < c)
    (hden_pos : 0 < betaStepDenom N_c β_k r_k)
    (hden_lt1 : betaStepDenom N_c β_k r_k ≤ 1) :
    c ≤ balabanCouplingStep N_c β_k r_k - β_k := by
  rw [beta_step_sub_eq N_c β_k r_k (ne_of_gt hden_pos)]
  have hβ_sq_nn : 0 ≤ β_k ^ 2 := by nlinarith
  have hβ_sq_ge1 : 1 ≤ β_k ^ 2 := by nlinarith
  have hcoeff_pos : 0 < balabanBetaCoeff N_c - r_k := by linarith
  have hnum_nn : 0 ≤ β_k ^ 2 * (balabanBetaCoeff N_c - r_k) := by nlinarith
  have h1 : c ≤ β_k ^ 2 * c := by nlinarith
  have h2 : β_k ^ 2 * c ≤ β_k ^ 2 * (balabanBetaCoeff N_c - r_k) :=
    mul_le_mul_of_nonneg_left hcoeff hβ_sq_nn
  have hnum : c ≤ β_k ^ 2 * (balabanBetaCoeff N_c - r_k) := le_trans h1 h2
  calc c ≤ β_k ^ 2 * (balabanBetaCoeff N_c - r_k) := hnum
    _ = β_k ^ 2 * (balabanBetaCoeff N_c - r_k) / 1 := by ring
    _ ≤ β_k ^ 2 * (balabanBetaCoeff N_c - r_k) / betaStepDenom N_c β_k r_k :=
        div_le_div_of_nonneg_left hnum_nn hden_pos hden_lt1

end

end YangMills.ClayCore

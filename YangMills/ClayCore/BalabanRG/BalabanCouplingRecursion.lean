import Mathlib
import YangMills.ClayCore.BalabanRG.RGContractionRate

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# BalabanCouplingRecursion — Layer 13A

Formalizes the coupling constant recursion from P91 Appendix A.2.
This is the physical engine behind `cauchy_decay_P81_step2`.

## The recursion (P91 A.2)

  β_{k+1}⁻¹ = β_k⁻¹ - b₀ + r_k

where:
  β = 1/g² is the inverse coupling (weak coupling: β >> 1)
  b₀ = 11·N_c/(48·π²) > 0 is the one-loop beta function coefficient
  r_k are higher-loop remainder terms with |r_k| ≤ C·g²_k

In the weak-coupling regime, β grows monotonically:
  β_{k+1} > β_k  (asymptotic freedom)

This implies physicalContractionRate β_{k+1} < physicalContractionRate β_k:
  exp(-β_{k+1}) < exp(-β_k)

## Connection to cauchy_decay_P81_step2

If β_k → ∞ as k → ∞ (asymptotic freedom),
then physicalContractionRate β_k → 0, giving the contraction estimate.
-/

noncomputable section

/-- One-loop beta function coefficient for SU(N_c).
    b₀ = 11·N_c/(48·π²). Source: P91 A.2, standard QCD. -/
def balabanBetaCoeff (N_c : ℕ) : ℝ :=
  (11 * N_c : ℝ) / (48 * Real.pi ^ 2)

/-- b₀ > 0 for N_c ≥ 1. -/
private theorem Nc_pos_rec (N_c : ℕ) [NeZero N_c] : 0 < (N_c : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N_c))

theorem balabanBetaCoeff_pos (N_c : ℕ) [NeZero N_c] :
    0 < balabanBetaCoeff N_c := by
  unfold balabanBetaCoeff
  apply div_pos
  · have : 0 < (N_c : ℝ) := Nc_pos_rec N_c
    nlinarith
  · have : 0 < Real.pi := Real.pi_pos
    nlinarith [sq_nonneg Real.pi]

/-- The coupling recursion: β_{k+1}⁻¹ = β_k⁻¹ - b₀ + r_k.
    Equivalently: β_{k+1} = β_k / (1 - b₀·β_k + r_k·β_k). -/
def balabanCouplingStep (N_c : ℕ) (β_k r_k : ℝ) : ℝ :=
  β_k / (1 - balabanBetaCoeff N_c * β_k + r_k * β_k)

/-- Under asymptotic freedom (b₀ > 0, r_k small), β grows: β_{k+1} > β_k. -/
theorem asymptotic_freedom_implies_beta_growth (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
  (hβ_upper : 3 * balabanBetaCoeff N_c * β_k < 2)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    β_k < balabanCouplingStep N_c β_k r_k := by
  have hb_pos : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have hβ_pos : 0 < β_k := by linarith
  have hr_left : -(balabanBetaCoeff N_c / 2) < r_k := (abs_lt.mp hr).1
  have hr_right : r_k < balabanBetaCoeff N_c / 2 := (abs_lt.mp hr).2
  unfold balabanCouplingStep
  have hd_pos : (0 : ℝ) < 1 - balabanBetaCoeff N_c * β_k + r_k * β_k := by
    nlinarith [mul_pos (show (0:ℝ) < balabanBetaCoeff N_c / 2 + r_k from by linarith) hβ_pos]
  have hd_lt_one : 1 - balabanBetaCoeff N_c * β_k + r_k * β_k < 1 := by
    nlinarith [mul_pos hβ_pos (show (0:ℝ) < balabanBetaCoeff N_c - r_k from by linarith)]
  have key : β_k * (1 - balabanBetaCoeff N_c * β_k + r_k * β_k) < β_k := by
    have := mul_lt_mul_of_pos_left hd_lt_one hβ_pos; linarith [mul_one β_k]
  have hdinv : 0 < (1 - balabanBetaCoeff N_c * β_k + r_k * β_k)⁻¹ := inv_pos.mpr hd_pos
  have step : β_k * (1 - balabanBetaCoeff N_c * β_k + r_k * β_k) * (1 - balabanBetaCoeff N_c * β_k + r_k * β_k)⁻¹ < β_k * (1 - balabanBetaCoeff N_c * β_k + r_k * β_k)⁻¹ :=
    mul_lt_mul_of_pos_right key hdinv
  rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hd_pos), mul_one, ← div_eq_mul_inv] at step
  exact step

/-- Contraction rate decreases as β grows. -/
theorem rate_decreases_with_beta (β₁ β₂ : ℝ) (h : β₁ < β₂) :
    physicalContractionRate β₂ < physicalContractionRate β₁ := by
  unfold physicalContractionRate
  apply Real.exp_lt_exp.mpr
  linarith

/-- Under asymptotic freedom, contraction rate decreases at each step. -/
theorem contraction_rate_decreases_under_recursion (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
  (hβ_upper : 3 * balabanBetaCoeff N_c * β_k < 2)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    physicalContractionRate (balabanCouplingStep N_c β_k r_k)
      < physicalContractionRate β_k :=
  rate_decreases_with_beta β_k _
    (asymptotic_freedom_implies_beta_growth N_c β_k r_k hβ hβ_upper hr)

/-!
## Connection to cauchy_decay_P81_step2

The Cauchy decay theorem needs:
  ‖T_k(K₁) - T_k(K₂)‖ ≤ exp(-β_k) · ‖K₁ - K₂‖

Via the coupling recursion:
  β_k ≥ β_0 + k · (b₀/2) → ∞

So physicalContractionRate β_k = exp(-β_k) → 0, giving the contraction.

The sorry in cauchy_decay_P81_step2 is exactly:
  given C_uv from P82, use asymptotic freedom (this file) to refine to exp(-β).

Next step: connect `asymptotic_freedom_implies_beta_growth` to P81 §3.
-/

end

end YangMills.ClayCore

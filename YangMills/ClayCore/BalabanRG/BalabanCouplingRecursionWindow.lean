import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanCouplingRecursion

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
noncomputable section

/-!
# BalabanCouplingRecursionWindow

Analytic correction lane for the P91 Appendix A.2 coupling step.

The theorem in `BalabanCouplingRecursion.lean` isolates the qualitative mechanism
(asymptotic freedom should make `β` grow), but the raw step
  β_{k+1} = β_k / (1 - b₀ β_k + r_k β_k)
only behaves monotonically if the denominator stays in the weak-coupling window `(0,1)`.

To keep the proof stable under this toolchain, the window is stated in multiplicative form:
  β_k * (3 * b₀) < 2.

This is the same analytic content as β_k < 2 / (3 b₀), but avoids fragile quotient lemmas.
No new hub is introduced here.
-/

theorem balaban_coupling_step_denominator_lt_one_of_remainder_small
    (N_c : ℕ) [NeZero N_c] (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    1 - balabanBetaCoeff N_c * β_k + r_k * β_k < 1 := by
  have hb : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have hβpos : 0 < β_k := lt_of_lt_of_le zero_lt_one hβ
  have hr_upper : r_k < balabanBetaCoeff N_c / 2 := (abs_lt.mp hr).2
  nlinarith

theorem balaban_coupling_step_denominator_pos_of_remainder_small_and_beta_window_mul
    (N_c : ℕ) [NeZero N_c] (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    0 < 1 - balabanBetaCoeff N_c * β_k + r_k * β_k := by
  have hb : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
  have hβpos : 0 < β_k := lt_of_lt_of_le zero_lt_one hβ
  have hr_lower : -(balabanBetaCoeff N_c / 2) < r_k := (abs_lt.mp hr).1
  have hbase : 0 < 1 - balabanBetaCoeff N_c * β_k - (balabanBetaCoeff N_c / 2) * β_k := by
    nlinarith [hβ_window_mul]
  have hrem : -(balabanBetaCoeff N_c / 2) * β_k < r_k * β_k := by
    nlinarith
  nlinarith [hbase, hrem]

/-- Correct P91 A.2 monotonicity statement in the explicit weak-coupling window where the
denominator of the step map stays in `(0,1)`. Window stated in multiplicative form:
`β_k * (3 * b₀) < 2`. -/
theorem asymptotic_freedom_implies_beta_growth_in_window_mul
    (N_c : ℕ) [NeZero N_c] (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    β_k < balabanCouplingStep N_c β_k r_k := by
  have hβpos : 0 < β_k := lt_of_lt_of_le zero_lt_one hβ
  have hden_lt_one :
      1 - balabanBetaCoeff N_c * β_k + r_k * β_k < 1 :=
    balaban_coupling_step_denominator_lt_one_of_remainder_small N_c β_k r_k hβ hr
  have hden_pos :
      0 < 1 - balabanBetaCoeff N_c * β_k + r_k * β_k :=
    balaban_coupling_step_denominator_pos_of_remainder_small_and_beta_window_mul
      N_c β_k r_k hβ hr hβ_window_mul
  set d : ℝ := 1 - balabanBetaCoeff N_c * β_k + r_k * β_k with hd
  have hdpos : 0 < d := by
    simpa [d] using hden_pos
  have hdlt : d < 1 := by
    simpa [d] using hden_lt_one
  have h1md : 0 < 1 - d := by
    linarith
  have hrepr : β_k / d - β_k = β_k * (1 - d) / d := by
    have hne : d ≠ 0 := ne_of_gt hdpos
    field_simp [hne]
  have hdiff : 0 < β_k / d - β_k := by
    rw [hrepr]
    positivity
  have hgrow : β_k < β_k / d := by
    linarith
  unfold balabanCouplingStep
  simpa [d] using hgrow

/-- In the same weak-coupling window, the physical contraction rate decreases after one RG step. -/
theorem contraction_rate_decreases_under_recursion_in_window_mul
    (N_c : ℕ) [NeZero N_c] (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    physicalContractionRate (balabanCouplingStep N_c β_k r_k) < physicalContractionRate β_k := by
  exact
    rate_decreases_with_beta β_k _
      (asymptotic_freedom_implies_beta_growth_in_window_mul N_c β_k r_k hβ hr hβ_window_mul)

end

end YangMills.ClayCore

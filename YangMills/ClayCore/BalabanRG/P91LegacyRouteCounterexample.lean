import Mathlib
import YangMills.ClayCore.BalabanRG.P91DenominatorControlWindow

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

noncomputable section

/-!
# P91LegacyRouteCounterexample

This file does not introduce a new hub.
It certifies, by explicit example, that the legacy old-route P91 hypothesis

  β < 2 / b₀

is too weak to guarantee the denominator positivity statement it was meant to support.

The corrected window already used elsewhere in the repository is the multiplicative one

  β * (3 * b₀) < 2,

and this explicit counterexample lands exactly in the gap between those two hypothesis packages.
-/

private theorem b0_one_pos : 0 < balabanBetaCoeff 1 := by
  exact balabanBetaCoeff_pos 1

private theorem b0_one_lt_one : balabanBetaCoeff 1 < 1 := by
  unfold balabanBetaCoeff
  have hbig : (11 : ℝ) < 48 * Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hdiv :
      (11 : ℝ) / (48 * Real.pi ^ 2) < (48 * Real.pi ^ 2) / (48 * Real.pi ^ 2) := by
    gcongr
  have hone : (48 * Real.pi ^ 2) / (48 * Real.pi ^ 2) = (1 : ℝ) := by
    field_simp [show (48 * Real.pi ^ 2) ≠ 0 by positivity]
  simpa [hone] using hdiv

/-- Explicit counterexample to the legacy old-route denominator positivity package. -/
theorem legacy_old_route_denominator_counterexample :
    let b0 := balabanBetaCoeff 1
    let β_k : ℝ := 3 / (2 * b0)
    let r_k : ℝ := -(b0 / 4)
    1 ≤ β_k ∧
    β_k < 2 / b0 ∧
    |r_k| < b0 / 2 ∧
    ¬ (0 < 1 - (b0 - r_k) * β_k) := by
  dsimp
  have hb0_pos : 0 < balabanBetaCoeff 1 := b0_one_pos
  have hb0_lt_one : balabanBetaCoeff 1 < 1 := b0_one_lt_one

  have hβ0 : 1 ≤ 3 / (2 * balabanBetaCoeff 1) := by
    have hineq : 2 * balabanBetaCoeff 1 ≤ 3 := by
      nlinarith [hb0_lt_one]
    field_simp [hb0_pos.ne']
    nlinarith

  have hβ_upper_legacy : 3 / (2 * balabanBetaCoeff 1) < 2 / balabanBetaCoeff 1 := by
    field_simp [hb0_pos.ne']
    nlinarith

  have hr_small : |-(balabanBetaCoeff 1 / 4)| < balabanBetaCoeff 1 / 2 := by
    rw [abs_neg, abs_of_pos]
    · nlinarith
    · positivity

  have hrepr :
      1 - (balabanBetaCoeff 1 - (-(balabanBetaCoeff 1 / 4))) *
            (3 / (2 * balabanBetaCoeff 1))
        = (-7 : ℝ) / 8 := by
    field_simp [hb0_pos.ne']
    ring

  refine ⟨hβ0, hβ_upper_legacy, hr_small, ?_⟩
  rw [hrepr]
  norm_num

/-- The same explicit point is excluded by the corrected multiplicative weak-coupling
window used in the green P91 files. -/
theorem legacy_counterexample_fails_corrected_window :
    let b0 := balabanBetaCoeff 1
    let β_k : ℝ := 3 / (2 * b0)
    ¬ β_k * ((3 : ℝ) * b0) < 2 := by
  dsimp
  have hb0_pos : 0 < balabanBetaCoeff 1 := b0_one_pos
  have hcalc :
      (3 / (2 * balabanBetaCoeff 1)) * ((3 : ℝ) * balabanBetaCoeff 1) = 9 / 2 := by
    field_simp [hb0_pos.ne']
    ring
  rw [hcalc]
  norm_num

/-- Audit corollary: the corrected multiplicative window is strictly stronger than the
legacy old-route upper bound at the explicit counterexample point. -/
theorem corrected_window_avoids_the_legacy_gap :
    let b0 := balabanBetaCoeff 1
    let β_k : ℝ := 3 / (2 * b0)
    β_k < 2 / b0 ∧ ¬ β_k * ((3 : ℝ) * b0) < 2 := by
  dsimp
  have hb0_pos : 0 < balabanBetaCoeff 1 := b0_one_pos
  have hlegacy : 3 / (2 * balabanBetaCoeff 1) < 2 / balabanBetaCoeff 1 := by
    field_simp [hb0_pos.ne']
    nlinarith
  exact ⟨hlegacy, legacy_counterexample_fails_corrected_window⟩

end

end YangMills.ClayCore

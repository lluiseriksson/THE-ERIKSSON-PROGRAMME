/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L30_CreativeAttack_Robustness.NonTriviality_Robust

/-!
# Parametric robustness theorem (Phase 288)

A fully parametric statement: SU(2) non-triviality holds for ANY
admissible bounds, ranging over a continuous family.

## Strategic placement

This is **Phase 288** of the L30_CreativeAttack_Robustness block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L30_CreativeAttack_Robustness

/-! ## §1. Parametric statement -/

/-- **Parametric robustness**: for every pair of positive bounds
    `(γ_lower, C_upper)` and every `g²` strictly below the threshold
    `γ_lower/C_upper`, the robust 4-point lower bound is positive. -/
theorem parametric_robustness :
    ∀ (γ_lower C_upper g : ℝ),
      0 < γ_lower → 0 < C_upper → 0 < g ^ 2 →
      g ^ 2 < γ_lower / C_upper →
      0 < g ^ 2 * γ_lower - g ^ 4 * C_upper := by
  intro γ_lower C_upper g hγ hC hgsq h_below
  have h_eqv : g ^ 2 < Robust_SU2_Threshold γ_lower C_upper := h_below
  have := robust_SU2_nonTriviality γ_lower C_upper g hγ hC hgsq h_eqv
  exact this

#print axioms parametric_robustness

/-! ## §2. Existence of a robust witness for any bounds -/

/-- **For ANY positive `(γ, C)`, a witness coupling `g` exists**.

    Specifically: choose `g² = γ/(2C)` which is half the threshold. -/
theorem witness_exists_for_any_bounds
    (γ C : ℝ) (hγ : 0 < γ) (hC : 0 < C) :
    ∃ g : ℝ, 0 < g ^ 2 ∧ g ^ 2 < γ / C ∧
      0 < g ^ 2 * γ - g ^ 4 * C := by
  refine ⟨Real.sqrt (γ / (2 * C)), ?_, ?_, ?_⟩
  · -- g² > 0
    have h_div_pos : 0 < γ / (2 * C) := div_pos hγ (by linarith)
    rw [Real.sq_sqrt h_div_pos.le]
    exact h_div_pos
  · -- g² < γ/C
    have h_div_pos : 0 < γ / (2 * C) := div_pos hγ (by linarith)
    rw [Real.sq_sqrt h_div_pos.le]
    rw [lt_div_iff hC]
    rw [div_mul_eq_mul_div, lt_div_iff (by linarith : (0:ℝ) < 2*C)]
    nlinarith
  · -- 0 < g²·γ - g⁴·C
    have h_div_pos : 0 < γ / (2 * C) := div_pos hγ (by linarith)
    have h_sqrt_sq : (Real.sqrt (γ / (2 * C)))^2 = γ / (2 * C) :=
      Real.sq_sqrt h_div_pos.le
    apply parametric_robustness _ _ _ hγ hC
    · rw [h_sqrt_sq]; exact h_div_pos
    · rw [h_sqrt_sq]
      rw [lt_div_iff hC]
      rw [div_mul_eq_mul_div, lt_div_iff (by linarith : (0:ℝ) < 2*C)]
      nlinarith

#print axioms witness_exists_for_any_bounds

end YangMills.L30_CreativeAttack_Robustness

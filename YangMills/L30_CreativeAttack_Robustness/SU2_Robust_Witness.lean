/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L30_CreativeAttack_Robustness.NonTriviality_Robust
import YangMills.L30_CreativeAttack_Robustness.SU2_C_UpperBoundsList
import YangMills.L30_CreativeAttack_Robustness.SU2_GammaLowerBoundsList

/-!
# SU(2) robust non-triviality witness (Phase 287)

**Concrete witnesses** combining specific upper/lower bounds.

## Strategic placement

This is **Phase 287** of the L30_CreativeAttack_Robustness block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L30_CreativeAttack_Robustness

/-! ## §1. Witness pair: Casimir² γ + trivial C -/

/-- **The most powerful witness pair**: `γ_lower = 9/16` (Casimir²)
    and `C_upper = 1` (trivial). -/
def witnessPair_strongest : (ℝ × ℝ) :=
  (gamma_lower_Casimir_squared, C_upper_trivial)

/-- **Threshold for the strongest witness pair**: `9/16 / 1 = 9/16`.

    This is **much wider** than the placeholder threshold `1/64`. -/
theorem witnessPair_strongest_threshold :
    Robust_SU2_Threshold witnessPair_strongest.1 witnessPair_strongest.2
      = 9 / 16 := by
  unfold witnessPair_strongest gamma_lower_Casimir_squared C_upper_trivial
         Robust_SU2_Threshold
  norm_num

#print axioms witnessPair_strongest_threshold

/-! ## §2. The strongest witness: g = 1/2 -/

/-- **For the strongest witness pair, `g_strong = 1/2` is below the
    threshold `9/16`**.

    Specifically: `(1/2)² = 1/4 = 4/16 < 9/16 = threshold`. -/
def g_strongest_witness : ℝ := 1 / 2

theorem g_strongest_witness_sq : g_strongest_witness ^ 2 = 1 / 4 := by
  unfold g_strongest_witness; norm_num

theorem g_strongest_below_threshold :
    g_strongest_witness ^ 2 <
      Robust_SU2_Threshold witnessPair_strongest.1 witnessPair_strongest.2 := by
  rw [g_strongest_witness_sq, witnessPair_strongest_threshold]
  norm_num

#print axioms g_strongest_below_threshold

/-! ## §3. The robust SU(2) non-triviality at the strongest witness -/

/-- **THE KEY ROBUST RESULT**: SU(2) is non-trivial at `g = 1/2` IF
    we have any pair of bounds with `γ_lower ≥ 9/16` and
    `C_upper ≤ 1`. The placeholder values from L20 are FAR too
    conservative — much wider thresholds work. -/
theorem SU2_robust_nonTriviality_at_g_half :
    0 < Robust_SU2_S4_LowerBound
      witnessPair_strongest.1 witnessPair_strongest.2
      g_strongest_witness := by
  apply robust_SU2_nonTriviality
  · exact gamma_lower_Casimir_squared_pos
  · exact C_upper_trivial_pos
  · rw [g_strongest_witness_sq]; norm_num
  · exact g_strongest_below_threshold

#print axioms SU2_robust_nonTriviality_at_g_half

/-! ## §4. Comparison to L20 placeholder result -/

/-- **The robust threshold is 36 times the placeholder threshold**:
    `9/16 = 36 · (1/64)`. -/
theorem robust_threshold_dominates_placeholder :
    Robust_SU2_Threshold gamma_lower_Casimir_squared C_upper_trivial =
      36 * (1 / 64) := by
  unfold gamma_lower_Casimir_squared C_upper_trivial Robust_SU2_Threshold
  norm_num

#print axioms robust_threshold_dominates_placeholder

end YangMills.L30_CreativeAttack_Robustness

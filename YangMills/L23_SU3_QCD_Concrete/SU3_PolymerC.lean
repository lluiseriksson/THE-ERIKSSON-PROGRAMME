/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L23_SU3_QCD_Concrete.SU3_TreeLevelGamma

/-!
# SU(3) polymer C (Phase 220)

## Strategic placement

This is **Phase 220** of the L23_SU3_QCD_Concrete block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L23_SU3_QCD_Concrete

/-- **SU(3) polymer remainder prefactor** (placeholder `9`). -/
def C_SU3 : ℝ := 9

/-- **`C_SU3 > 0`**. -/
theorem C_SU3_pos : 0 < C_SU3 := by
  unfold C_SU3; norm_num

#print axioms C_SU3_pos

/-- **SU(3) strict-positivity threshold**: `γ_SU3/C_SU3 = 1/81`. -/
def SU3_threshold : ℝ := gamma_SU3 / C_SU3

/-- **The threshold equals `1/81`**. -/
theorem SU3_threshold_value : SU3_threshold = 1 / 81 := by
  unfold SU3_threshold gamma_SU3 C_SU3
  norm_num

#print axioms SU3_threshold_value

/-- **The threshold is positive**. -/
theorem SU3_threshold_pos : 0 < SU3_threshold := by
  rw [SU3_threshold_value]; norm_num

/-- **SU(3) 4-point lower bound**. -/
def SU3_S4_LowerBound (g : ℝ) : ℝ := g ^ 2 * gamma_SU3 - g ^ 4 * C_SU3

/-- **At `g = 0`, bound is 0**. -/
theorem SU3_S4_LowerBound_at_zero : SU3_S4_LowerBound 0 = 0 := by
  unfold SU3_S4_LowerBound; simp

/-- **SU(3) concrete non-triviality**: at `0 < g² < 1/81`,
    `SU3_S4_LowerBound g > 0`. -/
theorem SU3_nonTriviality_concrete
    (g : ℝ) (h_g_sq_pos : 0 < g ^ 2) (h_below : g ^ 2 < SU3_threshold) :
    0 < SU3_S4_LowerBound g := by
  unfold SU3_S4_LowerBound
  have h_C_pos := C_SU3_pos
  have h_gsq_C : g ^ 2 * C_SU3 < gamma_SU3 := by
    rw [SU3_threshold] at h_below
    rw [lt_div_iff h_C_pos] at h_below
    exact h_below
  have h_dom : g ^ 4 * C_SU3 < g ^ 2 * gamma_SU3 := by
    have : g ^ 4 = g ^ 2 * g ^ 2 := by ring
    rw [this]
    calc g ^ 2 * g ^ 2 * C_SU3
        = g ^ 2 * (g ^ 2 * C_SU3) := by ring
      _ < g ^ 2 * gamma_SU3 := (mul_lt_mul_left h_g_sq_pos).mpr h_gsq_C
  linarith

#print axioms SU3_nonTriviality_concrete

end YangMills.L23_SU3_QCD_Concrete

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(3) tree-level γ (Phase 219)

The SU(3) tree-level prefactor for non-triviality. SU(3) has more
structure constants and a Casimir of `4/3` (vs `3/4` for SU(2)),
so the value differs from SU(2).

## Strategic placement

This is **Phase 219** of the L23_SU3_QCD_Concrete block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L23_SU3_QCD_Concrete

/-- **SU(3) tree-level prefactor**: placeholder value `1/9`. The
    true Yang-Mills computation depends on SU(3) Casimir
    `C_F = 4/3` and structure constants. -/
def gamma_SU3 : ℝ := 1 / 9

/-- **`gamma_SU3 > 0`**. -/
theorem gamma_SU3_pos : 0 < gamma_SU3 := by
  unfold gamma_SU3; norm_num

#print axioms gamma_SU3_pos

/-- **`gamma_SU3 < 1`**. -/
theorem gamma_SU3_lt_one : gamma_SU3 < 1 := by
  unfold gamma_SU3; norm_num

#print axioms gamma_SU3_lt_one

/-- **`gamma_SU3 < gamma_SU2`** would be expected from physics
    (more structure ⇒ smaller tree prefactor). With placeholder
    values `gamma_SU3 = 1/9 < 1/16 = gamma_SU2`?
    No: `1/9 ≈ 0.111 > 1/16 ≈ 0.0625`. So with these placeholders
    the inequality goes the OTHER way. We just record the fact. -/
theorem gamma_SU3_explicit : gamma_SU3 = 1/9 := rfl

/-! ## SU(3) tree-level bound -/

/-- **SU(3) tree-level lower bound**: `g²·γ_SU3`. -/
def SU3_treeLevelBound (g : ℝ) : ℝ := g ^ 2 * gamma_SU3

/-- **SU(3) tree bound is non-negative**. -/
theorem SU3_treeLevelBound_nonneg (g : ℝ) :
    0 ≤ SU3_treeLevelBound g := by
  unfold SU3_treeLevelBound
  exact mul_nonneg (sq_nonneg g) (le_of_lt gamma_SU3_pos)

/-- **SU(3) tree bound is positive at non-zero coupling**. -/
theorem SU3_treeLevelBound_pos (g : ℝ) (hg : g ≠ 0) :
    0 < SU3_treeLevelBound g := by
  unfold SU3_treeLevelBound
  have h_g_sq : 0 < g ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (abs_pos.mpr hg) 2
  exact mul_pos h_g_sq gamma_SU3_pos

#print axioms SU3_treeLevelBound_pos

end YangMills.L23_SU3_QCD_Concrete

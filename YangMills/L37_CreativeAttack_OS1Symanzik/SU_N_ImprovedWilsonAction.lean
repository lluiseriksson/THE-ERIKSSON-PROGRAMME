/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L37_CreativeAttack_OS1Symanzik.SU_N_FirstOrderArtifact
import YangMills.L37_CreativeAttack_OS1Symanzik.SU_N_SymanzikCounterTerm

/-!
# SU(N) improved Wilson action (Phase 358)

The improved action with cancelled `O(a²)` artifact.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L37_CreativeAttack_OS1Symanzik

/-! ## §1. Improved action's `a²` coefficient -/

/-- **Improved action's `a²` coefficient**: artifact + counter
    cancel, giving exactly zero. -/
def SU_N_Improved_a2 (N : ℕ) : ℝ :=
  SU_N_FirstArtifact N + SU_N_SymanzikCounter N

theorem SU_N_Improved_a2_zero (N : ℕ) :
    SU_N_Improved_a2 N = 0 := SU_N_artifact_counter_cancel N

#print axioms SU_N_Improved_a2_zero

/-! ## §2. Residual `a⁴` coefficient -/

/-- **Residual `a⁴` coefficient after improvement**: the next-order
    correction. Placeholder value `N/360`. -/
def SU_N_Improved_a4_residual (N : ℕ) : ℝ := (N : ℝ) / 360

theorem SU_N_Improved_a4_residual_pos (N : ℕ) (hN : 1 ≤ N) :
    0 < SU_N_Improved_a4_residual N := by
  unfold SU_N_Improved_a4_residual
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- **Residual is much smaller than the cancelled artifact**:
    `N/360 < N/24` for `N ≥ 1`. -/
theorem SU_N_Improved_residual_lt_artifact (N : ℕ) (hN : 1 ≤ N) :
    SU_N_Improved_a4_residual N < (N : ℝ) / 24 := by
  unfold SU_N_Improved_a4_residual
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_lt_div_iff (by norm_num : (0:ℝ) < 360) (by norm_num : (0:ℝ) < 24)]
  linarith

#print axioms SU_N_Improved_residual_lt_artifact

end YangMills.L37_CreativeAttack_OS1Symanzik

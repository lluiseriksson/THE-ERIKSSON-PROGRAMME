/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(N) one-loop matching (Phase 357)

One-loop matching condition for the Symanzik improvement.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L37_CreativeAttack_OS1Symanzik

/-! ## §1. One-loop matching coefficient -/

/-- **SU(N) one-loop Symanzik coefficient**: at one-loop,
    `c_W^{1-loop}(N) = c_0(N) + c_1 · g²` for explicit constants.
    Tree-level: `c_0(N) = 1` (Sheikholeslami-Wohlert). -/
def SU_N_treeLevel_c_SW : ℝ := 1

theorem SU_N_treeLevel_c_SW_value : SU_N_treeLevel_c_SW = 1 := rfl

/-- **One-loop correction coefficient** (placeholder, depends on N). -/
def SU_N_oneLoop_c_1 (N : ℕ) : ℝ := (N : ℝ) / 16

theorem SU_N_oneLoop_c_1_pos (N : ℕ) (hN : 1 ≤ N) :
    0 < SU_N_oneLoop_c_1 N := by
  unfold SU_N_oneLoop_c_1
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

#print axioms SU_N_oneLoop_c_1_pos

/-! ## §2. Combined one-loop coefficient -/

/-- **Combined one-loop coefficient**: `c_SW^{tree} + g² · c_1(N)`. -/
def SU_N_combined_c_SW (N : ℕ) (g : ℝ) : ℝ :=
  SU_N_treeLevel_c_SW + g ^ 2 * SU_N_oneLoop_c_1 N

/-- **At zero coupling, equals tree-level**. -/
theorem SU_N_combined_c_SW_at_zero (N : ℕ) :
    SU_N_combined_c_SW N 0 = SU_N_treeLevel_c_SW := by
  unfold SU_N_combined_c_SW; simp

/-- **For `g ≥ 0` and `N ≥ 1`, the combined coefficient is positive**. -/
theorem SU_N_combined_c_SW_pos (N : ℕ) (g : ℝ) (hN : 1 ≤ N) :
    0 < SU_N_combined_c_SW N g := by
  unfold SU_N_combined_c_SW SU_N_treeLevel_c_SW
  have h_g2 : 0 ≤ g ^ 2 := sq_nonneg g
  have h_c1 : 0 < SU_N_oneLoop_c_1 N := SU_N_oneLoop_c_1_pos N hN
  nlinarith

#print axioms SU_N_combined_c_SW_pos

end YangMills.L37_CreativeAttack_OS1Symanzik

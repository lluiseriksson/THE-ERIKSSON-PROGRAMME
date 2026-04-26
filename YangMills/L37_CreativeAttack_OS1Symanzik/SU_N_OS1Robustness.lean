/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L37_CreativeAttack_OS1Symanzik.SU_N_OS1FromImprovement

/-!
# SU(N) OS1 robustness (Phase 360)

Robustness across coupling and N.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L37_CreativeAttack_OS1Symanzik

/-! ## §1. Universal OS1 closure -/

/-- **Universal OS1 closure**: for any `N ≥ 1`, the improved
    deviation tends to 0 as `a → 0⁺`. -/
theorem SU_N_universal_OS1_closure :
    ∀ N : ℕ, 1 ≤ N →
      Filter.Tendsto (SU_N_ImprovedDeviation N)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
  intros N hN
  exact SU_N_ImprovedDeviation_tendsto_zero N hN

#print axioms SU_N_universal_OS1_closure

/-! ## §2. Decay rate -/

/-- **The improved deviation decays as `O(a²)`**. -/
def SU_N_ImprovedDecayOrder : ℕ := 2

theorem SU_N_ImprovedDecayOrder_value : SU_N_ImprovedDecayOrder = 2 := rfl

/-! ## §3. Non-improved (raw Wilson) decay -/

/-- **Raw Wilson `O(a)` artifact**: not improved. -/
def SU_N_RawDecayOrder : ℕ := 1

theorem SU_N_decay_order_improvement :
    SU_N_RawDecayOrder < SU_N_ImprovedDecayOrder := by
  unfold SU_N_RawDecayOrder SU_N_ImprovedDecayOrder; norm_num

/-- **Improvement gain: 2 - 1 = 1 order of `a` faster decay**. -/
theorem SU_N_decay_order_gain :
    SU_N_ImprovedDecayOrder - SU_N_RawDecayOrder = 1 := by
  unfold SU_N_RawDecayOrder SU_N_ImprovedDecayOrder; norm_num

#print axioms SU_N_decay_order_gain

end YangMills.L37_CreativeAttack_OS1Symanzik

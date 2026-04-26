/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L37_CreativeAttack_OS1Symanzik.SU_N_FirstOrderArtifact

/-!
# SU(N) Symanzik counter-term (Phase 356)

The counter-term that cancels the first-order artifact.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L37_CreativeAttack_OS1Symanzik

/-! ## §1. Symanzik counter-term -/

/-- **SU(N) Symanzik counter-term coefficient**: `-N/24`,
    cancels `SU_N_FirstArtifact = N/24`. -/
def SU_N_SymanzikCounter (N : ℕ) : ℝ := -((N : ℝ) / 24)

/-- **Cancellation: `artifact + counter = 0`**. -/
theorem SU_N_artifact_counter_cancel (N : ℕ) :
    SU_N_FirstArtifact N + SU_N_SymanzikCounter N = 0 := by
  rw [SU_N_FirstArtifact_value]
  unfold SU_N_SymanzikCounter
  ring

#print axioms SU_N_artifact_counter_cancel

/-! ## §2. Counter-term sign -/

/-- **Counter is negative** (subtractive). -/
theorem SU_N_SymanzikCounter_neg (N : ℕ) (hN : 1 ≤ N) :
    SU_N_SymanzikCounter N < 0 := by
  unfold SU_N_SymanzikCounter
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  linarith [div_pos hN_pos (by norm_num : (0:ℝ) < 24)]

#print axioms SU_N_SymanzikCounter_neg

/-! ## §3. Concrete counter-terms -/

/-- **SU(2) counter: `-1/12`**. -/
theorem SU2_SymanzikCounter :
    SU_N_SymanzikCounter 2 = -(1/12) := by
  unfold SU_N_SymanzikCounter; norm_num

/-- **SU(3) counter: `-1/8`**. -/
theorem SU3_SymanzikCounter :
    SU_N_SymanzikCounter 3 = -(1/8) := by
  unfold SU_N_SymanzikCounter; norm_num

#print axioms SU3_SymanzikCounter

end YangMills.L37_CreativeAttack_OS1Symanzik

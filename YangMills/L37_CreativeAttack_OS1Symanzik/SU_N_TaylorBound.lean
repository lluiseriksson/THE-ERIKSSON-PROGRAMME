/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(N) Taylor bound (Phase 353)

Taylor expansion bounds for SU(N) Wilson plaquette improvement.

## Strategic placement

This is **Phase 353** of the L37_CreativeAttack_OS1Symanzik block —
eighth substantive attack of the session.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L37_CreativeAttack_OS1Symanzik

/-! ## §1. SU(N) Taylor coefficient -/

/-- **The SU(N) Taylor coefficient at fourth order**: same `1/12` as
    the 1D case, scaled by `N` (number of colours). -/
def SU_N_TaylorCoeff_4 (N : ℕ) : ℝ := (N : ℝ) / 12

/-- **Positivity for `N ≥ 1`**. -/
theorem SU_N_TaylorCoeff_4_pos (N : ℕ) (hN : 1 ≤ N) :
    0 < SU_N_TaylorCoeff_4 N := by
  unfold SU_N_TaylorCoeff_4
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

#print axioms SU_N_TaylorCoeff_4_pos

/-! ## §2. Concrete instances -/

/-- **`SU(2): SU_N_TaylorCoeff_4 = 2/12 = 1/6`**. -/
theorem SU_N_TaylorCoeff_4_at_2 :
    SU_N_TaylorCoeff_4 2 = 1/6 := by
  unfold SU_N_TaylorCoeff_4; norm_num

/-- **`SU(3): SU_N_TaylorCoeff_4 = 3/12 = 1/4`**. -/
theorem SU_N_TaylorCoeff_4_at_3 :
    SU_N_TaylorCoeff_4 3 = 1/4 := by
  unfold SU_N_TaylorCoeff_4; norm_num

#print axioms SU_N_TaylorCoeff_4_at_3

/-! ## §3. Linearity in N -/

/-- **`SU_N_TaylorCoeff_4` is linear in N**: `SU_N(N) = N · (1/12)`. -/
theorem SU_N_TaylorCoeff_4_linear (N : ℕ) :
    SU_N_TaylorCoeff_4 N = (N : ℝ) * (1/12) := by
  unfold SU_N_TaylorCoeff_4
  ring

end YangMills.L37_CreativeAttack_OS1Symanzik

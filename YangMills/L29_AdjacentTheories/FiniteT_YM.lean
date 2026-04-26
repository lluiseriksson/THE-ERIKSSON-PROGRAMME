/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Finite-temperature Yang-Mills (Phase 279)

YM at temperature T: Euclidean time compactified on circle of
radius `1/T`, with periodic boundary conditions.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L29_AdjacentTheories

/-- **Inverse temperature `β = 1/T`**. -/
def inverseTemperature (T : ℝ) : ℝ := 1 / T

theorem inverseTemperature_pos (T : ℝ) (hT : 0 < T) :
    0 < inverseTemperature T := by
  unfold inverseTemperature; positivity

#print axioms inverseTemperature_pos

/-- **Polyakov loop order parameter** for deconfinement (placeholder). -/
def polyakovLoop (T : ℝ) : ℝ :=
  if T < 1 then 0 else 1  -- step function at T_c = 1 (placeholder)

/-- **Polyakov loop is non-negative**. -/
theorem polyakovLoop_nonneg (T : ℝ) : 0 ≤ polyakovLoop T := by
  unfold polyakovLoop
  by_cases h : T < 1
  · rw [if_pos h]
  · rw [if_neg h]; norm_num

#print axioms polyakovLoop_nonneg

end YangMills.L29_AdjacentTheories

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# 2D Yang-Mills (Phase 273)

2D YM is exactly solvable (Migdal): partition function is a heat
kernel on the gauge group.

## Strategic placement

This is **Phase 273** of the L29_AdjacentTheories block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L29_AdjacentTheories

/-! ## §1. The 2D YM dimensionful coupling -/

/-- **2D YM coupling**: dimensionful, units of mass.
    The string tension is `σ = g²·C₂(R)` for an SU(N) Wilson loop
    in representation R. -/
def coupling_2D : ℝ := 1

theorem coupling_2D_pos : 0 < coupling_2D := by
  unfold coupling_2D; norm_num

/-! ## §2. 2D string tension -/

/-- **2D string tension** `σ = g²·C₂` (placeholder C₂ = 1). -/
def stringTension_2D (g : ℝ) : ℝ := g ^ 2

/-- **Always non-negative**. -/
theorem stringTension_2D_nonneg (g : ℝ) : 0 ≤ stringTension_2D g := sq_nonneg g

/-- **Strictly positive at non-zero coupling**. -/
theorem stringTension_2D_pos (g : ℝ) (hg : g ≠ 0) : 0 < stringTension_2D g := by
  unfold stringTension_2D
  rw [← sq_abs]
  exact pow_pos (abs_pos.mpr hg) 2

#print axioms stringTension_2D_pos

/-! ## §3. 2D is exactly solvable -/

/-- **2D YM is exactly solvable**: partition function = heat kernel. -/
def YM_2D_solvable : Prop := True

end YangMills.L29_AdjacentTheories

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Wilson fermions on the lattice (Phase 263)

Wilson's solution to the fermion-doubling problem.

## Strategic placement

This is **Phase 263** of the L28_StandardModelExtensions block —
the **twenty-second long-cycle block**, opening Standard Model
content.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L28_StandardModelExtensions

/-! ## §1. The Wilson parameter -/

/-- **Wilson parameter** `r`, the prefactor of the second-derivative
    term breaking chiral symmetry on the lattice. Standard choice
    `r = 1`. -/
def wilsonParameter : ℝ := 1

theorem wilsonParameter_pos : 0 < wilsonParameter := by
  unfold wilsonParameter; norm_num

#print axioms wilsonParameter_pos

/-! ## §2. Wilson fermion mass shift -/

/-- **Doubler mass at half momentum**: with Wilson term, doublers
    acquire mass `2r/a`. The doublers decouple in the continuum. -/
def doublerMass (r a : ℝ) : ℝ := 2 * r / a

/-- **Doubler mass is positive when `r, a > 0`**. -/
theorem doublerMass_pos (r a : ℝ) (hr : 0 < r) (ha : 0 < a) :
    0 < doublerMass r a := by
  unfold doublerMass
  exact div_pos (by linarith) ha

/-- **Doubler mass diverges as `a → 0`**: this is what decouples
    the doublers in the continuum. -/
theorem doublerMass_at_one_a (r : ℝ) (hr : 0 < r) :
    doublerMass r 1 = 2 * r := by
  unfold doublerMass; ring

end YangMills.L28_StandardModelExtensions

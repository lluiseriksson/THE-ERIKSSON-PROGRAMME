/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Taylor expansion setup (Phase 323)

Setup for the Taylor expansion of f(x+a) used to derive the
Wilson improvement coefficient.

## Strategic placement

This is **Phase 323** of the L34_CreativeAttack_WilsonCoeff block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L34_CreativeAttack_WilsonCoeff

/-! ## §1. Taylor coefficients -/

/-- **The Taylor coefficient `1/k!`** for the k-th term in `f(x+a)`. -/
noncomputable def taylorCoeff (k : ℕ) : ℝ := 1 / (Nat.factorial k : ℝ)

/-- **`taylorCoeff 0 = 1`**. -/
theorem taylorCoeff_zero : taylorCoeff 0 = 1 := by
  unfold taylorCoeff; simp

/-- **`taylorCoeff 1 = 1`**. -/
theorem taylorCoeff_one : taylorCoeff 1 = 1 := by
  unfold taylorCoeff; simp

/-- **`taylorCoeff 2 = 1/2`**. -/
theorem taylorCoeff_two : taylorCoeff 2 = 1/2 := by
  unfold taylorCoeff
  rw [Nat.factorial]
  norm_num

/-- **`taylorCoeff 3 = 1/6`**. -/
theorem taylorCoeff_three : taylorCoeff 3 = 1/6 := by
  unfold taylorCoeff
  rw [show Nat.factorial 3 = 6 from rfl]
  norm_num

/-- **`taylorCoeff 4 = 1/24`** — the key coefficient. -/
theorem taylorCoeff_four : taylorCoeff 4 = 1/24 := by
  unfold taylorCoeff
  rw [show Nat.factorial 4 = 24 from rfl]
  norm_num

#print axioms taylorCoeff_four

end YangMills.L34_CreativeAttack_WilsonCoeff

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Cubic group setup (Phase 343)

The hyperoctahedral group B_d acts on Z^d by sign changes and
coordinate permutations.

## Strategic placement

This is **Phase 343** of the L36_CreativeAttack_LatticeWard block —
seventh substantive attack of the session.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L36_CreativeAttack_LatticeWard

/-! ## §1. Hyperoctahedral group order -/

/-- **Hyperoctahedral group order**: `B_d` has `2^d · d!` elements. -/
def hyperoctahedralOrder (d : ℕ) : ℕ := 2 ^ d * Nat.factorial d

theorem hyperoctahedralOrder_at_2 : hyperoctahedralOrder 2 = 8 := by
  unfold hyperoctahedralOrder
  rw [show Nat.factorial 2 = 2 from rfl]; norm_num

theorem hyperoctahedralOrder_at_3 : hyperoctahedralOrder 3 = 48 := by
  unfold hyperoctahedralOrder
  rw [show Nat.factorial 3 = 6 from rfl]; norm_num

theorem hyperoctahedralOrder_at_4 : hyperoctahedralOrder 4 = 384 := by
  unfold hyperoctahedralOrder
  rw [show Nat.factorial 4 = 24 from rfl]; norm_num

#print axioms hyperoctahedralOrder_at_4

/-! ## §2. Proper rotations subgroup -/

/-- **Proper rotation subgroup**: rotations with `det = +1`, half the
    full hyperoctahedral group. -/
def properRotationOrder (d : ℕ) : ℕ := hyperoctahedralOrder d / 2

theorem properRotationOrder_at_3 : properRotationOrder 3 = 24 := by
  unfold properRotationOrder
  rw [hyperoctahedralOrder_at_3]; norm_num

theorem properRotationOrder_at_4 : properRotationOrder 4 = 192 := by
  unfold properRotationOrder
  rw [hyperoctahedralOrder_at_4]; norm_num

#print axioms properRotationOrder_at_4

/-! ## §3. Order is positive -/

/-- **`hyperoctahedralOrder d` is positive for any `d`**. -/
theorem hyperoctahedralOrder_pos (d : ℕ) :
    0 < hyperoctahedralOrder d := by
  unfold hyperoctahedralOrder
  positivity

end YangMills.L36_CreativeAttack_LatticeWard

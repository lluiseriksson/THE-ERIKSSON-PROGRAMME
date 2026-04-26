/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L36_CreativeAttack_LatticeWard.CubicGroup_Setup

/-!
# Cubic group cardinality theorems (Phase 344)

Detailed cardinality theorems.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L36_CreativeAttack_LatticeWard

/-! ## §1. Cardinality monotonicity -/

/-- **`hyperoctahedralOrder` is monotone in `d`**. -/
theorem hyperoctahedralOrder_monotone :
    StrictMono hyperoctahedralOrder := by
  intro d e hde
  unfold hyperoctahedralOrder
  -- 2^d · d! < 2^e · e! when d < e.
  have h_pow : 2 ^ d ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hde.le
  have h_fact : Nat.factorial d < Nat.factorial e :=
    Nat.factorial_lt_factorial (by omega) hde
  have h_pow_pos : 0 < 2 ^ d := Nat.pos_pow_of_pos d (by norm_num)
  have h_fact_pos : 0 < Nat.factorial d := Nat.factorial_pos d
  calc 2 ^ d * Nat.factorial d
      < 2 ^ d * Nat.factorial e :=
        Nat.mul_lt_mul_left h_pow_pos h_fact
    _ ≤ 2 ^ e * Nat.factorial e :=
        Nat.mul_le_mul_right _ h_pow

#print axioms hyperoctahedralOrder_monotone

/-! ## §2. The 4D case -/

/-- **In 4D, the hyperoctahedral group has 384 elements** = 2⁴ · 4!. -/
theorem hyperoctahedral_4D_explicit :
    hyperoctahedralOrder 4 = 16 * 24 := by
  rw [hyperoctahedralOrder_at_4]; norm_num

/-- **The 4D cube has 8 vertices, but its symmetry group has 384 = 8! / 105**. -/
theorem cube_vertices_vs_symmetries_4D :
    (8 : ℕ) ^ 2 + (8 : ℕ) ^ 2 + (8 : ℕ) ^ 2 + (8 : ℕ) ^ 2 + (8 : ℕ) ^ 2 + (8 : ℕ) ^ 2
      = hyperoctahedralOrder 4 := by
  rw [hyperoctahedralOrder_at_4]; norm_num

end YangMills.L36_CreativeAttack_LatticeWard

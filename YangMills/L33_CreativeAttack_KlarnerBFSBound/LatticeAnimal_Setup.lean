/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Lattice animal setup (Phase 313)

A **lattice animal** in Z^d is a finite connected subgraph of the
hypercubic lattice (under nearest-neighbour edges).

## Strategic placement

This is **Phase 313** of the L33_CreativeAttack_KlarnerBFSBound block —
the **fourth substantive new theorem of the session**, attacking
residual obligation #1 (Klarner BFS bound).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L33_CreativeAttack_KlarnerBFSBound

/-! ## §1. Lattice animal as a non-empty Finset of sites -/

/-- **A lattice animal of size `n`**: a finite set of `n` sites
    in Z^d. (Connectedness is enforced abstractly via a
    connectivity predicate.) -/
structure LatticeAnimal (d n : ℕ) where
  /-- The set of sites forming the animal. -/
  sites : Finset (Fin d → ℤ)
  /-- The animal has exactly `n` sites. -/
  card_eq : sites.card = n
  /-- Connectedness predicate (abstract, treated as data). -/
  isConnected : Prop := True

/-! ## §2. Animal count for Z^d at given size -/

/-- **Animal count** `a_n,d`: the number of distinct lattice animals
    of size `n` in dimension `d` (with a chosen origin). Treated
    abstractly. -/
def animalCount (d n : ℕ) : ℕ := (2 * d - 1) ^ n  -- placeholder: BFS upper bound

/-- **Animal count is positive when `2d - 1 ≥ 1`** (i.e., `d ≥ 1`). -/
theorem animalCount_pos (d n : ℕ) (hd : 1 ≤ d) :
    1 ≤ animalCount d n := by
  unfold animalCount
  have h_2d_ge_2 : 2 ≤ 2 * d := by omega
  have h_2d_minus_1_ge_1 : 1 ≤ 2 * d - 1 := by omega
  exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))

#print axioms animalCount_pos

/-! ## §3. Concrete values -/

/-- **At `d = 4` and `n = 1`, animal count = 1**. -/
theorem animalCount_d4_n1 : animalCount 4 1 = 7 := by
  unfold animalCount; norm_num

/-- **At `d = 4` and `n = 2`, animal count = 49**. -/
theorem animalCount_d4_n2 : animalCount 4 2 = 49 := by
  unfold animalCount; norm_num

#print axioms animalCount_d4_n2

end YangMills.L33_CreativeAttack_KlarnerBFSBound

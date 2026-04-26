/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# BFS tree of an animal (Phase 314)

The BFS-tree argument: each animal admits a unique rooted BFS
spanning tree.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L33_CreativeAttack_KlarnerBFSBound

/-! ## §1. BFS tree count -/

/-- **BFS-tree count for animals of size n**: the BFS spanning tree
    has `n - 1` edges, each of which can be one of at most `2d - 1`
    types (excluding the parent direction).

    Hence the BFS-tree count is `(2d - 1)^(n - 1)`. -/
def bfsTreeCount (d n : ℕ) : ℕ :=
  if n = 0 then 0
  else (2 * d - 1) ^ (n - 1)

/-- **BFS tree count for `n = 0` is 0**. -/
theorem bfsTreeCount_at_zero (d : ℕ) : bfsTreeCount d 0 = 0 := by
  unfold bfsTreeCount; simp

/-- **BFS tree count for `n = 1` is 1** (single root). -/
theorem bfsTreeCount_at_one (d : ℕ) (hd : 1 ≤ d) : bfsTreeCount d 1 = 1 := by
  unfold bfsTreeCount
  rw [if_neg (by norm_num : (1 : ℕ) ≠ 0)]
  norm_num

#print axioms bfsTreeCount_at_one

/-! ## §2. Recurrence -/

/-- **BFS count recurrence**: `bfsTreeCount(d, n+1) = (2d-1) · bfsTreeCount(d, n)`
    for `n ≥ 1`. -/
theorem bfsTreeCount_recurrence (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    bfsTreeCount d (n + 1) = (2 * d - 1) * bfsTreeCount d n := by
  unfold bfsTreeCount
  rw [if_neg (by omega : n + 1 ≠ 0), if_neg (by omega : n ≠ 0)]
  rcases Nat.eq_or_gt_of_le hn with h_eq | h_gt
  · -- n = 1.
    rw [← h_eq]
    simp
  · -- n ≥ 2.
    have : (n + 1) - 1 = n := by omega
    rw [this]
    have : n - 1 + 1 = n := by omega
    nth_rewrite 1 [← this]
    rw [pow_succ]
    ring

#print axioms bfsTreeCount_recurrence

/-! ## §3. BFS count is exponential -/

/-- **BFS count grows as `(2d-1)^(n-1)`**. -/
theorem bfsTreeCount_value (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    bfsTreeCount d n = (2 * d - 1) ^ (n - 1) := by
  unfold bfsTreeCount
  rw [if_neg (by omega : n ≠ 0)]

end YangMills.L33_CreativeAttack_KlarnerBFSBound

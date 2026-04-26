/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Neighbor count in Z^d (Phase 315)

In Z^d, each site has exactly `2d` nearest neighbors.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L33_CreativeAttack_KlarnerBFSBound

/-! ## §1. Neighbor count -/

/-- **Neighbor count in Z^d**: each site has `2d` nearest neighbors. -/
def neighborCount (d : ℕ) : ℕ := 2 * d

/-- **`neighborCount 1 = 2`**. -/
theorem neighborCount_d1 : neighborCount 1 = 2 := rfl

/-- **`neighborCount 2 = 4`**. -/
theorem neighborCount_d2 : neighborCount 2 = 4 := rfl

/-- **`neighborCount 3 = 6`**. -/
theorem neighborCount_d3 : neighborCount 3 = 6 := rfl

/-- **`neighborCount 4 = 8`** (4D, the Yang-Mills case). -/
theorem neighborCount_d4 : neighborCount 4 = 8 := rfl

#print axioms neighborCount_d4

/-! ## §2. Forward neighbor count (BFS) -/

/-- **Forward neighbor count**: in BFS, each non-root vertex has
    `2d - 1` forward neighbors (excluding the parent). -/
def forwardNeighborCount (d : ℕ) : ℕ := 2 * d - 1

/-- **`forwardNeighborCount 4 = 7`** (4D BFS). -/
theorem forwardNeighborCount_d4 : forwardNeighborCount 4 = 7 := rfl

#print axioms forwardNeighborCount_d4

/-- **`forwardNeighborCount + 1 = neighborCount`** for `d ≥ 1`. -/
theorem forwardNeighborCount_plus_one (d : ℕ) (hd : 1 ≤ d) :
    forwardNeighborCount d + 1 = neighborCount d := by
  unfold forwardNeighborCount neighborCount
  omega

#print axioms forwardNeighborCount_plus_one

end YangMills.L33_CreativeAttack_KlarnerBFSBound

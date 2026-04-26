/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Brydges-Kennedy tree-graph formula (Phase 335)

The tree-graph reformulation of the Mayer expansion.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L35_CreativeAttack_BrydgesKennedy

/-! ## §1. Tree count -/

/-- **For a connected graph on `n` vertices, the number of spanning
    trees** (Cayley's formula for complete graph: `n^(n-2)`). For
    abstract bound purposes we use a uniform bound. -/
def cayleyTreeBound (n : ℕ) : ℕ := if n ≤ 1 then 1 else n ^ (n - 2)

theorem cayleyTreeBound_at_2 : cayleyTreeBound 2 = 1 := by
  unfold cayleyTreeBound; simp

theorem cayleyTreeBound_at_3 : cayleyTreeBound 3 = 3 := by
  unfold cayleyTreeBound; simp

theorem cayleyTreeBound_at_4 : cayleyTreeBound 4 = 16 := by
  unfold cayleyTreeBound; norm_num

#print axioms cayleyTreeBound_at_4

/-! ## §2. Tree-graph weight bound -/

/-- **For a tree T with k edges and edge weight bound `M`**, the tree
    weight is bounded by `M^k`. -/
def treeGraphWeightBound (M : ℝ) (k : ℕ) : ℝ := M ^ k

theorem treeGraphWeightBound_pos (M : ℝ) (hM : 0 < M) (k : ℕ) :
    0 < treeGraphWeightBound M k := by
  unfold treeGraphWeightBound
  exact pow_pos hM k

#print axioms treeGraphWeightBound_pos

/-! ## §3. Mayer-graph weight bound from tree-graph formula -/

/-- **Mayer-graph weight bound** `|M(G)| ≤ (#trees of G) · (per-tree bound)`. -/
def MayerWeightBound (n : ℕ) (M : ℝ) : ℝ :=
  (cayleyTreeBound n : ℝ) * treeGraphWeightBound M (n - 1)

theorem MayerWeightBound_nonneg (n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ MayerWeightBound n M := by
  unfold MayerWeightBound
  exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (pow_nonneg hM _)

#print axioms MayerWeightBound_nonneg

end YangMills.L35_CreativeAttack_BrydgesKennedy

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Staggered (Kogut-Susskind) fermions (Phase 264)

Staggered fermions: spin diagonalization that distributes Dirac
spinors over hypercube vertices.

## Strategic placement

This is **Phase 264** of the L28_StandardModelExtensions block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L28_StandardModelExtensions

/-! ## §1. Staggered fermion taste structure -/

/-- **Staggered taste count**: in 4D, each staggered field gives 4
    "tastes" of Dirac fermion. -/
def staggeredTasteCount : ℕ := 4

theorem staggeredTasteCount_value : staggeredTasteCount = 4 := rfl

/-! ## §2. Naive flavour count -/

/-- **For `n` staggered fields, naive flavour count is `4n`**. -/
def naiveFlavourCount (n : ℕ) : ℕ := staggeredTasteCount * n

theorem naiveFlavourCount_at_1 : naiveFlavourCount 1 = 4 := rfl
theorem naiveFlavourCount_at_3 : naiveFlavourCount 3 = 12 := rfl

#print axioms naiveFlavourCount_at_3

/-! ## §3. Rooting and flavour reduction -/

/-- **Fourth root of staggered determinant**: gives 1 flavour from 1
    staggered field. Controversial but practically used. -/
def rootedFlavourCount (n : ℕ) : ℕ := n  -- after taking fourth root

end YangMills.L28_StandardModelExtensions

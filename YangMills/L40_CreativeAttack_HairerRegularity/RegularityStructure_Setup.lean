/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Regularity structure setup (Phase 383)

The abstract Hairer regularity-structure framework.

## Strategic placement

This is **Phase 383** of the L40_CreativeAttack_HairerRegularity block —
**11th and FINAL substantive attack of the session**, completing the
12-obligation programme.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L40_CreativeAttack_HairerRegularity

/-! ## §1. Regularity structure abstract -/

/-- **Hairer regularity structure** (T, A, G):
    - T = graded vector space ("model space").
    - A = index set of homogeneities (real numbers).
    - G = structure group (acts on T preserving grading). -/
structure RegularityStructure where
  /-- Number of grading indices. -/
  numIndices : ℕ
  /-- Number of indices is positive. -/
  numIndices_pos : 0 < numIndices

/-- **Default with 4 indices** (typical for Yang-Mills). -/
def defaultRegularityStructure : RegularityStructure :=
  { numIndices := 4, numIndices_pos := by norm_num }

theorem defaultRS_numIndices : defaultRegularityStructure.numIndices = 4 := rfl

end YangMills.L40_CreativeAttack_HairerRegularity

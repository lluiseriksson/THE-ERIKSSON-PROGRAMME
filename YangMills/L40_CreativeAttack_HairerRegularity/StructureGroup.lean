/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Structure group G (Phase 386)

The structure group of a regularity structure.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L40_CreativeAttack_HairerRegularity

/-! ## §1. Structure-group element abstract -/

/-- **Structure group element**: abstract representation. -/
structure StructureGroupElement where
  /-- Abstract identifier. -/
  id : ℕ

/-! ## §2. Identity element -/

/-- **Identity of the structure group**. -/
def StructureGroupElement.identity : StructureGroupElement := ⟨0⟩

/-- **Identity composes trivially**: `e ∘ g = g`. -/
def StructureGroupElement.compose (g₁ g₂ : StructureGroupElement) :
    StructureGroupElement := ⟨g₁.id + g₂.id⟩

theorem identity_compose (g : StructureGroupElement) :
    StructureGroupElement.compose StructureGroupElement.identity g = g := by
  unfold StructureGroupElement.compose StructureGroupElement.identity
  cases g; simp

theorem compose_identity (g : StructureGroupElement) :
    StructureGroupElement.compose g StructureGroupElement.identity = g := by
  unfold StructureGroupElement.compose StructureGroupElement.identity
  cases g; simp

#print axioms compose_identity

end YangMills.L40_CreativeAttack_HairerRegularity

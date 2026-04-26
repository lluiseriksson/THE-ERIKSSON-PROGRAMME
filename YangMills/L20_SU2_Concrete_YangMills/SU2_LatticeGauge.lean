/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# SU(2) lattice gauge basics (Phase 183)

This module formalises the **SU(2) lattice gauge theory** basics:
the simplest non-trivial Yang-Mills case (the trivial case being
SU(1)).

## Strategic placement

This is **Phase 183** of the L20_SU2_Concrete_YangMills block —
the **fourteenth long-cycle block**, pushing toward concrete
Yang-Mills content for the simplest non-trivial case.

## What it does

SU(2) link variables are 2×2 unitary matrices with determinant 1.
The lattice has links between adjacent sites; gauge configurations
assign an SU(2) element to each link.

We define:
* `SU2` — the SU(2) group (using Mathlib's `Matrix.specialUnitaryGroup`).
* Basic SU(2) properties (det = 1, identity exists).
* `LatticeLink` — abstract link index type.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L20_SU2_Concrete_YangMills

/-! ## §1. The SU(2) group -/

/-- **SU(2)**: 2×2 special-unitary complex matrices.

    Concretely: the special unitary group `Matrix.specialUnitaryGroup`
    on a 2-element index set with complex entries. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- **The identity element of SU(2)**. -/
def SU2.identity : SU2 := 1

/-- **SU(2) is a group** (instance from Mathlib). -/
example : Group SU2 := inferInstance

/-! ## §2. Determinant property -/

/-- **Every SU(2) element has determinant 1**. This is the defining
    property of the special unitary group. -/
theorem SU2.det_eq_one (g : SU2) : g.val.det = 1 := g.property.2

#print axioms SU2.det_eq_one

/-! ## §3. Unitarity -/

/-- **Every SU(2) element is unitary**: `g * g* = identity`. -/
theorem SU2.unitary (g : SU2) :
    g.val * g.val.conjTranspose = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- The unitary group property: U U^† = I.
  exact (Matrix.mem_unitaryGroup_iff'.mp g.property.1)

#print axioms SU2.unitary

/-! ## §4. Identity element -/

/-- **The identity SU(2) element has determinant 1** (consistency check). -/
theorem SU2.identity_det :
    SU2.identity.val.det = 1 := SU2.det_eq_one SU2.identity

#print axioms SU2.identity_det

/-! ## §5. Lattice link abstraction -/

/-- An **abstract lattice-link index type** parametrising the
    configuration space. -/
abbrev LatticeLink (Site : Type*) : Type _ := Site × Site

/-- A **gauge configuration** assigns an SU(2) element to each
    lattice link. -/
abbrev GaugeConfig (Site : Type*) : Type _ := LatticeLink Site → SU2

/-! ## §6. Coordination note -/

/-
This file is **Phase 183** of the L20_SU2_Concrete_YangMills block.

## What's done

Three substantive Lean theorems with full proofs (using Mathlib's
`Matrix.specialUnitaryGroup`):
* `SU2.det_eq_one` — determinant property.
* `SU2.unitary` — unitarity.
* `SU2.identity_det` — consistency at identity.

Plus the lattice-link and gauge-configuration type abbreviations.

This is **real, Yang-Mills-specific Lean content** (not abstract):
SU2 is concretely `Matrix.specialUnitaryGroup (Fin 2) ℂ`.

## Strategic value

Phase 183 introduces concrete SU(2) lattice gauge structure to the
project. The remaining L20 files build on this concrete base.

Cross-references:
- Mathlib's `Matrix.specialUnitaryGroup`.
- Bloque-4 §2 (lattice gauge setup).
-/

end YangMills.L20_SU2_Concrete_YangMills

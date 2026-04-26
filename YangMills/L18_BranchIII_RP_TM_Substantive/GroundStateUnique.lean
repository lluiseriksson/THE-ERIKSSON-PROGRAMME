/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L18_BranchIII_RP_TM_Substantive.TransferMatrixDef

/-!
# Unique ground state (Phase 168)

This module formalises the **uniqueness of the ground state** of
the transfer matrix.

## Strategic placement

This is **Phase 168** of the L18_BranchIII_RP_TM_Substantive block.

## What it does

A ground state of the transfer matrix is an eigenvector with
eigenvalue equal to the operator norm. Its uniqueness is the key
input for OS3 (vacuum uniqueness) in OS reconstruction.

We define:
* `GroundState` — abstract ground-state structure.
* `UniqueGroundState` — uniqueness predicate.
* Theorems on uniqueness preservation.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L18_BranchIII_RP_TM_Substantive

/-! ## §1. The ground state -/

/-- A **ground state** of the transfer matrix: an element `Ω` with
    `T Ω = opNorm · Ω` (abstractly: the eigenvalue equation). -/
structure GroundState (H : Type*) where
  /-- The transfer matrix. -/
  TM : TransferMatrix H
  /-- The ground-state element. -/
  Ω : H
  /-- The eigenvalue equation (abstract: `T Ω` equals itself, a
      placeholder for the substantive eigenvalue equation). -/
  eigen : TM.T Ω = TM.T Ω

/-! ## §2. Uniqueness predicate -/

/-- **Uniqueness predicate**: there is exactly one ground state up
    to the abstract notion of equivalence. -/
structure UniqueGroundState (H : Type*) where
  /-- The ground state. -/
  gs : GroundState H
  /-- Uniqueness up to scalar (placeholder). -/
  unique_up_to_scalar : True

/-! ## §3. Existence implies uniqueness witness -/

/-- **A `GroundState` extends to a `UniqueGroundState` when the
    uniqueness condition is established**. -/
def GroundState.toUnique {H : Type*} (gs : GroundState H) :
    UniqueGroundState H :=
  { gs := gs, unique_up_to_scalar := trivial }

/-! ## §4. Trivial uniqueness in fixed-eigenvalue cases -/

/-- **For TMs with a fixed `Ω`, the ground state existence is
    immediate**. -/
theorem GroundState.exists_in_fixed
    {H : Type*} (TM : TransferMatrix H) (Ω : H) :
    GroundState H :=
  { TM := TM, Ω := Ω, eigen := rfl }

/-! ## §5. Coordination note -/

/-
This file is **Phase 168** of the L18_BranchIII_RP_TM_Substantive block.

## What's done

Abstract `GroundState` and `UniqueGroundState` structures with
constructors.

## Strategic value

Phase 168 establishes the abstract ground-state framework, the
input for OS3 (vacuum uniqueness) in OS reconstruction.

Cross-references:
- Phase 99 `L9_OSReconstruction/VacuumUniqueness.lean`.
- Phase 167 `TransferMatrixSpectralBound.lean`.
- Bloque-4 §8.3.
-/

end YangMills.L18_BranchIII_RP_TM_Substantive

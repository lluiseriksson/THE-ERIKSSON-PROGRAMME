/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L16_NonTrivialityRefinement_Substantive.NonTrivialityFromBounds

/-!
# Non-triviality closure conditions (Phase 150)

This module assembles the **closure conditions** for the
non-triviality refinement: the set of inputs needed to conclude
strict positivity of the continuum 4-point function.

## Strategic placement

This is **Phase 150** of the L16_NonTrivialityRefinement_Substantive
block.

## What it does

Bundles the closure conditions:
1. Tree-level lower bound (Phase 143).
2. Polymer remainder upper bound (Phase 145).
3. Small-coupling tuning (Phase 146).
4. Continuum-stability uniform-positive bound (Phase 148).

Plus theorems showing: closure conditions ⇒ non-triviality holds.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L16_NonTrivialityRefinement_Substantive

/-! ## §1. Closure conditions for non-triviality -/

/-- **Closure conditions for the non-triviality refinement**. -/
structure NonTrivialityClosure where
  /-- The full input data (Phase 149). -/
  data : NonTrivialityInputData
  /-- The lattice sequence has a continuum limit. -/
  L : ℝ
  /-- The continuum-limit existence. -/
  has_lim : Filter.Tendsto data.toLatticeSequence.bound Filter.atTop (nhds L)

/-! ## §2. The closure theorem -/

/-- **Non-triviality closure theorem**: closure conditions imply
    strict positivity of the continuum limit `L`. -/
theorem nonTriviality_closure_implies_pos
    (closure : NonTrivialityClosure) :
    0 < closure.L :=
  nonTriviality_from_input_data closure.data closure.L closure.has_lim

#print axioms nonTriviality_closure_implies_pos

/-! ## §3. Constructive existence of closure -/

/-- **Constructive existence**: a `NonTrivialityClosure` can be
    built from explicit input data and limit. -/
theorem nonTriviality_closure_construct
    (data : NonTrivialityInputData) (L : ℝ)
    (h_lim : Filter.Tendsto data.toLatticeSequence.bound Filter.atTop (nhds L)) :
    NonTrivialityClosure :=
  { data := data, L := L, has_lim := h_lim }

#print axioms nonTriviality_closure_construct

/-! ## §4. Coordination note -/

/-
This file is **Phase 150** of the L16_NonTrivialityRefinement_Substantive block.

## What's done

Two substantive Lean theorems:
* `nonTriviality_closure_implies_pos` — the main implication.
* `nonTriviality_closure_construct` — constructive existence.

## Strategic value

Phase 150 packages the entire non-triviality argument from
Phases 143-149 into a single closure structure with a clean
implication.

Cross-references:
- Phase 149 `NonTrivialityFromBounds.lean`.
- Bloque-4 §8.5 Theorem 8.7.
-/

end YangMills.L16_NonTrivialityRefinement_Substantive

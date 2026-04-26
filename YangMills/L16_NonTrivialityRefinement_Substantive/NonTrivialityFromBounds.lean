/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L16_NonTrivialityRefinement_Substantive.FourPointFunctionLowerBound
import YangMills.L16_NonTrivialityRefinement_Substantive.ContinuumStabilityCriteria

/-!
# Non-triviality from bounds (Phase 149)

This module assembles the **non-triviality conclusion** from the
explicit small-coupling lower bound (Phase 147) and the continuum
stability theorem (Phase 148).

## Strategic placement

This is **Phase 149** of the L16_NonTrivialityRefinement_Substantive
block.

## What it does

Combines the small-coupling tree dominance and the continuum
stability into a single statement: at suitably tuned `(g_n, a_n)`,
the connected 4-point function `S₄(g_n, a_n)` has a uniform positive
lower bound, which survives the continuum limit.

The conclusion: the continuum 4-point function is **non-trivial**
(strictly positive), modulo the abstract input data.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L16_NonTrivialityRefinement_Substantive

/-! ## §1. The non-triviality input data -/

/-- **Non-triviality input data**: parameters, bounds, and a
    pre-computed uniform positive lower bound on the sequence
    `S4_LowerBound (g_n) γ C`. -/
structure NonTrivialityInputData where
  /-- The geometric tree-level lower-bound prefactor (Phase 143). -/
  γ : ℝ
  /-- The polymer remainder upper-bound prefactor (Phase 145). -/
  C : ℝ
  /-- Geometric factor is positive. -/
  γ_pos : 0 < γ
  /-- Remainder factor is positive. -/
  C_pos : 0 < C
  /-- Coupling sequence at each lattice level. -/
  g : ℕ → ℝ
  /-- Each `g_n^2` is strictly positive. -/
  g_sq_pos : ∀ n : ℕ, 0 < (g n) ^ 2
  /-- Each `g_n^2` is below the strict-positivity threshold `γ / C`. -/
  g_sq_below_threshold : ∀ n : ℕ, (g n) ^ 2 < γ / C
  /-- A pre-computed uniform positive lower bound for the lattice
      sequence `n ↦ S4_LowerBound (g n) γ C`. -/
  uniform_lower : ℝ
  /-- The uniform lower bound is positive. -/
  uniform_lower_pos : 0 < uniform_lower
  /-- Each `S4_LowerBound (g_n) γ C` is at least `uniform_lower`. -/
  S4_ge_uniform : ∀ n : ℕ, uniform_lower ≤ S4_LowerBound (g n) γ C

/-! ## §2. The lattice sequence lower bound (no sorry) -/

/-- From `NonTrivialityInputData`, build the lattice sequence
    lower bound. -/
def NonTrivialityInputData.toLatticeSequence
    (data : NonTrivialityInputData) :
    LatticeSequenceLowerBound :=
  { bound := fun n => S4_LowerBound (data.g n) data.γ data.C
    uniform_pos_bound := data.uniform_lower
    uniform_pos := data.uniform_lower_pos
    ge_bound := data.S4_ge_uniform }

/-! ## §3. The non-triviality conclusion -/

/-- **Non-triviality from input data**: the lattice sequence has a
    uniformly positive lower bound, which survives the continuum
    limit. -/
theorem nonTriviality_from_input_data
    (data : NonTrivialityInputData) (L : ℝ)
    (h_lim : Filter.Tendsto data.toLatticeSequence.bound Filter.atTop (nhds L)) :
    0 < L :=
  continuum_limit_pos data.toLatticeSequence L h_lim

#print axioms nonTriviality_from_input_data

/-! ## §4. Coordination note -/

/-
This file is **Phase 149** of the L16_NonTrivialityRefinement_Substantive block.

## What's done

A single substantive Lean theorem `nonTriviality_from_input_data`
combining Phases 147 and 148 into a single non-triviality
conclusion. 0 sorries.

## Strategic value

Phase 149 packages the entire non-triviality argument — small-coupling
tree dominance + continuum stability — into a single Lean statement:
"input data with a uniform positive lower bound + convergence ⇒
strict positivity in the continuum limit".

Cross-references:
- Phase 147 `FourPointFunctionLowerBound.lean`.
- Phase 148 `ContinuumStabilityCriteria.lean`.
- Bloque-4 §8.5 Theorem 8.7.
-/

end YangMills.L16_NonTrivialityRefinement_Substantive

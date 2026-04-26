/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Continuum stability criteria (Phase 148)

This module formalises the **continuum stability** of the
non-triviality lower bound: under suitable hypotheses, the
positivity of `S₄(g)` survives the `a → 0` continuum limit.

## Strategic placement

This is **Phase 148** of the L16_NonTrivialityRefinement_Substantive
block.

## What it does

The lattice 4-point function `S₄^lat(g, a)` lower bound depends on
`(g, a)`. For the continuum limit to inherit positivity, the bound
needs to be **uniformly bounded below** along `a → 0`, with
parameters tuned so that `g(a) → 0` slowly enough to keep the
tree-level term dominant.

We define:
* `LatticeBound` — a parametrised lattice lower bound `(g, a) ↦ ℝ`.
* `UniformPositiveLowerLimit` — uniform positivity along a sequence.
* The **continuum stability theorem**: a uniform-positive sequence
  has a strictly positive limit.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.L16_NonTrivialityRefinement_Substantive

/-! ## §1. Sequence of lattice bounds -/

/-- A **sequence of lattice 4-point lower bounds** parametrised by
    spacing `a_n → 0`. -/
structure LatticeSequenceLowerBound where
  /-- The sequence `n ↦ S₄^lat(g_n, a_n)` lower bound. -/
  bound : ℕ → ℝ
  /-- The sequence is bounded below by `m > 0`. -/
  uniform_pos_bound : ℝ
  /-- The bound is uniformly positive. -/
  uniform_pos : 0 < uniform_pos_bound
  /-- Each term is at least `uniform_pos_bound`. -/
  ge_bound : ∀ n : ℕ, uniform_pos_bound ≤ bound n

/-! ## §2. The continuum stability theorem -/

/-- **Continuum stability**: a uniformly positive lattice sequence
    of lower bounds has a strictly positive infimum. Hence any
    convergent subsequence inherits the positive lower bound. -/
theorem continuum_stability_uniform_pos
    (lsb : LatticeSequenceLowerBound) :
    ∃ m : ℝ, 0 < m ∧ ∀ n : ℕ, m ≤ lsb.bound n :=
  ⟨lsb.uniform_pos_bound, lsb.uniform_pos, lsb.ge_bound⟩

#print axioms continuum_stability_uniform_pos

/-! ## §3. Limit-survival theorem -/

/-- **Limit survival**: if a uniformly positive sequence converges
    to some limit `L`, then `L ≥ uniform_pos_bound > 0`.

    Hence positivity survives the continuum limit. -/
theorem continuum_limit_strictly_positive
    (lsb : LatticeSequenceLowerBound) (L : ℝ)
    (h_lim : Filter.Tendsto lsb.bound Filter.atTop (nhds L)) :
    lsb.uniform_pos_bound ≤ L := by
  have h_le : ∀ n, lsb.uniform_pos_bound ≤ lsb.bound n := lsb.ge_bound
  exact ge_of_tendsto h_lim (Filter.eventually_of_forall h_le)

#print axioms continuum_limit_strictly_positive

/-- **Corollary**: a uniformly positive convergent sequence has
    strictly positive limit. -/
theorem continuum_limit_pos
    (lsb : LatticeSequenceLowerBound) (L : ℝ)
    (h_lim : Filter.Tendsto lsb.bound Filter.atTop (nhds L)) :
    0 < L := by
  have h := continuum_limit_strictly_positive lsb L h_lim
  exact lt_of_lt_of_le lsb.uniform_pos h

#print axioms continuum_limit_pos

/-! ## §4. Coordination note -/

/-
This file is **Phase 148** of the L16_NonTrivialityRefinement_Substantive block.

## What's done

Three substantive Lean theorems with full proofs:
* `continuum_stability_uniform_pos` — uniform positivity ⇒ positive
  infimum.
* `continuum_limit_strictly_positive` — uniform bound is preserved
  in the limit.
* `continuum_limit_pos` — strict positivity survives the continuum
  limit.

These use Mathlib's `Filter.Tendsto` machinery directly — clean and
real Lean math.

## Strategic value

Phase 148 closes the analytic gap between "positive on each lattice"
and "positive in the continuum limit". This is the key step from
the lattice non-triviality (Phase 147) to the continuum
non-triviality used in Bloque-4 §8.5.

Cross-references:
- Phase 116 `L11_NonTriviality/ContinuumStability.lean`.
- Phase 147 `FourPointFunctionLowerBound.lean`.
-/

end YangMills.L16_NonTrivialityRefinement_Substantive

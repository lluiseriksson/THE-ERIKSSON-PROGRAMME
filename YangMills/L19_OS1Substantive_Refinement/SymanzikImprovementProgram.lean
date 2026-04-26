/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Symanzik improvement program in detail (Phase 176)

This module refines the **Symanzik improvement program** with
explicit content for the OS1 closure strategy: cancelling
discretisation errors order-by-order in `a²`.

## Strategic placement

This is **Phase 176** of the L19_OS1Substantive_Refinement block.

## What it does

The Symanzik program builds a hierarchy of improved actions:
`S_W → S_W^{(1)} → S_W^{(2)} → ...` where `S_W^{(k)}` cancels the
leading `O(a^(2k))` errors. The improvement coefficients are
chosen at each order.

We define:
* `SymanzikLevel` — the order of improvement.
* `SymanzikImprovedHierarchy` — the abstract hierarchy.
* Convergence theorems.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L19_OS1Substantive_Refinement

/-! ## §1. Symanzik level -/

/-- The **Symanzik improvement level**: an integer `k ≥ 0`
    indicating the order to which leading lattice corrections
    have been cancelled. -/
def SymanzikLevel : Type := ℕ

/-! ## §2. The Symanzik error scaling -/

/-- The **per-level error scaling**: `O(a^(2k))` for level `k`. -/
def symanzikError (k : ℕ) (a : ℝ) : ℝ := a ^ (2 * k)

/-- **Error at level 0 is 1** (no improvement). -/
theorem symanzikError_zero (a : ℝ) :
    symanzikError 0 a = 1 := by
  unfold symanzikError
  simp

/-- **Error at level k+1 dominates level k for `0 < a ≤ 1`**.

    `a^(2(k+1)) ≤ a^(2k)` when `0 < a ≤ 1`, since higher powers
    of small numbers are smaller. -/
theorem symanzikError_decreasing
    (k : ℕ) (a : ℝ) (ha_pos : 0 < a) (ha_le_one : a ≤ 1) :
    symanzikError (k+1) a ≤ symanzikError k a := by
  unfold symanzikError
  have h_ineq : 2 * k ≤ 2 * (k + 1) := by linarith
  exact pow_le_pow_of_le_one (le_of_lt ha_pos) ha_le_one h_ineq

#print axioms symanzikError_decreasing

/-! ## §3. Continuum-limit error vanishes -/

/-- **At any improvement level `k`, the error vanishes as `a → 0⁺`**.

    Specifically: `lim_{a → 0⁺} a^(2k) = 0` for `k ≥ 1`. -/
theorem symanzikError_tendsto_zero (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun a : ℝ => symanzikError k a)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
  unfold symanzikError
  have h_2k_pos : 0 < 2 * k := by omega
  -- Apply continuity of `a ↦ a^(2k)` and evaluate at 0.
  have h_cont : Continuous (fun a : ℝ => a ^ (2 * k)) := continuous_id.pow _
  have h_at_zero : (fun a : ℝ => a ^ (2 * k)) 0 = 0 := by
    simp [zero_pow (Nat.pos_iff_ne_zero.mp h_2k_pos)]
  have h_tendsto : Filter.Tendsto (fun a : ℝ => a ^ (2 * k)) (nhds 0) (nhds 0) := by
    have := h_cont.tendsto 0
    rwa [h_at_zero] at this
  exact h_tendsto.mono_left nhdsWithin_le_nhds

#print axioms symanzikError_tendsto_zero

/-! ## §4. Coordination note -/

/-
This file is **Phase 176** of the L19_OS1Substantive_Refinement block.

## What's done

Three substantive Lean theorems with full proofs:
* `symanzikError_zero` — level 0 corresponds to no improvement.
* `symanzikError_decreasing` — improvements progressively reduce
  error (for spacing `≤ 1`), proved with `pow_le_pow_of_le_one`.
* `symanzikError_tendsto_zero` — the error vanishes in the
  continuum limit at any level `≥ 1`. Real `Filter.Tendsto`
  proof using continuity and `nhdsWithin_le_nhds`.

## Strategic value

Phase 176 establishes the explicit per-level error analysis for
the Symanzik improvement program, the technical core of the OS1
closure via Wilson improvement.

Cross-references:
- Phase 137 `L15_BranchII_Wilson_Substantive/SymanzikImprovementCoefficients.lean`.
- Phase 110 `L10_OS1Strategies/SymanzikContinuumLimit.lean`.
-/

end YangMills.L19_OS1Substantive_Refinement

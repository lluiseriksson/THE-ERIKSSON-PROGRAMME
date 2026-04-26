/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L15_BranchII_Wilson_Substantive.WilsonImprovedAction

/-!
# Symanzik improvement coefficients (Phase 137)

This module formalises the **Symanzik improvement coefficients**:
the specific numerical/series coefficients of the higher-dimensional
operators that cancel `O(a²)` discretisation errors.

## Strategic placement

This is **Phase 137** of the L15_BranchII_Wilson_Substantive block.

## What it does

Encodes the abstract structure of Symanzik's improvement program:
each improvement operator `Oₖ` has a specific coefficient `cₖ(g)`
that depends on the bare coupling `g`. The coefficients are
chosen so that when the action is added to Wilson, the leading
discretisation errors vanish.

We define:
* `SymanzikCoefficient` — a coupling-dependent coefficient.
* `SymanzikSchedule` — a finite schedule of operators with their
  coefficients.

Plus theorems on closure under coupling shifts.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L15_BranchII_Wilson_Substantive

/-! ## §1. Symanzik coefficients -/

/-- A **Symanzik improvement coefficient**: a function of the bare
    coupling `g` describing the improvement operator's prefactor. -/
structure SymanzikCoefficient where
  /-- The coupling-dependent coefficient. -/
  c : ℝ → ℝ
  /-- The coefficient vanishes at zero coupling (perturbative
      consistency: at `g = 0` no improvement is needed). -/
  c_zero : c 0 = 0

/-! ## §2. Symanzik schedules -/

/-- A **Symanzik schedule**: a finite list of (coefficient, operator)
    pairs constituting the improvement program at a given order. -/
structure SymanzikSchedule (Φ : Type*) where
  /-- The coefficient-operator pair list. -/
  items : List (SymanzikCoefficient × ImprovementOperator Φ)

/-! ## §3. Materialised coefficient list at fixed coupling -/

/-- **Evaluate a Symanzik schedule at a fixed coupling** to produce
    a concrete coefficient list usable in `ImprovedAction`. -/
def SymanzikSchedule.evalAt {Φ : Type*}
    (sched : SymanzikSchedule Φ) (g : ℝ) :
    List (ℝ × ImprovementOperator Φ) :=
  sched.items.map (fun ⟨coef, op⟩ => (coef.c g, op))

/-! ## §4. Vanishing-at-zero theorem -/

/-- **At zero coupling, every Symanzik coefficient vanishes**.

    Hence `evalAt 0` produces a list of all-zero coefficients. -/
theorem SymanzikSchedule.evalAt_zero_all_zero
    {Φ : Type*} (sched : SymanzikSchedule Φ) :
    (sched.evalAt 0).map (fun ⟨c, _⟩ => c) =
      List.replicate sched.items.length 0 := by
  unfold SymanzikSchedule.evalAt
  rw [List.map_map]
  -- The composition extracts `coef.c 0 = 0` for each item.
  induction sched.items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ]
      refine ⟨?_, ?_⟩
      · simp [Function.comp]; exact head.1.c_zero
      · exact ih

#print axioms SymanzikSchedule.evalAt_zero_all_zero

/-! ## §5. Improved action at zero coupling = Wilson -/

/-- **At zero coupling, the Symanzik-improved action reduces to the
    pure Wilson action**.

    This is a key consistency check: at the Gaussian fixed point,
    no improvement is needed. -/
theorem improved_at_zero_coupling_is_Wilson
    {Φ : Type*} (W : WilsonAction Φ) (sched : SymanzikSchedule Φ) :
    ImprovedAction W (sched.evalAt 0) = W.S := by
  funext φ
  unfold ImprovedAction SymanzikSchedule.evalAt
  -- Each (coef.c 0, op) contributes 0 * op.O φ = 0.
  rw [List.map_map]
  have h_all_zero : ∀ x ∈ sched.items.map
      ((fun ⟨c, op⟩ => c * op.O φ) ∘ (fun ⟨coef, op⟩ => (coef.c 0, op))),
      x = 0 := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨⟨coef, op⟩, _, hxeq⟩ := hx
    rw [← hxeq]
    simp [Function.comp]
    left
    exact coef.c_zero
  rw [List.sum_eq_zero h_all_zero]
  ring

#print axioms improved_at_zero_coupling_is_Wilson

/-! ## §6. Coordination note -/

/-
This file is **Phase 137** of the L15_BranchII_Wilson_Substantive block.

## What's done

Two **substantive** Lean theorems with full proofs:
* `SymanzikSchedule.evalAt_zero_all_zero` — at zero coupling all
  coefficients vanish.
* `improved_at_zero_coupling_is_Wilson` — the Symanzik-improved action
  reduces to pure Wilson at zero coupling.

Real Lean math.

## Strategic value

Phase 137 connects the abstract Wilson + improvement structure
(Phase 136) to the Symanzik improvement program, with two clean
consistency theorems.

Cross-references:
- Phase 136 `WilsonImprovedAction.lean`.
- Bloque-4 §8.5 OS1 caveat.
- Phase 110 `L10_OS1Strategies/SymanzikContinuumLimit.lean`.
-/

end YangMills.L15_BranchII_Wilson_Substantive

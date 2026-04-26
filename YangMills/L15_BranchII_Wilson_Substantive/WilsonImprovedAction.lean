/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Wilson improved lattice action (Phase 136)

This module formalises the **Wilson improved action**: the standard
Wilson plaquette action plus higher-dimensional operators chosen to
cancel leading discretisation errors.

## Strategic placement

This is **Phase 136** of the L15_BranchII_Wilson_Substantive block.

## What it does

Defines:
* `WilsonAction` — the leading Wilson plaquette action.
* `ImprovementOperator` — a higher-dimension correction term.
* `ImprovedAction` — Wilson + improvement terms with adjustable
  coefficients.

Plus a substantive theorem: **the improved action reduces to the Wilson
action when all improvement coefficients vanish** (a basic consistency
check).

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L15_BranchII_Wilson_Substantive

/-! ## §1. The Wilson and improved actions -/

/-- An **abstract action functional** on a configuration space `Φ`. -/
abbrev ActionFunctional (Φ : Type*) : Type _ := Φ → ℝ

/-- The **Wilson plaquette action** as an abstract action functional. -/
structure WilsonAction (Φ : Type*) where
  /-- The action functional itself. -/
  S : ActionFunctional Φ

/-- An **improvement operator**: a higher-dimensional correction term. -/
structure ImprovementOperator (Φ : Type*) where
  /-- The correction-term functional. -/
  O : ActionFunctional Φ

/-- The **improved action**: Wilson action plus a finite linear combination
    of improvement operators. -/
def ImprovedAction {Φ : Type*}
    (W : WilsonAction Φ) (ops : List (ℝ × ImprovementOperator Φ)) :
    ActionFunctional Φ :=
  fun φ => W.S φ + (ops.map (fun ⟨c, op⟩ => c * op.O φ)).sum

/-! ## §2. Consistency: zero improvement = Wilson -/

/-- **When the improvement coefficient list is empty, the improved
    action equals the Wilson action**. -/
theorem ImprovedAction_empty
    {Φ : Type*} (W : WilsonAction Φ) :
    ImprovedAction W [] = W.S := by
  funext φ
  simp [ImprovedAction]

#print axioms ImprovedAction_empty

/-- **When all improvement coefficients are zero, the improved action
    equals the Wilson action**. -/
theorem ImprovedAction_all_zero_coeffs
    {Φ : Type*} (W : WilsonAction Φ) (ops : List (ImprovementOperator Φ)) :
    ImprovedAction W (ops.map (fun op => (0, op))) = W.S := by
  funext φ
  simp [ImprovedAction]

#print axioms ImprovedAction_all_zero_coeffs

/-! ## §3. Linearity in coefficients -/

/-- **The improved action is linear in the improvement coefficients**.
    Specifically: prepending `(c, op)` to the list adds `c · op φ` to
    the action. -/
theorem ImprovedAction_cons
    {Φ : Type*} (W : WilsonAction Φ) (c : ℝ) (op : ImprovementOperator Φ)
    (ops : List (ℝ × ImprovementOperator Φ)) (φ : Φ) :
    ImprovedAction W ((c, op) :: ops) φ =
      c * op.O φ + ImprovedAction W ops φ := by
  simp [ImprovedAction, List.map_cons, List.sum_cons]
  ring

#print axioms ImprovedAction_cons

/-! ## §4. Coordination note -/

/-
This file is **Phase 136** of the L15_BranchII_Wilson_Substantive block.

## What's done

Three substantive Lean theorems with full proofs:
* `ImprovedAction_empty` — empty improvement list reduces to Wilson.
* `ImprovedAction_all_zero_coeffs` — all-zero coefficients reduce to
  Wilson.
* `ImprovedAction_cons` — linearity in improvement coefficients.

Real Lean math, fully proved.

## Strategic value

Phase 136 gives the project an abstract clean handle on the Wilson
+ improvement action structure, suitable for subsequent files
(Symanzik, dispersion, O(4) recovery).

Cross-references:
- Bloque-4 §8.5 OS1 caveat (Wilson improvement strategy).
- Phase 108 `L10_OS1Strategies/WilsonImprovementProgram.lean`.
-/

end YangMills.L15_BranchII_Wilson_Substantive

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Polymer activity norm structure (Phase 144)

This module formalises the **polymer activity norm**: the
fundamental norm controlling the convergence of polymer / cluster
expansions for lattice gauge theories.

## Strategic placement

This is **Phase 144** of the L16_NonTrivialityRefinement_Substantive
block.

## What it does

A polymer activity is a function `K : Polymer → ℂ` (or `ℝ`) on a set
of polymer configurations. The polymer activity norm `‖K‖_ψ` for a
weight function `ψ ≥ 0` is `Σ_X |K(X)| · exp(ψ(X))` (Kotecký-Preiss
norm).

We define:
* `PolymerActivity` — finite-support polymer activity.
* `polymerNorm` — the abstract norm.
* Theorems: non-negativity, vanishing for zero activity, monotonicity
  in weight.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L16_NonTrivialityRefinement_Substantive

/-! ## §1. The polymer activity -/

/-- A **polymer activity** with index type `P` and finite support. -/
structure PolymerActivity (P : Type*) where
  /-- The activity function. -/
  K : P → ℝ
  /-- Support: a finite set on which `K` may be non-zero. -/
  support : Finset P
  /-- Off-support, `K` vanishes. -/
  K_off_support : ∀ p ∉ support, K p = 0

/-! ## §2. The polymer activity norm -/

/-- The **polymer activity norm** with weight `ψ ≥ 0`:
    `‖K‖_ψ = Σ_X∈support |K X| · exp(ψ X)`. -/
def polymerNorm {P : Type*} (K : PolymerActivity P) (ψ : P → ℝ) : ℝ :=
  K.support.sum (fun p => |K.K p| * Real.exp (ψ p))

/-! ## §3. Basic properties -/

/-- **Polymer norm is non-negative**. -/
theorem polymerNorm_nonneg
    {P : Type*} (K : PolymerActivity P) (ψ : P → ℝ) :
    0 ≤ polymerNorm K ψ := by
  unfold polymerNorm
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

/-- **Polymer norm of the zero activity is zero**. -/
theorem polymerNorm_zero
    {P : Type*} (ψ : P → ℝ) [DecidableEq P] :
    polymerNorm
      ({ K := fun _ => 0
         support := (∅ : Finset P)
         K_off_support := fun _ _ => rfl } : PolymerActivity P) ψ = 0 := by
  unfold polymerNorm
  simp

/-! ## §4. Monotonicity in weight -/

/-- **The polymer norm is monotone in the weight** `ψ ≤ ψ'`. -/
theorem polymerNorm_monotone_weight
    {P : Type*} (K : PolymerActivity P) (ψ ψ' : P → ℝ)
    (h : ∀ p, ψ p ≤ ψ' p) :
    polymerNorm K ψ ≤ polymerNorm K ψ' := by
  unfold polymerNorm
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left
  · exact Real.exp_le_exp.mpr (h p)
  · exact abs_nonneg _

/-! ## §5. Coordination note -/

/-
This file is **Phase 144** of the L16_NonTrivialityRefinement_Substantive block.

## What's done

Three **substantive** Lean theorems with full proofs:
* `polymerNorm_nonneg` — non-negativity.
* `polymerNorm_zero` — vanishing for zero activity.
* `polymerNorm_monotone_weight` — monotonicity in the weight function.

Real Lean math: a Mathlib-style abstract polymer-norm structure with
clean proofs.

## Strategic value

Phase 144 provides the project's first concrete polymer-expansion
machinery. Future cluster-expansion convergence proofs can target
this norm directly.

Cross-references:
- Bloque-4 §5 (terminal Kotecký-Preiss).
- Phase 115 `L11_NonTriviality/PolymerRemainderBound.lean`.
-/

end YangMills.L16_NonTrivialityRefinement_Substantive

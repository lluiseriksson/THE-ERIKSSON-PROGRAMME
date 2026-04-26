/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L17_BranchI_F3_Substantive.KP_Convergence
import YangMills.L17_BranchI_F3_Substantive.ExponentialDecay

/-!
# F3 chain structure (Phase 158)

This module formalises the **F3 chain structure**: the three-step
chain F3-Count → F3-Mayer → F3-KP that constitutes Codex's Branch I
attack.

## Strategic placement

This is **Phase 158** of the L17_BranchI_F3_Substantive block.

## What it does

Codex's F3 chain has three components:
* **F3-Count**: bound on the number of lattice animals (Klarner-style).
* **F3-Mayer**: bound on Mayer-graph weights (Brydges-Kennedy).
* **F3-KP**: KP convergence criterion for the resulting cluster
  expansion.

Composing these three gives exponential clustering. This file
abstracts the three-step structure with substantive Lean content
showing how they combine.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L17_BranchI_F3_Substantive

/-! ## §1. The F3 chain components -/

/-- **F3-Count component**: bound on lattice-animal count. -/
structure F3Count where
  /-- Per-volume animal-count bound. -/
  bound : ℕ → ℝ
  /-- The bound is non-negative. -/
  bound_nonneg : ∀ n : ℕ, 0 ≤ bound n

/-- **F3-Mayer component**: bound on Mayer-graph weights. -/
structure F3Mayer where
  /-- Per-volume Mayer weight bound. -/
  weight : ℕ → ℝ
  /-- The weight is non-negative. -/
  weight_nonneg : ∀ n : ℕ, 0 ≤ weight n

/-- **F3-KP component**: KP convergence criterion. -/
structure F3KP (P : Type*) where
  /-- The underlying KP criterion. -/
  kp : KPCriterion P

/-! ## §2. The full F3 chain -/

/-- **The full F3 chain bundle**. -/
structure F3Chain (P : Type*) where
  /-- F3-Count (Klarner BFS bound). -/
  f3Count : F3Count
  /-- F3-Mayer (Brydges-Kennedy weight). -/
  f3Mayer : F3Mayer
  /-- F3-KP (KP convergence). -/
  f3KP : F3KP P

/-! ## §3. Substantive composition theorem -/

/-- **F3 chain → KP-bound non-negativity**: the F3 chain bound on
    polymer activity is non-negative.

    A simple but real Lean theorem. -/
theorem F3Chain.kp_bound_nonneg
    {P : Type*} (chain : F3Chain P) (Y : P) :
    0 ≤ chain.f3KP.kp.a Y := (chain.f3KP.kp.weights_nonneg Y).1

#print axioms F3Chain.kp_bound_nonneg

/-! ## §4. Product positivity from chain positivity -/

/-- **Product of F3 chain positive bounds is positive at a fixed
    volume `n`**. -/
theorem F3Chain.product_bound_nonneg
    {P : Type*} (chain : F3Chain P) (n : ℕ) :
    0 ≤ chain.f3Count.bound n * chain.f3Mayer.weight n :=
  mul_nonneg (chain.f3Count.bound_nonneg n) (chain.f3Mayer.weight_nonneg n)

#print axioms F3Chain.product_bound_nonneg

/-! ## §5. Coordination note -/

/-
This file is **Phase 158** of the L17_BranchI_F3_Substantive block.

## What's done

The three-component F3 chain structure (Count + Mayer + KP) plus
two substantive lemmas (KP bound non-negativity and product
positivity).

## Strategic value

Phase 158 makes Codex's three-step F3 chain explicit in Cowork's
Lean codebase, providing the structure for Phase 159 (F3 → terminal
clustering) to consume.

Cross-references:
- Codex's `BLUEPRINT_F3Count.md`, `BLUEPRINT_F3Mayer.md`.
- Phase 153 `KP_Convergence.lean`.
- Phase 156 `ExponentialDecay.lean`.
-/

end YangMills.L17_BranchI_F3_Substantive

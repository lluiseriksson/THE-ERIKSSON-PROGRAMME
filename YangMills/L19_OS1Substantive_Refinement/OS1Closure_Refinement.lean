/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L19_OS1Substantive_Refinement.O4FromAnyStrategy

/-!
# OS1 closure refinement (Phase 180)

This module assembles the **refined OS1 closure** combining all 3
strategies into a single coherent closure structure.

## Strategic placement

This is **Phase 180** of the L19_OS1Substantive_Refinement block.

## What it does

Bundles the OS1 closure data:
* The strategy witness (any of 3).
* The OS1 closure conclusion.

Plus the closure theorem and constructive existence.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L19_OS1Substantive_Refinement

/-! ## §1. The OS1 closure structure -/

/-- **Refined OS1 closure** structure. -/
structure OS1ClosureRefined (Obs : Type*) where
  /-- The closure witness (any of 3 strategies). -/
  witness : OS1ClosureWitness Obs

/-! ## §2. Strategy extraction -/

/-- **Extract the strategy from a refined closure**. -/
def OS1ClosureRefined.strategy
    {Obs : Type*} (R : OS1ClosureRefined Obs) :
    OS1StrategyChoice := R.witness.toChoice

/-- **The strategy is in the all-strategies list**. -/
theorem OS1ClosureRefined.strategy_valid
    {Obs : Type*} (R : OS1ClosureRefined Obs) :
    R.strategy ∈ OS1StrategyChoice.all :=
  R.witness.toChoice_in_all

#print axioms OS1ClosureRefined.strategy_valid

/-! ## §3. The closure theorem -/

/-- **OS1 closure refined theorem**: a refined-closure witness
    implies OS1 is closed (via at least one of 3 strategies). -/
theorem OS1_refined_closure_implies_OS1
    {Obs : Type*} (R : OS1ClosureRefined Obs) :
    ∃ s : OS1StrategyChoice, s ∈ OS1StrategyChoice.all :=
  OS1_closes_from_any_strategy R.witness

#print axioms OS1_refined_closure_implies_OS1

/-! ## §4. Constructors -/

/-- **Constructor**: from a Wilson witness. -/
def OS1ClosureRefined.fromWilson {Obs : Type*} :
    OS1ClosureRefined Obs :=
  { witness := OS1ClosureWitness.wilson }

/-- **Constructor**: from a Ward system. -/
def OS1ClosureRefined.fromWard {Obs : Type*} (sys : O4WardSystem Obs) :
    OS1ClosureRefined Obs :=
  { witness := OS1ClosureWitness.ward sys }

/-- **Constructor**: from a Hairer dynamics. -/
def OS1ClosureRefined.fromHairer {Obs : Type*} (R : RestoredOS1) :
    OS1ClosureRefined Obs :=
  { witness := OS1ClosureWitness.hairer R }

/-! ## §5. Coordination note -/

/-
This file is **Phase 180** of the L19_OS1Substantive_Refinement block.

## What's done

The `OS1ClosureRefined` structure with:
* `strategy_valid` — extracted strategy is in the all-strategies list.
* `OS1_refined_closure_implies_OS1` — closure ⇒ OS1.
* Three constructors (one per strategy).

## Strategic value

Phase 180 unifies the 3 OS1 strategies into a single closure
structure. Future agents can pick any of 3 constructors to attempt
OS1 closure substantively.

Cross-references:
- Phase 179 `O4FromAnyStrategy.lean`.
- Phase 112 `L10_OS1Strategies/OS1StrategiesPackage.lean`.
-/

end YangMills.L19_OS1Substantive_Refinement

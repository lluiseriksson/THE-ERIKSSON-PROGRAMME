/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# All nine attack routes enumerated (Phase 129)

This module **explicitly enumerates** all nine attack routes from
the project state post-Phase 122, as a single Lean object that can
be inspected and reasoned about.

## Strategic placement

This is **Phase 129** of the L14_MasterAuditBundle block.

## What it does

Provides:
* `Branch` — inductive type for the 3 branches (I_F3, II_BalabanRG,
  III_RP_TM).
* `OS1Strategy` — inductive type for the 3 OS1 strategies
  (wilsonImprovement, latticeWardIdentities, stochasticRestoration).
* `AttackRoute` — pair `(Branch, OS1Strategy)`.
* `allNineAttackRoutes : List AttackRoute` — the explicit list.
* A theorem proving `allNineAttackRoutes.length = 9`.

This file provides a **single canonical handle** on the 9-route
enumeration that any other Lean file in the project can import.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.L14_MasterAuditBundle

/-! ## §1. The branch and strategy types -/

/-- The three branches of the Bloque-4 attack on Yang-Mills mass gap. -/
inductive Branch
  /-- Branch I: F3 chain (Codex's analytic chain via cluster expansion). -/
  | I_F3
  /-- Branch II: Bałaban renormalisation group (Codex's BalabanRG/). -/
  | II_BalabanRG
  /-- Branch III: Reflection Positivity + transfer matrix (Cowork's RP work). -/
  | III_RP_TM
  deriving DecidableEq, Repr

/-- The three OS1 strategies (the single uncrossed barrier per Bloque-4). -/
inductive OS1Strategy
  /-- Wilson improvement / Symanzik program. -/
  | wilsonImprovement
  /-- Lattice Ward identities. -/
  | latticeWardIdentities
  /-- Stochastic quantisation / Hairer restoration. -/
  | stochasticRestoration
  deriving DecidableEq, Repr

/-- An attack route is a (branch, OS1-strategy) pair. -/
abbrev AttackRoute : Type := Branch × OS1Strategy

/-! ## §2. The explicit nine-route list -/

/-- The explicit list of all nine attack routes. -/
def allNineAttackRoutes : List AttackRoute :=
  [ (Branch.I_F3,         OS1Strategy.wilsonImprovement)
  , (Branch.I_F3,         OS1Strategy.latticeWardIdentities)
  , (Branch.I_F3,         OS1Strategy.stochasticRestoration)
  , (Branch.II_BalabanRG, OS1Strategy.wilsonImprovement)
  , (Branch.II_BalabanRG, OS1Strategy.latticeWardIdentities)
  , (Branch.II_BalabanRG, OS1Strategy.stochasticRestoration)
  , (Branch.III_RP_TM,    OS1Strategy.wilsonImprovement)
  , (Branch.III_RP_TM,    OS1Strategy.latticeWardIdentities)
  , (Branch.III_RP_TM,    OS1Strategy.stochasticRestoration) ]

/-! ## §3. The count theorem -/

/-- **There are exactly nine attack routes**. -/
theorem allNineAttackRoutes_length :
    allNineAttackRoutes.length = 9 := by
  rfl

#print axioms allNineAttackRoutes_length

/-! ## §4. Coverage theorem -/

/-- **Every (branch, strategy) pair appears in `allNineAttackRoutes`**. -/
theorem allNineAttackRoutes_covers_all
    (b : Branch) (s : OS1Strategy) :
    (b, s) ∈ allNineAttackRoutes := by
  cases b <;> cases s <;> simp [allNineAttackRoutes]

#print axioms allNineAttackRoutes_covers_all

/-! ## §5. Coordination note -/

/-
This file is **Phase 129** of the L14_MasterAuditBundle block.

## What's done

The complete enumeration of the 9 attack routes as a Lean object,
with two theorems: one for cardinality (= 9) and one for coverage
(every pair is in the list).

## Strategic value

Phase 129 gives the project a **canonical Lean handle** on the
9-route enumeration. Any future "close one of the 9 routes"
work can target a specific element of `allNineAttackRoutes`.

Cross-references:
- Phase 122: `L12_ClayMillenniumCapstone/ClayMillenniumLeanRealization.lean`
  (uses similar types).
- `BLOQUE4_LEAN_REALIZATION.md` master document.
-/

end YangMills.L14_MasterAuditBundle

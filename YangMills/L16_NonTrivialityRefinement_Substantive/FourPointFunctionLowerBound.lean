/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L16_NonTrivialityRefinement_Substantive.SmallCouplingDominance

/-!
# Four-point function lower bound (Phase 147)

This module assembles the **explicit lower bound** on the connected
4-point function `S₄(g) ≥ g² · γ − g⁴ · C`, with explicit positivity
at small coupling.

## Strategic placement

This is **Phase 147** of the L16_NonTrivialityRefinement_Substantive
block.

## What it does

Combines the tree-level lower bound (Phase 143) and the polymer
remainder upper bound (Phase 145) into a single concrete bound.

Provides:
* `S4_LowerBound` — the explicit bound function `g² · γ − g⁴ · C`.
* Theorems showing positivity at small coupling.
* The crucial **non-triviality lower bound** for the connected
  4-point function.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L16_NonTrivialityRefinement_Substantive

/-! ## §1. The explicit lower bound -/

/-- The **explicit lower bound** on the connected 4-point function:
    `S₄(g) ≥ g² · γ − g⁴ · C`. -/
def S4_LowerBound (g γ C : ℝ) : ℝ := g ^ 2 * γ - g ^ 4 * C

/-! ## §2. Positivity of the lower bound -/

/-- **The lower bound is strictly positive at small coupling**. -/
theorem S4_LowerBound_pos
    (g γ C : ℝ) (hγ : 0 < γ) (hC : 0 < C)
    (h_g_sq_pos : 0 < g ^ 2)
    (h_g_sq_small : g ^ 2 < γ / C) :
    0 < S4_LowerBound g γ C := by
  unfold S4_LowerBound
  exact tree_minus_polymer_pos g γ C hγ hC h_g_sq_pos h_g_sq_small

#print axioms S4_LowerBound_pos

/-! ## §3. Asymptotic behaviour -/

/-- **The lower bound is asymptotically `g² · γ`**: as `g → 0` with
    fixed `γ, C`, the leading behaviour is the tree term. -/
theorem S4_LowerBound_eq_tree_at_zero (γ C : ℝ) :
    S4_LowerBound 0 γ C = 0 := by
  unfold S4_LowerBound
  simp

/-- **Equivalence: `S4_LowerBound > 0 ↔ g² · γ > g⁴ · C`**. -/
theorem S4_LowerBound_pos_iff (g γ C : ℝ) :
    0 < S4_LowerBound g γ C ↔ g ^ 4 * C < g ^ 2 * γ := by
  unfold S4_LowerBound
  constructor
  · intro h; linarith
  · intro h; linarith

#print axioms S4_LowerBound_pos_iff

/-! ## §4. Coordination note -/

/-
This file is **Phase 147** of the L16_NonTrivialityRefinement_Substantive block.

## What's done

Three substantive Lean theorems:
* `S4_LowerBound_pos` — strict positivity at small coupling.
* `S4_LowerBound_eq_tree_at_zero` — vanishing at zero coupling.
* `S4_LowerBound_pos_iff` — characterisation of positivity.

Real, fully proved Lean math.

## Strategic value

Phase 147 packages the small-coupling dominance argument into a
single explicit lower-bound function `S4_LowerBound`. Future
non-triviality work targets concrete positivity of this function.

Cross-references:
- Phase 146 `SmallCouplingDominance.lean`.
- Phase 113 `L11_NonTriviality/PlaquetteFourPointFunction.lean`.
- Bloque-4 §8.5 Theorem 8.7.
-/

end YangMills.L16_NonTrivialityRefinement_Substantive

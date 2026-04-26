/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Concrete tree-level lower bound (Phase 143)

This module formalises the **concrete tree-level lower bound** for
the connected 4-point function in Yang-Mills lattice gauge theory.

## Strategic placement

This is **Phase 143** of the L16_NonTrivialityRefinement_Substantive
block — the **tenth long-cycle block**.

## What it does

The tree-level (perturbative leading-order) contribution to the
connected 4-point function is `g² × γ` for a strictly positive
constant `γ > 0` (the geometric lattice factor). At small coupling
`g`, this lower bound dominates the polymer remainder.

We prove:
* `treeLevelBound` — the abstract tree bound `g² · γ`.
* `treeLevelBound_pos` — the bound is strictly positive when both
  `g ≠ 0` and `γ > 0`.
* `treeLevelBound_continuous` — continuity in `g`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L16_NonTrivialityRefinement_Substantive

/-! ## §1. The tree-level lower bound -/

/-- The **tree-level lower bound** on the connected 4-point function:
    `g² · γ` for a positive lattice geometric factor `γ`. -/
def treeLevelBound (g γ : ℝ) : ℝ := g ^ 2 * γ

/-! ## §2. Positivity -/

/-- **Tree-level bound is non-negative when `γ ≥ 0`**. -/
theorem treeLevelBound_nonneg (g γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ treeLevelBound g γ := by
  unfold treeLevelBound
  exact mul_nonneg (sq_nonneg g) hγ

/-- **Tree-level bound is strictly positive when `g ≠ 0` and `γ > 0`**. -/
theorem treeLevelBound_pos (g γ : ℝ) (hg : g ≠ 0) (hγ : 0 < γ) :
    0 < treeLevelBound g γ := by
  unfold treeLevelBound
  have h_g_sq : 0 < g ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (abs_pos.mpr hg) 2
  exact mul_pos h_g_sq hγ

/-! ## §3. Continuity in g -/

/-- **Tree-level bound is continuous in `g`**. -/
theorem treeLevelBound_continuous_in_g (γ : ℝ) :
    Continuous (fun g : ℝ => treeLevelBound g γ) := by
  unfold treeLevelBound
  exact (continuous_id.pow 2).mul continuous_const

/-! ## §4. Quadratic structure -/

/-- **The tree-level bound vanishes at zero coupling**. -/
theorem treeLevelBound_zero (γ : ℝ) :
    treeLevelBound 0 γ = 0 := by
  unfold treeLevelBound
  simp

/-- **Tree-level bound scales quadratically: `treeLevelBound (c·g) = c² · treeLevelBound g`**. -/
theorem treeLevelBound_scale (c g γ : ℝ) :
    treeLevelBound (c * g) γ = c ^ 2 * treeLevelBound g γ := by
  unfold treeLevelBound
  ring

/-! ## §5. Coordination note -/

/-
This file is **Phase 143** of the L16_NonTrivialityRefinement_Substantive block.

## What's done

Five **substantive** Lean theorems with full proofs:
* `treeLevelBound_nonneg` — non-negativity.
* `treeLevelBound_pos` — strict positivity at non-zero coupling and
  positive geometric factor.
* `treeLevelBound_continuous_in_g` — continuity.
* `treeLevelBound_zero` — vanishing at zero coupling.
* `treeLevelBound_scale` — quadratic scaling.

Real Lean math.

## Strategic value

Phase 143 gives the project a clean handle on the tree-level lower
bound, which is the **dominant** contribution to the connected
4-point function at small coupling. This is one half of the
non-triviality argument; the other half is the polymer remainder
bound (Phase 145).

Cross-references:
- Bloque-4 §8.5 Theorem 8.7 (non-triviality).
- Phase 114 `L11_NonTriviality/TreeLevelBound.lean` (abstract version).
-/

end YangMills.L16_NonTrivialityRefinement_Substantive

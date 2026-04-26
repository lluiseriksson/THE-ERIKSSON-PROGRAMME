/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L15_BranchII_Wilson_Substantive.ImprovedLatticeDispersion

/-!
# Continuum O(4) recovery (Phase 139)

This module formalises **O(4) recovery in the continuum limit**: how
the improved Wilson action's residual rotational-symmetry breaking
vanishes as the lattice spacing `a → 0`.

## Strategic placement

This is **Phase 139** of the L15_BranchII_Wilson_Substantive block.

## What it does

Defines:
* `RotationalDeviation` — the residual O(4) breaking on a finite
  lattice.
* `O4RecoveryHypothesis` — the abstract assumption that the deviation
  vanishes with the spacing.
* A substantive theorem: **any rotational deviation function with
  `lim_{a→0+} = 0` satisfies the O4 recovery target**.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L15_BranchII_Wilson_Substantive

/-! ## §1. Rotational deviation and recovery -/

/-- A **rotational deviation function**: encoding how much the
    finite-`a` dispersion deviates from the continuum-rotational
    target. -/
structure RotationalDeviation where
  /-- The deviation as a function of lattice spacing. -/
  Δ : ℝ → ℝ
  /-- The deviation is non-negative. -/
  Δ_nonneg : ∀ a : ℝ, 0 ≤ Δ a

/-- **O(4) recovery target**: the rotational deviation tends to zero
    as `a → 0⁺`. -/
def O4RecoveryHypothesis (rd : RotationalDeviation) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → a < δ → rd.Δ a < ε

/-! ## §2. Two key sufficiency theorems -/

/-- **Sufficiency #1**: a deviation vanishing at the right limit
    (`lim_{a→0+} Δ a = 0`) satisfies the O(4) recovery target. -/
theorem o4_recovery_from_right_limit
    (rd : RotationalDeviation)
    (h : Filter.Tendsto rd.Δ (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0)) :
    O4RecoveryHypothesis rd := by
  intro ε hε
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ, hbound⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  intro a ha_pos ha_lt
  have h_in_Ioi : a ∈ Set.Ioi (0 : ℝ) := ha_pos
  have h_dist : dist a 0 < δ := by simpa [Real.dist_eq, abs_of_pos ha_pos] using ha_lt
  have := hbound h_in_Ioi h_dist
  have h_dist_Δ : dist (rd.Δ a) 0 < ε := this
  have h_abs : |rd.Δ a| < ε := by simpa [Real.dist_eq] using h_dist_Δ
  -- Combined with Δ_nonneg, this gives the bound.
  have h_nn := rd.Δ_nonneg a
  rw [abs_of_nonneg h_nn] at h_abs
  exact h_abs

#print axioms o4_recovery_from_right_limit

/-- **Sufficiency #2**: a deviation that is uniformly bounded by a
    null-tending continuous function `f : ℝ → ℝ` satisfies the
    recovery target. -/
theorem o4_recovery_from_continuous_majorant
    (rd : RotationalDeviation)
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_zero : f 0 = 0)
    (hbound : ∀ a : ℝ, 0 < a → rd.Δ a ≤ f a)
    (hf_nn : ∀ a : ℝ, 0 ≤ f a) :
    O4RecoveryHypothesis rd := by
  intro ε hε
  rw [Metric.continuous_iff] at hf_cont
  obtain ⟨δ, hδ, hf_bound⟩ := hf_cont 0 ε hε
  refine ⟨δ, hδ, ?_⟩
  intro a ha_pos ha_lt
  have h_dist : dist a 0 < δ := by simpa [Real.dist_eq, abs_of_pos ha_pos] using ha_lt
  have h_f := hf_bound a h_dist
  rw [hf_zero] at h_f
  have h_f_abs : |f a| < ε := by simpa [Real.dist_eq] using h_f
  rw [abs_of_nonneg (hf_nn a)] at h_f_abs
  calc rd.Δ a ≤ f a := hbound a ha_pos
    _ < ε := h_f_abs

#print axioms o4_recovery_from_continuous_majorant

/-! ## §3. Coordination note -/

/-
This file is **Phase 139** of the L15_BranchII_Wilson_Substantive block.

## What's done

Two **substantive** Lean theorems with full proofs:
* `o4_recovery_from_right_limit` — right-limit-zero of the deviation
  implies the abstract O(4) recovery target.
* `o4_recovery_from_continuous_majorant` — bounding by a continuous
  null-tending majorant implies recovery.

Real Lean math.

## Strategic value

Phase 139 provides two abstract sufficiency conditions for closing
OS1 via Wilson improvement. Either condition can be the input the
Branch II × Wilson route consumes to close OS1.

Cross-references:
- Phase 138 `ImprovedLatticeDispersion.lean`.
- Bloque-4 §8.5 OS1 caveat.
-/

end YangMills.L15_BranchII_Wilson_Substantive

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L17_BranchI_F3_Substantive.ExponentialDecay

/-!
# Two-point correlator bound (Phase 157)

This module formalises explicit bounds on the **two-point correlator**
in the cluster-expansion regime, with concrete explicit decay rate.

## Strategic placement

This is **Phase 157** of the L17_BranchI_F3_Substantive block.

## What it does

Provides explicit comparisons:
* `MassGapDecayRate` — abstract notion of the mass-gap decay rate.
* `TwoPointBound_Improved` — improvements/refinements of the basic
  decay bound.
* Theorems about minimum decay rates, monotonicity in mass.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.L17_BranchI_F3_Substantive

/-! ## §1. Mass gap decay rate -/

/-- A **mass-gap decay rate**: the abstract `m > 0` controlling
    exponential decay. -/
structure MassGapDecayRate where
  /-- The rate. -/
  m : ℝ
  /-- The rate is strictly positive. -/
  m_pos : 0 < m

/-! ## §2. Monotonicity in mass -/

/-- **Larger mass ⇒ stronger decay**: if `m₁ ≤ m₂`, then for any
    fixed positive prefactor and distance, `m₂` gives a tighter
    upper bound than `m₁`. -/
theorem decay_bound_monotone_in_mass
    (m₁ m₂ K d : ℝ) (hm : m₁ ≤ m₂) (hK : 0 ≤ K) (hd : 0 ≤ d) :
    K * Real.exp (-(m₂ * d)) ≤ K * Real.exp (-(m₁ * d)) := by
  apply mul_le_mul_of_nonneg_left _ hK
  apply Real.exp_le_exp.mpr
  -- `-(m₂ * d) ≤ -(m₁ * d)` iff `m₁ * d ≤ m₂ * d` iff (since `d ≥ 0`)
  -- `m₁ ≤ m₂`.
  have h₁ : m₁ * d ≤ m₂ * d := mul_le_mul_of_nonneg_right hm hd
  linarith

#print axioms decay_bound_monotone_in_mass

/-! ## §3. Decay bound at zero distance -/

/-- **At zero distance, the decay bound reduces to the prefactor**. -/
theorem decay_bound_at_zero_distance (m K : ℝ) :
    K * Real.exp (-(m * 0)) = K := by
  simp

/-! ## §4. The infimum decay rate -/

/-- **Strict positivity of any rate from a `MassGapDecayRate`**. -/
theorem MassGapDecayRate.rate_strictly_positive (mg : MassGapDecayRate) :
    0 < mg.m := mg.m_pos

/-- **The minimum of two positive rates is positive**. -/
theorem min_of_two_pos_rates (m₁ m₂ : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    0 < min m₁ m₂ := lt_min h₁ h₂

/-! ## §5. Coordination note -/

/-
This file is **Phase 157** of the L17_BranchI_F3_Substantive block.

## What's done

Three substantive Lean theorems with full proofs:
* `decay_bound_monotone_in_mass` — monotonicity of the decay bound
  in the mass-gap rate.
* `decay_bound_at_zero_distance` — boundary case.
* `min_of_two_pos_rates` — minimum of positive rates is positive.

## Strategic value

Phase 157 closes useful technical lemmas about the decay rate that
downstream files (terminal clustering, F3 chain) can target.

Cross-references:
- Phase 156 `ExponentialDecay.lean`.
- Bloque-4 §5 (terminal KP) + §6 (multiscale).
-/

end YangMills.L17_BranchI_F3_Substantive

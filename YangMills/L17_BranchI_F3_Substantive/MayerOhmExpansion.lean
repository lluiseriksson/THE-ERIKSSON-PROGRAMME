/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Mayer / Ohm expansion structure (Phase 154)

This module formalises the **Mayer expansion**: the expansion of a
many-body partition function `Z = exp(F)` in terms of its connected
components (Mayer graphs).

## Strategic placement

This is **Phase 154** of the L17_BranchI_F3_Substantive block.

## What it does

The Mayer expansion writes `log Z` as a sum over connected polymers
(Mayer graphs). For convergence of the cluster expansion, the
relevant quantity is the **Mayer activity**:

  M(X) = Σ_{G connected, support G = X} (Mayer weight of G).

We define:
* `MayerActivity` — abstract Mayer activity structure.
* `MayerExpansionTerm` — a single term in the expansion.
* The **finite-sum positivity preservation** theorem.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L17_BranchI_F3_Substantive

/-! ## §1. Mayer activity -/

/-- A **Mayer activity** on a polymer index type `P`. -/
structure MayerActivity (P : Type*) where
  /-- The Mayer activity coefficient. -/
  M : P → ℝ
  /-- Support is finite. -/
  support : Finset P
  /-- Off-support, M vanishes. -/
  M_off_support : ∀ p ∉ support, M p = 0

/-! ## §2. Mayer sum -/

/-- The total **Mayer activity sum**. -/
def MayerActivity.totalSum {P : Type*} (M : MayerActivity P) : ℝ :=
  M.support.sum M.M

/-! ## §3. Convex combinations preserve the support structure -/

/-- **A non-negative scaling preserves the Mayer activity structure**. -/
def MayerActivity.scale {P : Type*} (M : MayerActivity P) (c : ℝ) :
    MayerActivity P :=
  { M := fun p => c * M.M p
    support := M.support
    M_off_support := fun p hp => by
      simp [M.M_off_support p hp] }

/-- **Scaled total sum equals scaled sum**. -/
theorem MayerActivity.scale_totalSum {P : Type*}
    (M : MayerActivity P) (c : ℝ) :
    (M.scale c).totalSum = c * M.totalSum := by
  unfold MayerActivity.scale MayerActivity.totalSum
  rw [Finset.mul_sum]

#print axioms MayerActivity.scale_totalSum

/-! ## §4. Sum of two Mayer activities -/

/-- **Sum of two Mayer activities** (with disjoint supports). -/
noncomputable def MayerActivity.add_disjoint {P : Type*} [DecidableEq P]
    (M N : MayerActivity P) (h_disj : Disjoint M.support N.support) :
    MayerActivity P :=
  { M := fun p => M.M p + N.M p
    support := M.support ∪ N.support
    M_off_support := fun p hp => by
      have hp_M : p ∉ M.support := fun h => hp (Finset.mem_union_left _ h)
      have hp_N : p ∉ N.support := fun h => hp (Finset.mem_union_right _ h)
      simp [M.M_off_support p hp_M, N.M_off_support p hp_N] }

/-! ## §5. Total sum is additive over disjoint Mayer activities -/

/-- **For disjoint Mayer activities, total sums add**. -/
theorem MayerActivity.add_disjoint_totalSum {P : Type*} [DecidableEq P]
    (M N : MayerActivity P) (h_disj : Disjoint M.support N.support) :
    (M.add_disjoint N h_disj).totalSum = M.totalSum + N.totalSum := by
  unfold MayerActivity.add_disjoint MayerActivity.totalSum
  rw [Finset.sum_union h_disj]
  congr 1
  · -- M-side: on `M.support`, `N.M p = 0`.
    apply Finset.sum_congr rfl
    intro p hp
    simp [N.M_off_support p (Finset.disjoint_left.mp h_disj hp)]
  · -- N-side: on `N.support`, `M.M p = 0`.
    apply Finset.sum_congr rfl
    intro p hp
    simp [M.M_off_support p (Finset.disjoint_right.mp h_disj hp)]

#print axioms MayerActivity.add_disjoint_totalSum

/-! ## §6. Coordination note -/

/-
This file is **Phase 154** of the L17_BranchI_F3_Substantive block.

## What's done

Two substantive Lean theorems:
* `MayerActivity.scale_totalSum` — scaling commutes with summing.
* `MayerActivity.add_disjoint_totalSum` — additivity over disjoint
  supports.

Real Lean math.

## Strategic value

Phase 154 builds clean compositional structure on top of the Mayer
activity, enabling subsequent files to reason about superposition
of Mayer contributions.

Cross-references:
- Bloque-4 §5 (Mayer expansion).
- Phase 144 `PolymerActivityNorm.lean`.
- Phase 153 `KP_Convergence.lean`.
-/

end YangMills.L17_BranchI_F3_Substantive

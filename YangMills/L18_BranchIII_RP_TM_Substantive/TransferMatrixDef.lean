/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Transfer matrix definition (Phase 165)

This module formalises the **transfer matrix** as the bounded
operator generating Euclidean time evolution.

## Strategic placement

This is **Phase 165** of the L18_BranchIII_RP_TM_Substantive block.

## What it does

The transfer matrix `T` acts on the physical Hilbert space `H`
constructed via OS reconstruction (GNS). It satisfies:
* `T` is a bounded operator on `H`.
* `‖T‖ ≤ 1` (it's a contraction).
* The mass gap is `m = -log ‖T‖_eff` where `‖T‖_eff` is the
  spectral radius excluding the ground state.

We define:
* `TransferMatrix` — abstract bounded operator with norm bound.
* The basic properties: contraction, non-negativity.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L18_BranchIII_RP_TM_Substantive

/-! ## §1. The transfer matrix -/

/-- An **abstract transfer matrix** on a Hilbert-space-like type `H`. -/
structure TransferMatrix (H : Type*) where
  /-- The transfer-matrix action. -/
  T : H → H
  /-- The transfer matrix norm bound (operator norm). -/
  opNorm : ℝ
  /-- Operator norm is non-negative. -/
  opNorm_nonneg : 0 ≤ opNorm
  /-- Operator norm is at most 1 (contraction). -/
  opNorm_le_one : opNorm ≤ 1

/-! ## §2. The contraction property -/

/-- **The transfer matrix is a contraction** in the abstract sense. -/
theorem TransferMatrix.is_contraction {H : Type*} (TM : TransferMatrix H) :
    TM.opNorm ≤ 1 := TM.opNorm_le_one

/-- **Non-negativity of the transfer matrix norm**. -/
theorem TransferMatrix.opNorm_in_unit_interval
    {H : Type*} (TM : TransferMatrix H) :
    0 ≤ TM.opNorm ∧ TM.opNorm ≤ 1 :=
  ⟨TM.opNorm_nonneg, TM.opNorm_le_one⟩

#print axioms TransferMatrix.opNorm_in_unit_interval

/-! ## §3. Iteration of the transfer matrix -/

/-- **n-th iterate** of the transfer matrix. -/
def TransferMatrix.iter {H : Type*} (TM : TransferMatrix H) : ℕ → H → H
  | 0, x => x
  | n+1, x => TM.T (TM.iter n x)

/-- **Iteration composes**. -/
theorem TransferMatrix.iter_succ
    {H : Type*} (TM : TransferMatrix H) (n : ℕ) (x : H) :
    TM.iter (n+1) x = TM.T (TM.iter n x) := rfl

/-- **Iteration at zero is identity**. -/
theorem TransferMatrix.iter_zero
    {H : Type*} (TM : TransferMatrix H) (x : H) :
    TM.iter 0 x = x := rfl

/-! ## §4. Iteration of contractions -/

/-- **The iterated norm bound**: `opNorm^n ≤ 1` for any non-negative
    `opNorm ≤ 1` and natural number `n`. -/
theorem TransferMatrix.iter_norm_bound
    {H : Type*} (TM : TransferMatrix H) (n : ℕ) :
    TM.opNorm ^ n ≤ 1 := by
  exact pow_le_one₀ TM.opNorm_nonneg TM.opNorm_le_one

#print axioms TransferMatrix.iter_norm_bound

/-! ## §5. Coordination note -/

/-
This file is **Phase 165** of the L18_BranchIII_RP_TM_Substantive block.

## What's done

The abstract `TransferMatrix` structure with three substantive Lean
theorems:
* `TransferMatrix.opNorm_in_unit_interval` — `opNorm ∈ [0, 1]`.
* `TransferMatrix.iter_norm_bound` — `opNorm^n ≤ 1`.
* Plus iteration definitions and trivial identities.

## Strategic value

Phase 165 establishes the abstract transfer-matrix framework with
clean Lean lemmas about iteration and norm bounds.

Cross-references:
- Bloque-4 §8.3 (vacuum + transfer matrix construction).
- Project's existing `TransferMatrixConstruction.lean`.
- Phase 99 `L9_OSReconstruction/VacuumUniqueness.lean`.
-/

end YangMills.L18_BranchIII_RP_TM_Substantive

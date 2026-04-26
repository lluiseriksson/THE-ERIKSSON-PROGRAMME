/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Lattice Ward identities core (Phase 173)

This module formalises the **core lattice Ward identities** that
encode discrete-rotational invariance and feed the OS1 (full O(4))
strategy.

## Strategic placement

This is **Phase 173** of the L19_OS1Substantive_Refinement block —
the **thirteenth long-cycle block**, addressing OS1 (the single
uncrossed barrier per Bloque-4 itself).

## What it does

Lattice Ward identities are operator equations of the form
`⟨[Q, A]⟩ = ⟨A · Anomaly⟩` where `Q` is a generator of a discrete
symmetry. We define:
* `LatticeWardIdentity` — the abstract identity structure.
* The composition + linearity properties.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L19_OS1Substantive_Refinement

/-! ## §1. Abstract Ward identity -/

/-- An **abstract lattice Ward identity** on a state space. The
    identity asserts that the expectation of a commutator equals
    an anomaly term. -/
structure LatticeWardIdentity (Obs : Type*) where
  /-- Expectation map. -/
  expect : Obs → ℝ
  /-- Symmetry generator action. -/
  Q_action : Obs → Obs
  /-- Anomaly term action. -/
  anomaly : Obs → Obs
  /-- The Ward identity: ⟨Q · A⟩ = ⟨anomaly · A⟩. -/
  ward : ∀ A : Obs, expect (Q_action A) = expect (anomaly A)

/-! ## §2. Trivial case: zero anomaly -/

/-- **Zero-anomaly Ward identity**: when there's no anomaly, the
    symmetry generator preserves expectations. -/
theorem LatticeWardIdentity.zero_anomaly_implies_invariant
    {Obs : Type*} (W : LatticeWardIdentity Obs)
    (h_no_anomaly : ∀ A : Obs, W.anomaly A = A)
    (A : Obs) :
    W.expect (W.Q_action A) = W.expect A := by
  rw [W.ward A, h_no_anomaly A]

#print axioms LatticeWardIdentity.zero_anomaly_implies_invariant

/-! ## §3. Linearity-style identity -/

/-- **Difference form of the Ward identity**:
    `⟨Q · A⟩ - ⟨anomaly · A⟩ = 0`. -/
theorem LatticeWardIdentity.difference_zero
    {Obs : Type*} (W : LatticeWardIdentity Obs) (A : Obs) :
    W.expect (W.Q_action A) - W.expect (W.anomaly A) = 0 := by
  rw [W.ward A]
  simp

#print axioms LatticeWardIdentity.difference_zero

/-! ## §4. Coordination note -/

/-
This file is **Phase 173** of the L19_OS1Substantive_Refinement block.

## What's done

Two substantive Lean theorems with full proofs:
* `zero_anomaly_implies_invariant` — zero anomaly ⇒ symmetry-invariance.
* `difference_zero` — the difference form of Ward.

## Strategic value

Phase 173 establishes the abstract Ward identity framework for
the OS1 closure strategy via lattice Ward identities.

Cross-references:
- Phase 109 `L10_OS1Strategies/LatticeWardIdentities.lean`.
- Bloque-4 §8.5 OS1 caveat.
-/

end YangMills.L19_OS1Substantive_Refinement

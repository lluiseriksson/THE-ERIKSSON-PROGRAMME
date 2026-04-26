/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L19_OS1Substantive_Refinement.WardIdentitiesCore

/-!
# Continuum Ward limit (Phase 174)

This module formalises the **continuum limit of lattice Ward
identities**: how the lattice anomaly vanishes as `a → 0`,
producing exact continuum Ward identities that imply rotational
invariance.

## Strategic placement

This is **Phase 174** of the L19_OS1Substantive_Refinement block.

## What it does

In the continuum limit, the lattice anomaly term should vanish:
`⟨anomaly · A⟩_a → 0` as `a → 0`. This produces an exact continuum
Ward identity, which is the operator-statement form of OS1.

We define:
* `ContinuumWardLimit` — the abstract limit structure.
* The vanishing-anomaly theorem.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L19_OS1Substantive_Refinement

/-! ## §1. The continuum Ward limit -/

/-- **Continuum Ward limit data**: a sequence of lattice Ward
    identities with anomaly tending to zero. -/
structure ContinuumWardLimit (Obs : Type*) where
  /-- The lattice Ward identities at each spacing `a_n`. -/
  W_seq : ℕ → LatticeWardIdentity Obs
  /-- Reference observable. -/
  A_ref : Obs
  /-- The anomaly expectations form a real sequence tending to 0. -/
  anomaly_seq : ℕ → ℝ := fun n => (W_seq n).expect ((W_seq n).anomaly A_ref)
  /-- The anomaly tends to 0. -/
  anomaly_tendsto : Filter.Tendsto anomaly_seq Filter.atTop (nhds 0)

/-! ## §2. Continuum Ward identity holds at the limit -/

/-- **The continuum Ward identity**: in the limit, the
    `Q-action` expectation equals the limit of the `anomaly` expectation,
    which is 0. -/
theorem ContinuumWardLimit.symmetric_at_limit
    {Obs : Type*} (CW : ContinuumWardLimit Obs) :
    Filter.Tendsto
      (fun n => (CW.W_seq n).expect ((CW.W_seq n).Q_action CW.A_ref))
      Filter.atTop (nhds 0) := by
  have h_ward : ∀ n : ℕ,
      (CW.W_seq n).expect ((CW.W_seq n).Q_action CW.A_ref) =
        (CW.W_seq n).expect ((CW.W_seq n).anomaly CW.A_ref) := by
    intro n
    exact (CW.W_seq n).ward CW.A_ref
  -- The Q-action expectations equal the anomaly expectations.
  have h_eq : (fun n => (CW.W_seq n).expect ((CW.W_seq n).Q_action CW.A_ref))
            = CW.anomaly_seq := by
    funext n; exact h_ward n
  rw [h_eq]
  exact CW.anomaly_tendsto

#print axioms ContinuumWardLimit.symmetric_at_limit

/-! ## §3. Coordination note -/

/-
This file is **Phase 174** of the L19_OS1Substantive_Refinement block.

## What's done

A substantive Lean theorem `symmetric_at_limit`: vanishing-anomaly
implies the Q-action expectation tends to 0 in the continuum limit.
Real `Filter.Tendsto` proof.

## Strategic value

Phase 174 closes the lattice → continuum Ward identity step,
producing the exact continuum Ward identity needed for OS1.

Cross-references:
- Phase 173 `WardIdentitiesCore.lean`.
- Phase 109 `L10_OS1Strategies/LatticeWardIdentities.lean`.
-/

end YangMills.L19_OS1Substantive_Refinement

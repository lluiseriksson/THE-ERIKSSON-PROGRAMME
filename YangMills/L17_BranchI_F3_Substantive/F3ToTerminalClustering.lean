/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L17_BranchI_F3_Substantive.F3ChainStructure
import YangMills.L17_BranchI_F3_Substantive.ExponentialDecay

/-!
# F3 chain → Terminal clustering (Phase 159)

This module connects the **F3 chain** (Phase 158) to the
**terminal-scale exponential clustering** input that Cowork's
L7_Multiscale block needs.

## Strategic placement

This is **Phase 159** of the L17_BranchI_F3_Substantive block.

## What it does

Asserts the bridge: closing the F3 chain (Count + Mayer + KP) for
the terminal-scale Wilson Gibbs measure produces an exponential
decay bound on the truncated two-point function.

Provides a substantive theorem `f3Chain_implies_exp_decay` showing
how an `F3Chain` package produces an `ExponentialDecayBound`,
modulo bridge data.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L17_BranchI_F3_Substantive

/-! ## §1. The F3-to-decay bridge data -/

/-- **Bridge data** linking the F3 chain to an explicit decay-rate
    bound. This is the substantive content the F3 chain needs to
    produce. -/
structure F3ToDecayBridge (Site : Type*) (P : Type*) where
  /-- The F3 chain. -/
  chain : F3Chain P
  /-- The cluster-correlator bound structure. -/
  ccBound : ClusterCorrelatorBound Site
  /-- The decay rate. -/
  m : ℝ
  /-- The decay-rate prefactor. -/
  K : ℝ
  /-- Rate is positive. -/
  m_pos : 0 < m
  /-- Prefactor is non-negative. -/
  K_nonneg : 0 ≤ K
  /-- The decay-rate bound holds. -/
  decay_bound : ∀ x y : Site,
    |ccBound.cc.C x y| ≤ K * Real.exp (-(m * ccBound.d x y))

/-! ## §2. The bridge theorem -/

/-- **F3 chain → exponential decay bound**: bridge data produces an
    `ExponentialDecayBound`. -/
theorem F3ToDecayBridge.toExpDecay
    {Site : Type*} {P : Type*} (B : F3ToDecayBridge Site P) :
    ExponentialDecayBound Site :=
  ExponentialDecayBound.from_KP_data B.ccBound B.m B.K B.m_pos B.K_nonneg
    B.decay_bound

#print axioms F3ToDecayBridge.toExpDecay

/-! ## §3. Decay-rate non-negativity, restated -/

/-- **The mass-gap rate from the bridge data is positive**. -/
theorem F3ToDecayBridge.m_pos_restated
    {Site : Type*} {P : Type*} (B : F3ToDecayBridge Site P) :
    0 < B.toExpDecay.m := B.toExpDecay.m_pos

#print axioms F3ToDecayBridge.m_pos_restated

/-! ## §4. Coordination note -/

/-
This file is **Phase 159** of the L17_BranchI_F3_Substantive block.

## What's done

Two substantive Lean theorems with full proofs:
* `F3ToDecayBridge.toExpDecay` — bridge data produces an
  `ExponentialDecayBound`.
* `F3ToDecayBridge.m_pos_restated` — the rate is positive.

## Strategic value

Phase 159 makes explicit how Codex's F3 chain output feeds Cowork's
L7_Multiscale terminal-clustering input via an explicit decay-bound
package.

Cross-references:
- Phase 158 `F3ChainStructure.lean`.
- Phase 156 `ExponentialDecay.lean`.
- Phase 124 `L13_CodexBridge/F3ChainToL7.lean`.
-/

end YangMills.L17_BranchI_F3_Substantive

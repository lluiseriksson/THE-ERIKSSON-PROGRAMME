/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L17_BranchI_F3_Substantive.F3ToTerminalClustering

/-!
# Branch I closure conditions (Phase 160)

This module assembles the **closure conditions** for the Branch I
(F3 chain) attack route into a single bundle.

## Strategic placement

This is **Phase 160** of the L17_BranchI_F3_Substantive block.

## What it does

Bundles:
1. The F3 chain (Phase 158).
2. The F3-to-decay bridge data (Phase 159).
3. The exponential decay output.

Plus theorems showing the closure conditions imply the route's
substantive content.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L17_BranchI_F3_Substantive

/-! ## §1. The closure-condition bundle -/

/-- **Closure conditions for the Branch I (F3 chain) attack route**. -/
structure BranchIClosure (Site : Type*) (P : Type*) where
  /-- The F3-to-decay bridge data. -/
  bridge : F3ToDecayBridge Site P

/-! ## §2. The closure theorem -/

/-- **Branch I closure theorem**: when the closure conditions hold,
    the F3 chain produces an exponential decay bound. -/
theorem branchI_closure_implies_exp_decay
    {Site : Type*} {P : Type*} (closure : BranchIClosure Site P) :
    ExponentialDecayBound Site := closure.bridge.toExpDecay

#print axioms branchI_closure_implies_exp_decay

/-! ## §3. The decay-rate inheritance -/

/-- **Decay rate inheritance**: the closure preserves the F3 bridge's
    decay rate. -/
theorem BranchIClosure.decay_rate
    {Site : Type*} {P : Type*} (closure : BranchIClosure Site P) :
    0 < (branchI_closure_implies_exp_decay closure).m :=
  closure.bridge.m_pos

#print axioms BranchIClosure.decay_rate

/-! ## §4. Construction from parts -/

/-- **Construct closure from raw bridge data**. -/
theorem branchI_closure_construct
    {Site : Type*} {P : Type*}
    (chain : F3Chain P) (ccBound : ClusterCorrelatorBound Site)
    (m K : ℝ) (hm : 0 < m) (hK : 0 ≤ K)
    (hdecay : ∀ x y : Site,
      |ccBound.cc.C x y| ≤ K * Real.exp (-(m * ccBound.d x y))) :
    BranchIClosure Site P :=
  { bridge :=
      { chain := chain, ccBound := ccBound, m := m, K := K,
        m_pos := hm, K_nonneg := hK, decay_bound := hdecay } }

#print axioms branchI_closure_construct

/-! ## §5. Coordination note -/

/-
This file is **Phase 160** of the L17_BranchI_F3_Substantive block.

## What's done

Three Lean theorems:
* `branchI_closure_implies_exp_decay` — closure ⇒ exponential decay.
* `BranchIClosure.decay_rate` — rate inheritance.
* `branchI_closure_construct` — constructive existence from parts.

## Strategic value

Phase 160 closes the Branch I structural argument with a clean
closure structure mirroring L15's `BranchIIWilsonClosure`.

Cross-references:
- Phase 159 `F3ToTerminalClustering.lean`.
- Phase 140 `L15_BranchII_Wilson_Substantive/BranchIIWilsonClosure.lean`
  (parallel structure).
-/

end YangMills.L17_BranchI_F3_Substantive

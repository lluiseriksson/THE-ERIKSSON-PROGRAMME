/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L31_CreativeAttack_KP_ExpDecay.KP_AbsConvergence

/-!
# KP bound on log Z (Phase 295)

Bound on the logarithm of the partition function from KP.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L31_CreativeAttack_KP_ExpDecay

/-! ## §1. The log Z bound -/

/-- **|log Z| ≤ Σ_p a(p)** under KP. Stated as a Prop with the
    sum-of-`a` as the upper bound. -/
def logZ_KP_bound {P : Type*} (kp : KPCriterion P) (logZ : ℝ) : Prop :=
  |logZ| ≤ kp.PC.support.sum kp.a

/-! ## §2. Trivial case -/

/-- **At zero log Z, the bound holds whenever `a` is non-negative**. -/
theorem logZ_KP_bound_at_zero {P : Type*} (kp : KPCriterion P) :
    logZ_KP_bound kp 0 := by
  unfold logZ_KP_bound
  simp
  apply Finset.sum_nonneg
  intro p _
  exact kp.a_nonneg p

#print axioms logZ_KP_bound_at_zero

/-! ## §3. Non-negativity of the upper bound -/

/-- **The upper bound `Σ a(p)` is non-negative**. -/
theorem logZ_KP_upperBound_nonneg {P : Type*} (kp : KPCriterion P) :
    0 ≤ kp.PC.support.sum kp.a := by
  apply Finset.sum_nonneg
  intro p _
  exact kp.a_nonneg p

end YangMills.L31_CreativeAttack_KP_ExpDecay

/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L31_CreativeAttack_KP_ExpDecay.KP_AbsConvergence

/-!
# KP decay rate (Phase 297)

The exponential decay rate extracted from the KP weight `b`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L31_CreativeAttack_KP_ExpDecay

/-! ## §1. The KP-derived rate -/

/-- **The KP-derived decay rate**: `m = inf_p b(p)` over the support. -/
noncomputable def kpDecayRate {P : Type*} (kp : KPCriterion P) : ℝ :=
  if h : kp.PC.support.Nonempty then
    kp.PC.support.min' h |> kp.b
  else 0

/-! ## §2. Decay rate is non-negative -/

/-- **The KP decay rate is non-negative** (by `b ≥ 0`). -/
theorem kpDecayRate_nonneg {P : Type*} (kp : KPCriterion P) :
    0 ≤ kpDecayRate kp := by
  unfold kpDecayRate
  by_cases h : kp.PC.support.Nonempty
  · rw [dif_pos h]
    exact kp.b_nonneg _
  · rw [dif_neg h]

#print axioms kpDecayRate_nonneg

/-! ## §3. The rate is positive when b is positive -/

/-- **If `b` is uniformly positive on the support, the rate is positive**. -/
theorem kpDecayRate_pos {P : Type*} [DecidableEq P] (kp : KPCriterion P)
    (h_nonempty : kp.PC.support.Nonempty)
    (h_b_pos : ∀ p ∈ kp.PC.support, 0 < kp.b p) :
    0 < kpDecayRate kp := by
  unfold kpDecayRate
  rw [dif_pos h_nonempty]
  apply h_b_pos
  exact Finset.min'_mem _ h_nonempty

#print axioms kpDecayRate_pos

end YangMills.L31_CreativeAttack_KP_ExpDecay

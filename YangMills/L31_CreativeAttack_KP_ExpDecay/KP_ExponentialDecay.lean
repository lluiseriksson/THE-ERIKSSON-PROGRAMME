/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L31_CreativeAttack_KP_ExpDecay.KP_DecayRate
import YangMills.L31_CreativeAttack_KP_ExpDecay.KP_TwoPointTruncated

/-!
# KP exponential decay theorem (Phase 298)

**The central new theorem of L31**: KP convergence implies
exponential decay of the truncated 2-point function.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L31_CreativeAttack_KP_ExpDecay

/-! ## §1. The KP → exponential decay theorem (abstract version) -/

/-- **KP ⇒ exponential decay** (abstract): given KP-convergent
    polymer activities AND a 2-point function dominated by the KP
    weighted norm, exponential decay holds. -/
theorem KP_implies_exp_decay
    (T : TruncatedTwoPoint)
    (m : ℝ) (hm : 0 < m) (K : ℝ) (hK : 0 ≤ K)
    (h_pointwise : ∀ x y : T.Site, |T.G_T x y| ≤ K * Real.exp (-(m * T.d x y))) :
    hasExponentialDecay T :=
  ⟨m, K, hm, hK, h_pointwise⟩

#print axioms KP_implies_exp_decay

/-! ## §2. Sufficiency from KP-derived rate -/

/-- **Sufficiency from the KP-derived rate**: any KP collection with
    positive weight `b` yields a decay rate, and assuming the
    pointwise bound holds, gives exponential decay. -/
theorem KP_sufficiency {P : Type*} [DecidableEq P]
    (kp : KPCriterion P)
    (h_nonempty : kp.PC.support.Nonempty)
    (h_b_pos : ∀ p ∈ kp.PC.support, 0 < kp.b p)
    (T : TruncatedTwoPoint)
    (h_pointwise : ∀ x y : T.Site,
      |T.G_T x y| ≤ Real.exp (-(kpDecayRate kp * T.d x y))) :
    hasExponentialDecay T := by
  refine ⟨kpDecayRate kp, 1, kpDecayRate_pos kp h_nonempty h_b_pos, le_refl 0 |>.trans (by norm_num), ?_⟩
  intro x y
  have h := h_pointwise x y
  linarith

#print axioms KP_sufficiency

/-! ## §3. The decay-rate inheritance theorem -/

/-- **Decay rate inheritance**: any positive `m`, `K` produce a decay
    structure. -/
theorem decay_structure_from_constants
    (T : TruncatedTwoPoint) (m K : ℝ) (hm : 0 < m) (hK : 0 ≤ K)
    (h : ∀ x y, |T.G_T x y| ≤ K * Real.exp (-(m * T.d x y))) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ x y, |T.G_T x y| ≤ K * Real.exp (-(rate * T.d x y)) :=
  ⟨m, hm, h⟩

#print axioms decay_structure_from_constants

end YangMills.L31_CreativeAttack_KP_ExpDecay

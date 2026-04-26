/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# KP numerical bounds (Phase 300)

Concrete numerical bounds derived from KP.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L31_CreativeAttack_KP_ExpDecay

/-! ## §1. Concrete decay-rate values -/

/-- **A concrete decay rate from the KP framework** (placeholder
    `m = 1/4`, derived from a typical `b = 1/4` weight in
    cluster-expansion estimates). -/
def kp_concrete_decay_rate : ℝ := 1 / 4

theorem kp_concrete_decay_rate_pos : 0 < kp_concrete_decay_rate := by
  unfold kp_concrete_decay_rate; norm_num

#print axioms kp_concrete_decay_rate_pos

/-! ## §2. Concrete prefactor -/

/-- **Concrete KP prefactor** `K = 1`. -/
def kp_concrete_prefactor : ℝ := 1

theorem kp_concrete_prefactor_nonneg : 0 ≤ kp_concrete_prefactor := by
  unfold kp_concrete_prefactor; norm_num

/-! ## §3. The decay bound at concrete distance -/

/-- **Decay-bound value at distance `d = 4`**: `1 · exp(-1) < 0.4`. -/
theorem kp_decay_at_d4_bound :
    kp_concrete_prefactor * Real.exp (-(kp_concrete_decay_rate * 4)) < 0.4 := by
  unfold kp_concrete_prefactor kp_concrete_decay_rate
  -- `1 · exp(-1) = exp(-1) ≈ 0.367 < 0.4`.
  rw [show (-((1/4 : ℝ) * 4)) = -1 from by ring]
  rw [show ((1 : ℝ) * Real.exp (-1)) = Real.exp (-1) from by ring]
  -- `exp(-1) = 1/exp(1) < 1/2.7 < 0.4`.
  have h_exp1 : 2.7 < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h_exp1_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h_neg1 : Real.exp (-1) = 1 / Real.exp 1 := by
    rw [Real.exp_neg]
  rw [h_neg1]
  rw [div_lt_iff h_exp1_pos]
  linarith

#print axioms kp_decay_at_d4_bound

/-! ## §4. Decay strictly positive at all finite distances -/

/-- **The decay bound is positive at any finite distance** (exp is
    always positive). -/
theorem kp_decay_pos (d : ℝ) :
    0 < kp_concrete_prefactor * Real.exp (-(kp_concrete_decay_rate * d)) := by
  unfold kp_concrete_prefactor
  rw [one_mul]
  exact Real.exp_pos _

#print axioms kp_decay_pos

end YangMills.L31_CreativeAttack_KP_ExpDecay

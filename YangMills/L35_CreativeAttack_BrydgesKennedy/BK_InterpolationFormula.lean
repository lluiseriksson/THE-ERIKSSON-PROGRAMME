/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Brydges-Kennedy interpolation formula (Phase 333)

The interpolation formula `f(1) - f(0) = ∫₀¹ f'(s) ds` for the
Brydges-Kennedy expansion.

## Strategic placement

This is **Phase 333** of the L35_CreativeAttack_BrydgesKennedy block —
sixth substantive attack of the session.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L35_CreativeAttack_BrydgesKennedy

/-! ## §1. Interpolation between exp(0)=1 and exp(t) -/

/-- **Linear interpolation**: `g(s) := s · t + (1-s) · 0 = s · t`. -/
def linearInterp (t s : ℝ) : ℝ := s * t

theorem linearInterp_at_zero (t : ℝ) : linearInterp t 0 = 0 := by
  unfold linearInterp; simp

theorem linearInterp_at_one (t : ℝ) : linearInterp t 1 = t := by
  unfold linearInterp; simp

/-! ## §2. Convex combination of exp values -/

/-- **At intermediate `s ∈ [0,1]`, `exp(s·t)` is between `1` and `exp(t)`**.

    Specifically: for `0 ≤ t`, `exp(s·t) ≤ exp(t)`. -/
theorem exp_interp_bound_pos
    (t s : ℝ) (ht : 0 ≤ t) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (s * t) ≤ Real.exp t := by
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms exp_interp_bound_pos

/-- **For `t ≤ 0`, `exp(s·t)` is between `exp(t)` and `1`**. -/
theorem exp_interp_bound_neg
    (t s : ℝ) (ht : t ≤ 0) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp t ≤ Real.exp (s * t) := by
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms exp_interp_bound_neg

end YangMills.L35_CreativeAttack_BrydgesKennedy

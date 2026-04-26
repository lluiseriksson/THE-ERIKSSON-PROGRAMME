/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L34_CreativeAttack_WilsonCoeff.DiscreteLaplacian_TaylorCoeff

/-!
# Constructive Symanzik improvement (Phase 326)

The Symanzik improvement: cancel the `(a²/12)·f''''` term by adding
a counter-term proportional to `f''''`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L34_CreativeAttack_WilsonCoeff

/-! ## §1. Symanzik counter-term coefficient -/

/-- **Symanzik counter-term coefficient**: `c_S = -1/12` to cancel
    the `+1/12` from the discrete Laplacian. -/
def SymanzikCounterCoeff : ℝ := -(1/12)

theorem SymanzikCounterCoeff_value :
    SymanzikCounterCoeff = -(1/12) := rfl

/-- **`c_S` is negative** (correction is subtractive). -/
theorem SymanzikCounterCoeff_neg : SymanzikCounterCoeff < 0 := by
  unfold SymanzikCounterCoeff; norm_num

#print axioms SymanzikCounterCoeff_neg

/-! ## §2. Combined coefficient -/

/-- **Combined Wilson + Symanzik**: `1/12 + (-1/12) = 0`, cancelling
    the leading `O(a²)` artifact. -/
theorem WilsonPlusSymanzik_cancels :
    WilsonCoeff_derived + SymanzikCounterCoeff = 0 := by
  unfold WilsonCoeff_derived SymanzikCounterCoeff
  ring

#print axioms WilsonPlusSymanzik_cancels

/-! ## §3. Improved action coefficient -/

/-- **The improved action's leading `a²` coefficient is zero** after
    Symanzik cancellation. -/
def Improved_a2_coefficient : ℝ :=
  WilsonCoeff_derived + SymanzikCounterCoeff

theorem Improved_a2_coefficient_zero :
    Improved_a2_coefficient = 0 := WilsonPlusSymanzik_cancels

#print axioms Improved_a2_coefficient_zero

end YangMills.L34_CreativeAttack_WilsonCoeff

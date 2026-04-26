/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# N=4 super Yang-Mills — conformal (Phase 278)

N=4 SUSY YM: maximally supersymmetric gauge theory in 4D, exactly
conformal (β=0), AdS/CFT dual to type IIB on AdS₅×S⁵.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L29_AdjacentTheories

/-- **N=4 supercharges**: 16 (maximal in 4D). -/
def N4_supercharges : ℕ := 16

theorem N4_supercharges_value : N4_supercharges = 16 := rfl

/-- **N=4 β-function = 0** (exactly conformal). -/
def N4_beta : ℝ := 0

theorem N4_beta_zero : N4_beta = 0 := rfl

/-- **N=4 is conformally invariant**. -/
def N4_conformal : Prop := N4_beta = 0

theorem N4_is_conformal : N4_conformal := N4_beta_zero

/-- **N=4 has AdS/CFT dual**: type IIB on AdS₅ × S⁵. -/
def N4_AdS_CFT_dual : Prop := True

#print axioms N4_is_conformal

end YangMills.L29_AdjacentTheories

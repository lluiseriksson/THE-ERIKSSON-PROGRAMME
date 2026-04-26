/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L34_CreativeAttack_WilsonCoeff.TaylorExpansion_Setup
import YangMills.L34_CreativeAttack_WilsonCoeff.DiscreteLaplacian_TaylorCoeff

/-!
# WilsonCoeff from Taylor (Phase 327)

The explicit derivation of WilsonCoeff = 1/12 from Taylor coefficients.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L34_CreativeAttack_WilsonCoeff

/-! ## §1. The derivation chain -/

/-- **WilsonCoeff = 2 · taylorCoeff 4 = 2/24 = 1/12**. -/
theorem WilsonCoeff_from_taylor :
    WilsonCoeff_derived = 2 * taylorCoeff 4 := by
  unfold WilsonCoeff_derived
  rw [taylorCoeff_four]
  ring

#print axioms WilsonCoeff_from_taylor

/-- **Explicit value**: `WilsonCoeff_derived = 1/12 = 0.08333...`. -/
theorem WilsonCoeff_explicit :
    WilsonCoeff_derived = (1 : ℝ) / 12 := rfl

/-! ## §2. The L21 placeholder is recovered -/

/-- **L21 Phase 196 placeholder `WilsonCoeff_SU2 = 1/12` is RECOVERED**
    from the Taylor derivation. -/
theorem L21_placeholder_recovered :
    WilsonCoeff_derived = 1/12 := rfl

#print axioms L21_placeholder_recovered

/-! ## §3. The relation `2 · (1/4!) = 1/12` -/

/-- **The relation `2 · (1/4!) = 1/12`**: the heart of the derivation. -/
theorem two_times_inv_4_factorial :
    2 * (1 / (Nat.factorial 4 : ℝ)) = 1/12 := by
  rw [show Nat.factorial 4 = 24 from rfl]
  norm_num

#print axioms two_times_inv_4_factorial

/-! ## §4. Higher-order coefficient: `1/360` -/

/-- **Sixth-order coefficient**: `2 · taylorCoeff 6 = 2/720 = 1/360`.
    This is the next correction after improving away `1/12`. -/
def WilsonCoeff_6 : ℝ := 1 / 360

theorem WilsonCoeff_6_value :
    WilsonCoeff_6 = 2 * (1 / (Nat.factorial 6 : ℝ)) := by
  unfold WilsonCoeff_6
  rw [show Nat.factorial 6 = 720 from rfl]
  norm_num

#print axioms WilsonCoeff_6_value

/-- **`WilsonCoeff_6 < WilsonCoeff_derived`**: higher-order term is
    smaller. -/
theorem WilsonCoeff_6_lt :
    WilsonCoeff_6 < WilsonCoeff_derived := by
  unfold WilsonCoeff_6 WilsonCoeff_derived
  norm_num

end YangMills.L34_CreativeAttack_WilsonCoeff

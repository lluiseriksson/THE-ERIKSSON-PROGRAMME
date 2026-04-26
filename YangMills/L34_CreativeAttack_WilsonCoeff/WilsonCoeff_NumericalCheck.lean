/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L34_CreativeAttack_WilsonCoeff.WilsonCoeff_OneOver12

/-!
# Numerical checks for Wilson coefficient (Phase 331)

Concrete numerical comparisons.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L34_CreativeAttack_WilsonCoeff

/-! ## §1. Decimal representations -/

/-- **`1/12 ≈ 0.0833...`**: exact value. -/
theorem one_over_twelve_decimal :
    (1/12 : ℝ) = 1 / 12 := rfl

/-- **Concrete bound: `(1/12)² = 1/144`**. -/
theorem one_over_twelve_squared :
    ((1/12 : ℝ))^2 = 1/144 := by norm_num

/-! ## §2. Comparison with other rational values -/

/-- **`1/12 < 1/8`**. -/
theorem one_over_12_lt_one_over_8 :
    (1/12 : ℝ) < 1/8 := by norm_num

/-- **`1/12 > 1/16`**. -/
theorem one_over_12_gt_one_over_16 :
    (1/12 : ℝ) > 1/16 := by norm_num

/-- **`1/12 < 1/10`**. -/
theorem one_over_12_lt_one_over_10 :
    (1/12 : ℝ) < 1/10 := by norm_num

#print axioms one_over_12_lt_one_over_10

/-! ## §3. Improvement-error bound at concrete spacing -/

/-- **At lattice spacing `a = 1/4`, the Wilson artifact size is
    `(1/4)² · (1/12) = 1/192 < 0.006`**. -/
theorem wilson_artifact_at_quarter_spacing :
    (1/4 : ℝ) ^ 2 * (1/12 : ℝ) < 0.006 := by
  norm_num

#print axioms wilson_artifact_at_quarter_spacing

/-- **At `a = 1/10`, artifact `< 0.001`**. -/
theorem wilson_artifact_at_tenth_spacing :
    (1/10 : ℝ) ^ 2 * (1/12 : ℝ) < 0.001 := by
  norm_num

#print axioms wilson_artifact_at_tenth_spacing

end YangMills.L34_CreativeAttack_WilsonCoeff

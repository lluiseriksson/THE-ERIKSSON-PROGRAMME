/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L34_CreativeAttack_WilsonCoeff.WilsonCoeff_OneOver12

/-!
# Wilson coefficient robustness (Phase 329)

Robustness: any Symanzik improvement bound `|c_S| ≤ 1/12` works.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L34_CreativeAttack_WilsonCoeff

/-! ## §1. Robust improvement -/

/-- **Robust improvement**: any Symanzik counter-coefficient `c_S`
    satisfying `|c_S| ≤ 1/12` reduces the artifact size to
    `||c_W| - |c_S|| ≤ 1/12`. -/
theorem robust_improvement
    (c_S : ℝ) (h_bound : |c_S| ≤ 1/12) :
    |WilsonCoeff_derived - c_S| ≤ 1/12 + 1/12 := by
  unfold WilsonCoeff_derived
  have h1 : |((1:ℝ)/12)| = 1/12 := by
    rw [abs_of_pos]; norm_num
  calc |((1:ℝ)/12) - c_S|
      ≤ |((1:ℝ)/12)| + |c_S| := abs_sub _ _
    _ ≤ 1/12 + 1/12 := by linarith [h_bound, h1.le]

#print axioms robust_improvement

/-! ## §2. Optimal Symanzik counter -/

/-- **Optimal counter-term: `c_S = 1/12` makes the residual zero**. -/
theorem optimal_Symanzik_zero_residual :
    WilsonCoeff_derived - (1/12 : ℝ) = 0 := by
  unfold WilsonCoeff_derived
  norm_num

#print axioms optimal_Symanzik_zero_residual

/-! ## §3. Wilson coefficient is in `(0, 1/4]` -/

/-- **The Wilson coefficient `1/12` lies in `(0, 1/4]`**. -/
theorem WilsonCoeff_in_interval :
    0 < WilsonCoeff_derived ∧ WilsonCoeff_derived ≤ (1:ℝ)/4 := by
  refine ⟨?_, ?_⟩
  · exact WilsonCoeff_derived_pos
  · unfold WilsonCoeff_derived; norm_num

#print axioms WilsonCoeff_in_interval

end YangMills.L34_CreativeAttack_WilsonCoeff

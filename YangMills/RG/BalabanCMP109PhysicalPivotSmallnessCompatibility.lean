/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109PhysicalPivotBackgroundContraction
import YangMills.RG.BalabanCMP99SourceUbarRadiusBudget

/-!
# Non-vacuity of the physical CMP109 pivot smallness regime

The physical pivot contraction has two scalar small-background conditions:

* the printed logarithmic-chart radius is at most `1/3`;
* the generated pivot-defect budget is strictly below one.

The apparent `M²` and `L^(d-1)` costs are not separate consumer hypotheses:
they occur inside the second budget.  This file proves that every nested
background-Lipschitz budget is exactly linear in `epsilon0`, then constructs
one strictly positive `epsilon0` satisfying both physical conditions
simultaneously.

The witness depends on the actual norm of the ambient Lie-coordinate
retraction.  It therefore proves genuine non-vacuity without replacing that
norm by an arbitrary rational target.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

/-- The complete physical pivot background budget is exactly linear in the
small-background radius. -/
theorem cmp109PhysicalPivotBackgroundBudget_eq_at_one_mul
    (d L Nc : ℕ) [NeZero Nc] (epsilon0 : ℝ) :
    cmp109PhysicalPivotBackgroundBudget d L Nc epsilon0 =
      cmp109PhysicalPivotBackgroundBudget d L Nc 1 * epsilon0 := by
  unfold cmp109PhysicalPivotBackgroundBudget
    cmp102PhysicalRightVariationBackgroundBudget
    cmp102PhysicalBlockDerivativeBackgroundBudget
    cmp102PhysicalRightInverseBackgroundBudget
    cmp102PhysicalExpAverageBackgroundValueBudget
    cmp102PhysicalExpAverageBackgroundDerivativeBudget
    cmp102PhysicalLogAverageBackgroundValueBudget
    cmp102PhysicalLogAverageBackgroundDerivativeBudget
  dsimp only
  ring

/-- A positive source radius chosen from the two literal physical
coefficients.  The conservative factor six leaves strict margin for the
pivot contraction and a factor-two margin for the one-third chart radius. -/
noncomputable def cmp109PhysicalPivotSmallnessWitness
    (d L Nc : ℕ) [NeZero Nc] : ℝ :=
  let radiusCoefficient := cmp99SourceUbarDeviationCoefficient d L
  let pivotCoefficient :=
    cmp109PhysicalPivotBackgroundBudget d L Nc 1
  (6 * (1 + radiusCoefficient) * (1 + pivotCoefficient))⁻¹

theorem cmp109PhysicalPivotSmallnessWitness_pos
    (d L Nc : ℕ) [NeZero Nc] :
    0 < cmp109PhysicalPivotSmallnessWitness d L Nc := by
  have hradius :
      0 ≤ cmp99SourceUbarDeviationCoefficient d L :=
    cmp99SourceUbarDeviationCoefficient_nonneg d L
  have hpivot :
      0 ≤ cmp109PhysicalPivotBackgroundBudget d L Nc 1 :=
    cmp109PhysicalPivotBackgroundBudget_nonneg (by norm_num)
  unfold cmp109PhysicalPivotSmallnessWitness
  positivity

/-- The explicit witness lies inside the printed one-third logarithmic
chart. -/
theorem cmp109PhysicalPivotSmallnessWitness_radius
    (d L Nc : ℕ) [NeZero Nc] :
    cmp99SourceUbarFineDeviationRadius d L
        (cmp109PhysicalPivotSmallnessWitness d L Nc) ≤ 1 / 3 := by
  let R := cmp99SourceUbarDeviationCoefficient d L
  let C := cmp109PhysicalPivotBackgroundBudget d L Nc 1
  have hR : 0 ≤ R := cmp99SourceUbarDeviationCoefficient_nonneg d L
  have hC : 0 ≤ C :=
    cmp109PhysicalPivotBackgroundBudget_nonneg (by norm_num)
  have hden : 0 < 6 * (1 + R) * (1 + C) := by positivity
  rw [cmp99SourceUbarFineDeviationRadius_eq_coefficient_mul]
  simp only [cmp109PhysicalPivotSmallnessWitness]
  change R / (6 * (1 + R) * (1 + C)) ≤ 1 / 3
  rw [div_le_iff₀ hden]
  nlinarith [mul_nonneg hR hC]

/-- The same explicit witness makes the literal physical pivot defect a
strict contraction. -/
theorem cmp109PhysicalPivotSmallnessWitness_budget
    (d L Nc : ℕ) [NeZero Nc] :
    cmp109PhysicalPivotBackgroundBudget d L Nc
        (cmp109PhysicalPivotSmallnessWitness d L Nc) < 1 := by
  let R := cmp99SourceUbarDeviationCoefficient d L
  let C := cmp109PhysicalPivotBackgroundBudget d L Nc 1
  have hR : 0 ≤ R := cmp99SourceUbarDeviationCoefficient_nonneg d L
  have hC : 0 ≤ C :=
    cmp109PhysicalPivotBackgroundBudget_nonneg (by norm_num)
  have hden : 0 < 6 * (1 + R) * (1 + C) := by positivity
  rw [cmp109PhysicalPivotBackgroundBudget_eq_at_one_mul]
  simp only [cmp109PhysicalPivotSmallnessWitness]
  change C / (6 * (1 + R) * (1 + C)) < 1
  rw [div_lt_one hden]
  nlinarith [mul_nonneg hR hC]

/-- Bundled physical scalar regime consumed by the CMP109 pivot
contraction.  Adding another scalar condition to that contraction should be
reflected as another mandatory field here. -/
structure CMP109PhysicalPivotSmallnessRegime
    (d L Nc : ℕ) [NeZero Nc] where
  epsilon0 : ℝ
  epsilon0_pos : 0 < epsilon0
  background_radius :
    cmp99SourceUbarFineDeviationRadius d L epsilon0 ≤ 1 / 3
  pivot_budget :
    cmp109PhysicalPivotBackgroundBudget d L Nc epsilon0 < 1

/-- The physical pivot smallness regime is inhabited for every fixed
dimension, block scale, and nonzero colour count. -/
noncomputable def cmp109PhysicalPivotSmallnessRegimeWitness
    (d L Nc : ℕ) [NeZero Nc] :
    CMP109PhysicalPivotSmallnessRegime d L Nc where
  epsilon0 := cmp109PhysicalPivotSmallnessWitness d L Nc
  epsilon0_pos := cmp109PhysicalPivotSmallnessWitness_pos d L Nc
  background_radius :=
    cmp109PhysicalPivotSmallnessWitness_radius d L Nc
  pivot_budget :=
    cmp109PhysicalPivotSmallnessWitness_budget d L Nc

end

end YangMills.RG

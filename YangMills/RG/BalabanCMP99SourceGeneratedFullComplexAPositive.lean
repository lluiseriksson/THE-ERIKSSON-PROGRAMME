/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreen

/-!
# Positivity of the generated full-complex coefficient

The literal Step-7b coefficient is the product of the generated physical mass
and one normalized block-average weight.  At successor depth both factors are
strictly positive for the canonical generated spacing.  This module produces
that fact internally; it does not accept positivity of the coefficient as an
input and does not assert any fine-symbol or stabilized-denominator
nonvanishing.
-/

namespace YangMills.RG

noncomputable section

/-- The normalized block-average weight is strictly positive for a nonzero
block side. -/
theorem cmp99SourceBlockAverageWeight_pos
    (M d : ℕ) [NeZero M] :
    0 < cmp99SourceBlockAverageWeight M d := by
  unfold cmp99SourceBlockAverageWeight
  exact inv_pos.mpr (pow_pos (Nat.cast_pos.mpr (NeZero.pos M)) d)

/-- At successor depth the generated physical mass is strictly positive as
soon as the physical spacing is positive. -/
theorem cmp99SourceGeneratedPhysicalMass_pos_succ
    (d M depth : ℕ) [NeZero d] [NeZero M]
    {spacing epsilon : ℝ} (hspacing : 0 < spacing) :
    0 < cmp99SourceGeneratedPhysicalMass
      d M (depth + 1) spacing epsilon := by
  unfold cmp99SourceGeneratedPhysicalMass
  exact div_pos
    (pow_pos cmp99OneScaleBlockPoincareConstant_pos (depth + 1))
    (cmp99SourcePoincareEnergyCoeff_pos_succ
      d M depth hspacing)

/-- The literal generated full-complex coefficient is positive at successor
depth for every positive spacing. -/
theorem cmp99SourceGeneratedFullComplexA_pos_succ
    (d M depth : ℕ) [NeZero d] [NeZero M]
    {spacing epsilon : ℝ} (hspacing : 0 < spacing) :
    0 < cmp99SourceGeneratedFullComplexA
      d M (depth + 1) spacing epsilon := by
  unfold cmp99SourceGeneratedFullComplexA
  exact mul_pos
    (cmp99SourceGeneratedPhysicalMass_pos_succ
      d M depth hspacing)
    (cmp99SourceBlockAverageWeight_pos (M ^ (depth + 1)) d)

/-- Physical specialization used by the generated Step-7b precision: four
dimensions, canonical spacing, and zero source radius. -/
theorem cmp99SourceGeneratedFullComplexA_pos_physical
    (M depth : ℕ) [NeZero M] :
    0 < cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0 := by
  exact cmp99SourceGeneratedFullComplexA_pos_succ 4 M depth
    (cmp99SourceGeneratedFullComplexSpacing_pos M (depth + 1))

end

end YangMills.RG

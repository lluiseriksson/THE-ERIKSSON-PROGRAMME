/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedRegionalFineSlope

/-!
# Scale no-go for the two-terminal-block regional cutoff

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

The generated regional cutoff currently has side
`2 * M^(depth+1)`, whereas the proved range of its generated precision is
`M^(depth+1)`.  Hence its inverse cutoff scale cannot produce the `O(M^-1)`
gain of CMP99 (3.89): multiplication by the certified range cancels it to a
constant.  This records the obstruction instead of silently treating the
two-terminal-block partition as the source large-block partition.
-/

namespace YangMills.RG

noncomputable section

/-- The current cutoff side is exactly twice the terminal precision range. -/
theorem cmp99SourceGeneratedCellCutoffScale_eq_two_mul_precisionRange
    (M depth : ℕ) :
    cmp99SourceGeneratedCellCutoffScale M depth =
      2 * (M ^ (depth + 1) : ℝ) := by
  unfold cmp99SourceGeneratedCellCutoffScale
  norm_num

/-- Consequently, the range/cutoff ratio is the fixed number `1/2`, not a
parameter tending to zero with the source large-block scale. -/
theorem cmp99SourceGenerated_precisionRange_div_cellCutoffScale
    (M depth : ℕ) [NeZero M] :
    (M ^ (depth + 1) : ℝ) /
        cmp99SourceGeneratedCellCutoffScale M depth = 1 / 2 := by
  rw [cmp99SourceGeneratedCellCutoffScale_eq_two_mul_precisionRange]
  have hpow : (M ^ (depth + 1) : ℝ) ≠ 0 := by positivity
  field_simp

/-- The literal slope coefficient from the generated regional cutoff loses
its displayed inverse scale after one precision-range displacement. -/
theorem cmp99SourceGenerated_cellSlope_mul_precisionRange
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) [NeZero M] :
    ((8 * P.derivBound) /
        cmp99SourceGeneratedCellCutoffScale M depth) *
      (M ^ (depth + 1) : ℝ) = 4 * P.derivBound := by
  rw [cmp99SourceGeneratedCellCutoffScale_eq_two_mul_precisionRange]
  have hpow : (M ^ (depth + 1) : ℝ) ≠ 0 := by positivity
  field_simp <;> ring

end

end YangMills.RG

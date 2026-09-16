/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalTwoFieldBlock

/-!
# Two-field control after right normalization and the final CMP98 logarithm

At the background parameter `t = 0`, the literal contour and logarithmic
average are independent of the supplied tangent field.  Hence the exact
right-normalizing inverse is common to both fields.  This module proves that
fact and propagates the represented-block estimate through right
normalization and the final Mercator logarithm.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102TwoFieldRelativeLogMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The exact background inverse is independent of the tangent field. -/
theorem cmp98Eq119NonlinearBlockInverseAtZero_twoField_eq
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq119NonlinearBlockInverseAtZero U A b =
      cmp98Eq119NonlinearBlockInverseAtZero U B b := by
  unfold cmp98Eq119NonlinearBlockInverseAtZero
  rw [cmp98ContourMatrixCurve_zero_eq_wilsonLine,
    cmp98ContourMatrixCurve_zero_eq_wilsonLine]

/-- Explicit two-field budget after multiplication by the common
right-normalizing inverse. -/
def cmp102SourceRelativeDeviationTwoFieldBudget
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (t r : ℝ) : ℝ :=
  cmp102SourceNonlinearBlockTwoFieldBudget A B t r *
    cmp98SourceOuterExpNormBudget r

/-- The normalized nonlinear deviations inherit the block estimate through
the exact common background inverse. -/
theorem norm_cmp98Eq119NonlinearRelativeDeviation_twoField_sub_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hA : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hB : |t| * cmp98SourceFieldSupNorm B ≤ 1 / 2)
    (hrA : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hrB : 1 / 3 + cmp98SourceContourDisplacementBudget B t ≤ r)
    (hr1 : r < 1) :
    ‖cmp98Eq119NonlinearRelativeDeviation U A b t -
        cmp98Eq119NonlinearRelativeDeviation U B b t‖ ≤
      cmp102SourceRelativeDeviationTwoFieldBudget A B t r := by
  let BA := cmp98Eq119NonlinearBlockCurve U A b t
  let BB := cmp98Eq119NonlinearBlockCurve U B b t
  let I := cmp98Eq119NonlinearBlockInverseAtZero U A b
  have hI :
      cmp98Eq119NonlinearBlockInverseAtZero U B b = I := by
    exact (cmp98Eq119NonlinearBlockInverseAtZero_twoField_eq
      U A B b).symm
  have hblock : ‖BA - BB‖ ≤
      cmp102SourceNonlinearBlockTwoFieldBudget A B t r := by
    simpa [BA, BB] using
      norm_cmp98Eq119NonlinearBlockCurve_twoField_sub_le
        U A B b t r hbase hA hB hrA hrB hr1
  have hr13 : (1 / 3 : ℝ) ≤ r := by
    linarith [cmp98SourceContourDisplacementBudget_nonneg A t]
  have hnormI : ‖I‖ ≤ cmp98SourceOuterExpNormBudget r := by
    simpa [I] using
      norm_cmp98Eq119NonlinearBlockInverseAtZero_le_sourceBudget
        U A b r hbase hr13 hr1
  have halg :
      (BA * I - 1) - (BB * I - 1) = (BA - BB) * I := by
    noncomm_ring
  unfold cmp98Eq119NonlinearRelativeDeviation
  rw [hI]
  change ‖(BA * I - 1) - (BB * I - 1)‖ ≤ _
  rw [halg]
  exact (norm_mul_le _ _).trans
    (mul_le_mul hblock hnormI (norm_nonneg _)
      ((norm_nonneg _).trans hblock))

/-- The final nonlinear logarithmic coordinates are two-field Lipschitz on
a common source-generated relative-deviation ball. -/
theorem norm_cmp98Eq119NonlinearLogCoordinate_twoField_sub_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r s : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hA : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hB : |t| * cmp98SourceFieldSupNorm B ≤ 1 / 2)
    (hrA : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hrB : 1 / 3 + cmp98SourceContourDisplacementBudget B t ≤ r)
    (hr1 : r < 1)
    (hsA : cmp98SourcePhysicalBlockDisplacementBudget A t r ≤ s)
    (hsB : cmp98SourcePhysicalBlockDisplacementBudget B t r ≤ s)
    (hs1 : s < 1) :
    ‖cmp98Eq119NonlinearLogCoordinate U A b t -
        cmp98Eq119NonlinearLogCoordinate U B b t‖ ≤
      nearLogDerivativeBudget s *
        cmp102SourceRelativeDeviationTwoFieldBudget A B t r := by
  let ZA := cmp98Eq119NonlinearRelativeDeviation U A b t
  let ZB := cmp98Eq119NonlinearRelativeDeviation U B b t
  have hZA : ‖ZA‖ ≤ s := by
    exact (norm_cmp98Eq119NonlinearRelativeDeviation_le_sourceBudget
      U A b t r hbase hA hrA hr1).trans hsA
  have hZB : ‖ZB‖ ≤ s := by
    exact (norm_cmp98Eq119NonlinearRelativeDeviation_le_sourceBudget
      U B b t r hbase hB hrB hr1).trans hsB
  have hdiff : ‖ZA - ZB‖ ≤
      cmp102SourceRelativeDeviationTwoFieldBudget A B t r := by
    simpa [ZA, ZB] using
      norm_cmp98Eq119NonlinearRelativeDeviation_twoField_sub_le
        U A B b t r hbase hA hB hrA hrB hr1
  have hs0 : 0 ≤ s := (norm_nonneg ZA).trans hZA
  unfold cmp98Eq119NonlinearLogCoordinate
  exact (norm_nearLog_sub_nearLog_le hs0 hs1 hZA hZB).trans
    (mul_le_mul_of_nonneg_left hdiff
      (nearLogDerivativeBudget_nonneg s hs0))

end

end YangMills.RG

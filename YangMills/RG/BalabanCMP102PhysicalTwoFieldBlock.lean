/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalTwoFieldUbar

/-!
# Two-field control of the physical CMP98 nonlinear block

The literal two-field estimate is propagated through the outer
noncommutative exponential and the straight coarse contour.  Both
contributions are retained separately in the explicit budget.  No
Lipschitz constant for the represented block is supplied by the caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102TwoFieldBlockMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Two-field budget for the outer exponential of the logarithmic average. -/
def cmp102SourceUbarExpTwoFieldBudget
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (t r : ℝ) : ℝ :=
  cmp102ExpLipschitzBudget (cmp98SourceLogAverageRadius r) *
    (nearLogDerivativeBudget r *
      cmp102SourceFourContourTwoFieldBudget A B t)

/-- Two-field budget for the literal straight coarse contour. -/
def cmp102SourceCoarseContourTwoFieldBudget
    (A B : PhysicalGaugeOneCochain d (M * N') Nc) (t : ℝ) : ℝ :=
  (M : ℝ) * (cmp102ExpLipschitzBudget (1 / 2) *
    (|t| * cmp98SourceFieldSupNorm (A - B)))

/-- Complete two-field budget for the represented nonlinear block. -/
def cmp102SourceNonlinearBlockTwoFieldBudget
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (t r : ℝ) : ℝ :=
  cmp102SourceUbarExpTwoFieldBudget A B t r +
    cmp98SourceOuterExpNormBudget r *
      cmp102SourceCoarseContourTwoFieldBudget A B t

theorem cmp102SourceUbarExpTwoFieldBudget_nonneg
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (t r : ℝ) (hr : 0 ≤ r) :
    0 ≤ cmp102SourceUbarExpTwoFieldBudget A B t r := by
  unfold cmp102SourceUbarExpTwoFieldBudget
  exact mul_nonneg
    (cmp102ExpLipschitzBudget_nonneg _
      (cmp98SourceLogAverageRadius_nonneg r hr))
    (mul_nonneg (nearLogDerivativeBudget_nonneg r hr)
      (cmp102SourceFourContourTwoFieldBudget_nonneg A B t))

theorem cmp102SourceCoarseContourTwoFieldBudget_nonneg
    (A B : PhysicalGaugeOneCochain d (M * N') Nc) (t : ℝ) :
    0 ≤ cmp102SourceCoarseContourTwoFieldBudget A B t := by
  unfold cmp102SourceCoarseContourTwoFieldBudget
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg
      (cmp102ExpLipschitzBudget_nonneg (1 / 2) (by norm_num))
      (mul_nonneg (abs_nonneg t)
        (cmp98SourceFieldSupNorm_nonneg (A - B))))

/-- The outer exponentials at two physical fields are Lipschitz with an
explicit source-generated constant. -/
theorem norm_cmp98UbarExpAverage_twoField_sub_le
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
    ‖cmp98UbarExpAverage U b
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) -
        cmp98UbarExpAverage U b
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent B))‖ ≤
      cmp102SourceUbarExpTwoFieldBudget A B t r := by
  let R := cmp98SourceLogAverageRadius r
  let YA := cmp98UbarLogAverage U b
    (t • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A))
  let YB := cmp98UbarLogAverage U b
    (t • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent B))
  have hr13 : (1 / 3 : ℝ) ≤ r := by
    linarith [cmp98SourceContourDisplacementBudget_nonneg A t]
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13
  have hR0 : 0 ≤ R := cmp98SourceLogAverageRadius_nonneg r hr0
  have hYA : ‖YA‖ ≤ R := by
    simpa [YA, R] using
      norm_cmp98UbarLogAverage_physicalLine_le_sourceRadius
        U A b t r hbase hA hrA hr1
  have hYB : ‖YB‖ ≤ R := by
    simpa [YB, R] using
      norm_cmp98UbarLogAverage_physicalLine_le_sourceRadius
        U B b t r hbase hB hrB hr1
  have hdiff : ‖YA - YB‖ ≤
      nearLogDerivativeBudget r *
        cmp102SourceFourContourTwoFieldBudget A B t := by
    simpa [YA, YB] using
      norm_cmp98UbarLogAverage_twoField_sub_le
        U A B b t r hbase hA hB hrA hrB hr1
  have hexp :=
    norm_exp_sub_exp_le_cmp102ExpLipschitzBudget hR0 hYA hYB
  unfold cmp98UbarExpAverage
  exact hexp.trans (mul_le_mul_of_nonneg_left hdiff
    (cmp102ExpLipschitzBudget_nonneg R hR0))

/-- A physical outer exponential on the same source ball has the existing
source-explicit norm budget. -/
theorem norm_cmp98UbarExpAverage_physicalLine_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hA : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hrA : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hr1 : r < 1) :
    ‖cmp98UbarExpAverage U b
      (t • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A))‖ ≤
      cmp98SourceOuterExpNormBudget r := by
  let R := cmp98SourceLogAverageRadius r
  let Y := cmp98UbarLogAverage U b
    (t • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A))
  have hr13 : (1 / 3 : ℝ) ≤ r := by
    linarith [cmp98SourceContourDisplacementBudget_nonneg A t]
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13
  have hR0 : 0 ≤ R := cmp98SourceLogAverageRadius_nonneg r hr0
  have hY : ‖Y‖ ≤ R := by
    simpa [Y, R] using
      norm_cmp98UbarLogAverage_physicalLine_le_sourceRadius
        U A b t r hbase hA hrA hr1
  have hraw := norm_exp_le_derivativeBudgets hR0 hY
  simpa [cmp98UbarExpAverage, cmp98SourceOuterExpNormBudget, R, Y] using hraw

/-- The straight coarse contour is two-field Lipschitz with its exact
length `M`. -/
theorem norm_cmp98SourceCoarseContour_twoField_sub_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hA : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hB : |t| * cmp98SourceFieldSupNorm B ≤ 1 / 2) :
    ‖cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) t -
        cmp98ContourMatrixCurve U B
          (cmp98SourceCoarseBondPath (Nc := Nc) b) t‖ ≤
      cmp102SourceCoarseContourTwoFieldBudget A B t := by
  have hraw := norm_cmp98ContourMatrixCurve_sub_le U A B
    (cmp98SourceCoarseBondPath (Nc := Nc) b) t (1 / 2)
    (by norm_num) hA hB
  simpa [cmp102SourceCoarseContourTwoFieldBudget,
    cmp98SourceCoarseBondPath_length (Nc := Nc)] using hraw

/-- The complete literal nonlinear represented block is two-field Lipschitz
with no supplied block-level constant. -/
theorem norm_cmp98Eq119NonlinearBlockCurve_twoField_sub_le
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
    ‖cmp98Eq119NonlinearBlockCurve U A b t -
        cmp98Eq119NonlinearBlockCurve U B b t‖ ≤
      cmp102SourceNonlinearBlockTwoFieldBudget A B t r := by
  let EA := cmp98UbarExpAverage U b
    (t • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A))
  let EB := cmp98UbarExpAverage U b
    (t • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent B))
  let CA := cmp98ContourMatrixCurve U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) t
  let CB := cmp98ContourMatrixCurve U B
    (cmp98SourceCoarseBondPath (Nc := Nc) b) t
  have hEA : ‖EA - EB‖ ≤
      cmp102SourceUbarExpTwoFieldBudget A B t r := by
    simpa [EA, EB] using
      norm_cmp98UbarExpAverage_twoField_sub_le
        U A B b t r hbase hA hB hrA hrB hr1
  have hEB : ‖EB‖ ≤ cmp98SourceOuterExpNormBudget r := by
    simpa [EB] using
      norm_cmp98UbarExpAverage_physicalLine_le_sourceBudget
        U B b t r hbase hB hrB hr1
  have hCA : ‖CA‖ = 1 :=
    norm_cmp98ContourMatrixCurve_eq_one U A _ t
  have hC : ‖CA - CB‖ ≤
      cmp102SourceCoarseContourTwoFieldBudget A B t := by
    simpa [CA, CB] using
      norm_cmp98SourceCoarseContour_twoField_sub_le U A B b t hA hB
  unfold cmp98Eq119NonlinearBlockCurve
  change ‖EA * CA - EB * CB‖ ≤ _
  rw [twoFactor_sub_zero_eq]
  unfold cmp102SourceNonlinearBlockTwoFieldBudget
  calc
    ‖(EA - EB) * CA + EB * (CA - CB)‖
        ≤ ‖(EA - EB) * CA‖ + ‖EB * (CA - CB)‖ :=
      norm_add_le _ _
    _ ≤ ‖EA - EB‖ * ‖CA‖ + ‖EB‖ * ‖CA - CB‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ cmp102SourceUbarExpTwoFieldBudget A B t r * 1 +
          cmp98SourceOuterExpNormBudget r *
            cmp102SourceCoarseContourTwoFieldBudget A B t := by
      exact add_le_add
        (mul_le_mul hEA hCA.le (norm_nonneg _)
          ((norm_nonneg _).trans hEA))
        (mul_le_mul hEB hC (norm_nonneg _)
          ((norm_nonneg _).trans hEB))
    _ = _ := by ring

end

end YangMills.RG

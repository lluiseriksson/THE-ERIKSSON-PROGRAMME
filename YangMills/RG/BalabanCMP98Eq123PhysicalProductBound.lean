/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98OuterExponentialBounds
import YangMills.RG.BalabanCMP98TwoFactorQuadratic

/-!
# The literal physical two-factor remainder in CMP98 (123)

This source-shaped theorem composes the independently verified outer
exponential and straight coarse-contour estimates through the exact
two-factor identity.  Its right-hand side is displayed with local `let`
bindings matching the existing source budgets exactly; no conversion through
an abstract remainder certificate is needed.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq123PhysicalProductBoundMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The quadratic remainder of the exact represented block before right
normalization.  Keeping this source object named lets downstream estimates
compose without repeatedly unfolding the large physical formula. -/
def cmp98Eq123PhysicalTwoFactorProductRemainder
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98UbarExpAverage U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) *
        cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) t -
    cmp98UbarExpAverage U b 0 *
        cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 -
    t • (fderiv ℝ
          (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
            Matrix (Fin Nc) (Fin Nc) ℂ)
          (cmp98UbarLogAverage U b 0)
          (cmp98UbarLogAveragePhysicalVariation U A b) *
          cmp98ContourMatrixCurve U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 +
        cmp98UbarExpAverage U b 0 *
          cmp98ContourFirstVariation U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)

set_option maxHeartbeats 1000000 in
/-- Source-explicit quadratic remainder for the literal represented product
`exp(Y(t)) * C(t)`, before right normalization. -/
theorem norm_cmp98Eq123PhysicalTwoFactorProduct_sub_zero_sub_first_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hr : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hr1 : r < 1) :
    let R := cmp98SourceLogAverageRadius r
    let D := nearLogDerivativeBudget r *
      cmp98SourceContourDisplacementBudget A t
    let Q := nearLogSecondDerivativeBudget r *
          cmp98SourceContourDisplacementBudget A t ^ 2 +
        nearLogDerivativeBudget r *
          cmp98SourceContourQuadraticBudget A t
    let QE := expSecondDerivativeBudget R * D ^ 2 +
      expDerivativeBudget R * Q
    ‖cmp98UbarExpAverage U b
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) *
          cmp98ContourMatrixCurve U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) t -
        cmp98UbarExpAverage U b 0 *
          cmp98ContourMatrixCurve U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 -
        t • (fderiv ℝ
            (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
              Matrix (Fin Nc) (Fin Nc) ℂ)
            (cmp98UbarLogAverage U b 0)
            (cmp98UbarLogAveragePhysicalVariation U A b) *
            cmp98ContourMatrixCurve U A
              (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 +
          cmp98UbarExpAverage U b 0 *
            cmp98ContourFirstVariation U A
              (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)‖ ≤
      QE + cmp98SourceOuterExpNormBudget r *
          cmp98SourceCoarseContourQuadraticBudget A t +
        cmp98SourceOuterExpDisplacementBudget A t r *
          cmp98SourceCoarseContourDisplacementBudget A t := by
  dsimp only
  have hr13 : (1 / 3 : ℝ) ≤ r := by
    linarith [cmp98SourceContourDisplacementBudget_nonneg A t]
  apply norm_twoFactor_sub_zero_sub_first_le
  · exact norm_cmp98UbarExpAverage_physicalLine_sub_zero_sub_linear_le
      U A b t r hbase hsmall hr hr1
  · exact norm_cmp98UbarExpAverage_zero_le_sourceBudget
      U b r hbase hr13 hr1
  · exact norm_cmp98SourceCoarseContour_sub_zero_sub_linear_le
      U A b t hsmall
  · exact norm_cmp98UbarExpAverage_physicalLine_sub_zero_le_sourceBudget
      U A b t r hbase hsmall hr hr1
  · exact norm_cmp98SourceCoarseContour_sub_zero_le U A b t hsmall
  · rw [cmp98ContourMatrixCurve_zero_eq_wilsonLine]
    exact norm_SUN_coe_l2_opNorm _

set_option maxHeartbeats 1000000 in
/-- Compact source-facing form of the preceding literal estimate. -/
theorem norm_cmp98Eq123PhysicalTwoFactorProductRemainder_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hr : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hr1 : r < 1) :
    let R := cmp98SourceLogAverageRadius r
    let D := nearLogDerivativeBudget r *
      cmp98SourceContourDisplacementBudget A t
    let Q := nearLogSecondDerivativeBudget r *
          cmp98SourceContourDisplacementBudget A t ^ 2 +
        nearLogDerivativeBudget r *
          cmp98SourceContourQuadraticBudget A t
    let QE := expSecondDerivativeBudget R * D ^ 2 +
      expDerivativeBudget R * Q
    ‖cmp98Eq123PhysicalTwoFactorProductRemainder U A b t‖ ≤
      QE + cmp98SourceOuterExpNormBudget r *
          cmp98SourceCoarseContourQuadraticBudget A t +
        cmp98SourceOuterExpDisplacementBudget A t r *
          cmp98SourceCoarseContourDisplacementBudget A t := by
  dsimp only
  unfold cmp98Eq123PhysicalTwoFactorProductRemainder
  exact norm_cmp98Eq123PhysicalTwoFactorProduct_sub_zero_sub_first_le
    U A b t r hbase hsmall hr hr1

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq123PhysicalProductBound
import YangMills.RG.BalabanCMP98Eq123QuadraticFrontier

/-!
# The source-explicit physical block remainder in CMP98 (123)

This file performs the exact right normalization omitted from the preceding
two-factor estimate.  The normalized remainder is the unnormalized product
remainder multiplied by the literal background inverse.  Both factors of
that inverse are then bounded from their physical definitions.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq123PhysicalBlockBoundMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

omit [NeZero Nc] in
/-- Pure algebra behind right normalization of a quadratic remainder. -/
theorem twoFactorRemainder_mul_rightInverse
    (Bt B0 Bp I : Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ)
    (hI : B0 * I = 1) :
    (Bt * I - 1) - t • (Bp * I) =
      (Bt - B0 - t • Bp) * I := by
  rw [← hI]
  rw [sub_mul, sub_mul, smul_mul_assoc]

/-- The literal right-normalizing inverse has an explicit source budget. -/
theorem norm_cmp98Eq119NonlinearBlockInverseAtZero_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hr13 : 1 / 3 ≤ r) (hr1 : r < 1) :
    ‖cmp98Eq119NonlinearBlockInverseAtZero U A b‖ ≤
      cmp98SourceOuterExpNormBudget r := by
  let R := cmp98SourceLogAverageRadius r
  let Y0 := cmp98UbarLogAverage U b 0
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13
  have hR0 : 0 ≤ R := cmp98SourceLogAverageRadius_nonneg r hr0
  have hY0base : ‖Y0‖ ≤ nearLogDerivativeBudget r * (1 / 3 : ℝ) := by
    simpa [Y0] using norm_cmp98UbarLogAverage_zero_le U b r hbase hr13 hr1
  have hY0 : ‖-Y0‖ ≤ R := by
    rw [norm_neg]
    have hB1 := nearLogDerivativeBudget_nonneg r hr0
    exact hY0base.trans (by
      dsimp only [R, cmp98SourceLogAverageRadius]
      exact mul_le_mul_of_nonneg_left hr13 hB1)
  have hexp : ‖NormedSpace.exp (-Y0)‖ ≤
      cmp98SourceOuterExpNormBudget r := by
    have hraw := norm_exp_le_derivativeBudgets hR0 hY0
    simpa [cmp98SourceOuterExpNormBudget, R] using hraw
  unfold cmp98Eq119NonlinearBlockInverseAtZero
  calc
    ‖Matrix.conjTranspose
          (cmp98ContourMatrixCurve U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) 0) *
        NormedSpace.exp (-Y0)‖
        ≤ ‖Matrix.conjTranspose
            (cmp98ContourMatrixCurve U A
              (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)‖ *
            ‖NormedSpace.exp (-Y0)‖ := norm_mul_le _ _
    _ = ‖NormedSpace.exp (-Y0)‖ := by
      rw [Matrix.l2_opNorm_conjTranspose,
        cmp98ContourMatrixCurve_zero_eq_wilsonLine,
        norm_SUN_coe_l2_opNorm, one_mul]
    _ ≤ cmp98SourceOuterExpNormBudget r := hexp

set_option maxHeartbeats 1000000 in
/-- The physical normalized remainder is exactly the preceding literal
two-factor remainder times the background inverse. -/
theorem cmp98Eq123PhysicalBlockRemainder_eq_productRemainder_mul_inverse
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp98Eq123PhysicalBlockRemainder U A b t =
    cmp98Eq123PhysicalTwoFactorProductRemainder U A b t *
        cmp98Eq119NonlinearBlockInverseAtZero U A b := by
  have hI :
      (cmp98UbarExpAverage U b 0 *
          cmp98ContourMatrixCurve U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) 0) *
        cmp98Eq119NonlinearBlockInverseAtZero U A b = 1 := by
    unfold cmp98Eq119NonlinearBlockInverseAtZero cmp98UbarExpAverage
    rw [mul_assoc, ← mul_assoc
        (cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0),
      cmp98ContourMatrixCurve_zero_mul_conjTranspose_general U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b),
      one_mul, cmp98_exp_mul_exp_neg]
  unfold cmp98Eq123PhysicalBlockRemainder
    cmp98Eq119NonlinearRelativeDeviation
    cmp98Eq119NonlinearRightVariation
    cmp98Eq123PhysicalTwoFactorProductRemainder
  rw [(hasDerivAt_cmp98Eq119NonlinearBlockCurve U A b hsmall).deriv,
    cmp98Eq119_fourFactorFirst_eq]
  unfold cmp98Eq119NonlinearBlockCurve
  exact twoFactorRemainder_mul_rightInverse
    (cmp98UbarExpAverage U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) *
      cmp98ContourMatrixCurve U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) t)
    (cmp98UbarExpAverage U b 0 *
      cmp98ContourMatrixCurve U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)
    (fderiv ℝ
          (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
            Matrix (Fin Nc) (Fin Nc) ℂ)
          (cmp98UbarLogAverage U b 0)
          (cmp98UbarLogAveragePhysicalVariation U A b) *
        cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 +
      cmp98UbarExpAverage U b 0 *
        cmp98ContourFirstVariation U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)
    (cmp98Eq119NonlinearBlockInverseAtZero U A b) t hI

set_option maxHeartbeats 6000000 in
/-- Fully source-explicit norm bound for the physical represented-block
remainder in CMP98 (123), before the final local logarithm correction. -/
theorem norm_cmp98Eq123PhysicalBlockRemainder_le_sourceBudget
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
    ‖cmp98Eq123PhysicalBlockRemainder U A b t‖ ≤
      (QE + cmp98SourceOuterExpNormBudget r *
          cmp98SourceCoarseContourQuadraticBudget A t +
        cmp98SourceOuterExpDisplacementBudget A t r *
          cmp98SourceCoarseContourDisplacementBudget A t) *
        cmp98SourceOuterExpNormBudget r := by
  dsimp only
  have hr13 : (1 / 3 : ℝ) ≤ r := by
    linarith [cmp98SourceContourDisplacementBudget_nonneg A t]
  have hbase' : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
    intro x hx
    exact (hbase x hx).trans_lt (by norm_num)
  rw [cmp98Eq123PhysicalBlockRemainder_eq_productRemainder_mul_inverse
    U A b t hbase']
  have hproduct :=
    norm_cmp98Eq123PhysicalTwoFactorProductRemainder_le_sourceBudget
      U A b t r hbase hsmall hr hr1
  exact (norm_mul_le _ _).trans (mul_le_mul
    hproduct
    (norm_cmp98Eq119NonlinearBlockInverseAtZero_le_sourceBudget
      U A b r hbase hr13 hr1)
    (norm_nonneg _) ((norm_nonneg _).trans hproduct))

end

end YangMills.RG

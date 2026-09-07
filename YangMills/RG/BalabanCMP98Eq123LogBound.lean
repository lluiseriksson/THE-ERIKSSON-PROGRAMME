/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq123PhysicalBlockBound

/-!
# The complete quantitative CMP98 (123) remainder

The preceding modules bound the represented block before the local
logarithm.  Here we additionally bound its exact normalized displacement,
apply the sharp Mercator remainder, and combine both pieces through the
source-faithful decomposition of (123).
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq123LogBoundMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Source budget for the exact normalized represented-block displacement. -/
def cmp98SourcePhysicalBlockDisplacementBudget
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t r : ℝ) : ℝ :=
  (cmp98SourceOuterExpDisplacementBudget A t r +
      cmp98SourceOuterExpNormBudget r *
        cmp98SourceCoarseContourDisplacementBudget A t) *
    cmp98SourceOuterExpNormBudget r

/-- Literal unnormalized represented-block displacement. -/
def cmp98Eq123PhysicalProductDisplacement
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
        (cmp98SourceCoarseBondPath (Nc := Nc) b) 0

/-- The straight physical contour remains unitary at every interpolation
parameter and hence has L2 operator norm one. -/
theorem norm_cmp98ContourMatrixCurve_eq_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N')))
    (t : ℝ) :
    ‖cmp98ContourMatrixCurve U A es t‖ = 1 := by
  let C := cmp98ContourMatrixCurve U A es t
  have hunit : Matrix.conjTranspose C * C = 1 := by
    exact cmp98ContourMatrixCurve_conjTranspose_mul_general U A es t
  have hsq : ‖C‖ * ‖C‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hunit, norm_one]
  nlinarith [norm_nonneg C]

omit [NeZero Nc] in
/-- Exact first-order two-factor displacement identity. -/
theorem twoFactor_sub_zero_eq
    (Et E0 Ct C0 : Matrix (Fin Nc) (Fin Nc) ℂ) :
    Et * Ct - E0 * C0 =
      (Et - E0) * Ct + E0 * (Ct - C0) := by
  noncomm_ring

omit [NeZero Nc] in
/-- Right normalization of a first-order product displacement. -/
theorem twoFactorDisplacement_mul_rightInverse
    (Bt B0 I : Matrix (Fin Nc) (Fin Nc) ℂ) (hI : B0 * I = 1) :
    Bt * I - 1 = (Bt - B0) * I := by
  rw [sub_mul, hI]

set_option maxHeartbeats 1000000 in
/-- The literal unnormalized represented block has the expected product
displacement budget. -/
theorem norm_cmp98Eq123PhysicalProduct_sub_zero_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hr : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hr1 : r < 1) :
    ‖cmp98Eq123PhysicalProductDisplacement U A b t‖ ≤
      cmp98SourceOuterExpDisplacementBudget A t r +
        cmp98SourceOuterExpNormBudget r *
          cmp98SourceCoarseContourDisplacementBudget A t := by
  let Et := cmp98UbarExpAverage U b
    (t • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A))
  let E0 := cmp98UbarExpAverage U b 0
  let Ct := cmp98ContourMatrixCurve U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) t
  let C0 := cmp98ContourMatrixCurve U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  have hdecomp : Et * Ct - E0 * C0 =
      (Et - E0) * Ct + E0 * (Ct - C0) :=
    twoFactor_sub_zero_eq Et E0 Ct C0
  have hEt :=
    norm_cmp98UbarExpAverage_physicalLine_sub_zero_le_sourceBudget
      U A b t r hbase hsmall hr hr1
  have hE0 : ‖E0‖ ≤ cmp98SourceOuterExpNormBudget r := by
    have hr13 : (1 / 3 : ℝ) ≤ r := by
      linarith [cmp98SourceContourDisplacementBudget_nonneg A t]
    simpa [E0] using
      norm_cmp98UbarExpAverage_zero_le_sourceBudget U b r hbase hr13 hr1
  have hCt : ‖Ct‖ = 1 := by
    exact norm_cmp98ContourMatrixCurve_eq_one U A _ t
  have hC := norm_cmp98SourceCoarseContour_sub_zero_le U A b t hsmall
  unfold cmp98Eq123PhysicalProductDisplacement
  change ‖Et * Ct - E0 * C0‖ ≤ _
  rw [hdecomp]
  calc
    ‖(Et - E0) * Ct + E0 * (Ct - C0)‖
        ≤ ‖(Et - E0) * Ct‖ + ‖E0 * (Ct - C0)‖ := norm_add_le _ _
    _ ≤ ‖Et - E0‖ * ‖Ct‖ + ‖E0‖ * ‖Ct - C0‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ cmp98SourceOuterExpDisplacementBudget A t r * 1 +
          cmp98SourceOuterExpNormBudget r *
            cmp98SourceCoarseContourDisplacementBudget A t := by
      exact add_le_add
        (mul_le_mul hEt hCt.le (norm_nonneg _)
          ((norm_nonneg _).trans hEt))
        (mul_le_mul hE0 hC (norm_nonneg _) ((norm_nonneg _).trans hE0))
    _ = _ := by ring

/-- The exact relative deviation fed into `nearLog` is source-bounded. -/
theorem norm_cmp98Eq119NonlinearRelativeDeviation_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hr : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hr1 : r < 1) :
    ‖cmp98Eq119NonlinearRelativeDeviation U A b t‖ ≤
      cmp98SourcePhysicalBlockDisplacementBudget A t r := by
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
  have hdecomp : cmp98Eq119NonlinearRelativeDeviation U A b t =
      cmp98Eq123PhysicalProductDisplacement U A b t *
        cmp98Eq119NonlinearBlockInverseAtZero U A b := by
    unfold cmp98Eq119NonlinearRelativeDeviation
      cmp98Eq123PhysicalProductDisplacement
      cmp98Eq119NonlinearBlockCurve
    exact twoFactorDisplacement_mul_rightInverse
      (cmp98UbarExpAverage U b
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) *
        cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) t)
      (cmp98UbarExpAverage U b 0 *
        cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)
      (cmp98Eq119NonlinearBlockInverseAtZero U A b) hI
  have hr13 : (1 / 3 : ℝ) ≤ r := by
    linarith [cmp98SourceContourDisplacementBudget_nonneg A t]
  rw [hdecomp]
  exact (norm_mul_le _ _).trans (mul_le_mul
    (norm_cmp98Eq123PhysicalProduct_sub_zero_le_sourceBudget
      U A b t r hbase hsmall hr hr1)
    (norm_cmp98Eq119NonlinearBlockInverseAtZero_le_sourceBudget
      U A b r hbase hr13 hr1)
    (norm_nonneg _)
    ((norm_nonneg _).trans
      (norm_cmp98Eq123PhysicalProduct_sub_zero_le_sourceBudget
        U A b t r hbase hsmall hr hr1)))

/-- Monotonicity estimate for the sharp Mercator remainder majorant. -/
theorem sq_div_one_sub_le_sq_div_one_sub
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    x ^ 2 / (1 - x) ≤ y ^ 2 / (1 - y) := by
  have hx1 : 0 < 1 - x := by linarith
  have hy1 : 0 < 1 - y := by linarith
  rw [div_le_div_iff₀ hx1 hy1]
  have hy0 : 0 ≤ y := hx.trans hxy
  have hfactor : 0 ≤ (y - x) * (x * (1 - y) + y) :=
    mul_nonneg (sub_nonneg.mpr hxy)
      (add_nonneg (mul_nonneg hx (le_of_lt hy1)) hy0)
  nlinarith

set_option maxHeartbeats 3000000 in
/-- Complete source-explicit quantitative form of the CMP98 (123)
logarithmic remainder. -/
theorem norm_cmp98Eq122NonlinearLogRemainder_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hr : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hr1 : r < 1)
    (hdev1 : cmp98SourcePhysicalBlockDisplacementBudget A t r < 1) :
    let R := cmp98SourceLogAverageRadius r
    let D := nearLogDerivativeBudget r *
      cmp98SourceContourDisplacementBudget A t
    let Q := nearLogSecondDerivativeBudget r *
          cmp98SourceContourDisplacementBudget A t ^ 2 +
        nearLogDerivativeBudget r *
          cmp98SourceContourQuadraticBudget A t
    let QE := expSecondDerivativeBudget R * D ^ 2 +
      expDerivativeBudget R * Q
    let B := cmp98SourcePhysicalBlockDisplacementBudget A t r
    ‖cmp98Eq122NonlinearLogRemainder U A b t‖ ≤
      B ^ 2 / (1 - B) +
        (QE + cmp98SourceOuterExpNormBudget r *
            cmp98SourceCoarseContourQuadraticBudget A t +
          cmp98SourceOuterExpDisplacementBudget A t r *
            cmp98SourceCoarseContourDisplacementBudget A t) *
          cmp98SourceOuterExpNormBudget r := by
  dsimp only
  let Z := cmp98Eq119NonlinearRelativeDeviation U A b t
  let B := cmp98SourcePhysicalBlockDisplacementBudget A t r
  have hZ : ‖Z‖ ≤ B := by
    exact norm_cmp98Eq119NonlinearRelativeDeviation_le_sourceBudget
      U A b t r hbase hsmall hr hr1
  have hZ1 : ‖Z‖ < 1 := hZ.trans_lt hdev1
  have hcorrection : ‖nearLog Z - Z‖ ≤ B ^ 2 / (1 - B) :=
    (norm_nearLog_sub_self_le hZ1).trans
      (sq_div_one_sub_le_sq_div_one_sub (norm_nonneg Z)
        hZ hdev1)
  rw [cmp98Eq122NonlinearLogRemainder_eq_nearLogCorrection_add_physicalRemainder]
  exact (norm_add_le _ _).trans (add_le_add hcorrection
    (norm_cmp98Eq123PhysicalBlockRemainder_le_sourceBudget
      U A b t r hbase hsmall hr hr1))

end

end YangMills.RG

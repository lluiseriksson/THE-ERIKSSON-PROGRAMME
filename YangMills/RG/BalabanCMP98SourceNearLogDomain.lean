/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98ContourExponentialTransport
import YangMills.RG.BalabanCMP98Eq123AnalyticRemainder

/-!
# A source-explicit Mercator domain along the CMP98 physical line

The qualitative analytic proof of CMP98 (123) assumes that every local
four-contour deviation lies in the open Mercator unit ball.  The exact
exponential transport now turns that assumption away from the background
into a scalar source budget.  Starting from the printed one-third margin,
the entire logarithmic block average and its outer exponential are analytic
at every physical parameter for which the volume-independent contour budget
is smaller than two thirds.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98SourceNearLogDomainMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Explicit displacement budget for one complete CMP98 source contour. -/
def cmp98SourceContourDisplacementBudget
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t : ℝ) : ℝ :=
  (2 * (d + 1) * M : ℕ) *
      (2 * (|t| * cmp98SourceFieldSupNorm A)) *
      (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^
        (2 * (d + 1) * M)

theorem cmp98SourceContourDisplacementBudget_nonneg
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t : ℝ) :
    0 ≤ cmp98SourceContourDisplacementBudget A t := by
  unfold cmp98SourceContourDisplacementBudget
  have hq : 0 ≤ |t| * cmp98SourceFieldSupNorm A :=
    mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
  positivity

/-- The one-third background margin and a two-thirds source displacement
budget keep every point of the block in the Mercator domain. -/
theorem cmp98UbarAmbientDeviationMatrix_physicalLine_lt_one_of_third
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hbudget : cmp98SourceContourDisplacementBudget A t < 2 / 3) :
    ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))‖ < 1 := by
  intro x hx
  apply norm_cmp98UbarAmbientDeviationMatrix_physicalLine_lt_one
    U A b x hx t (1 / 3)
  · exact hbase x hx
  · exact hsmall
  · change (1 / 3 : ℝ) + cmp98SourceContourDisplacementBudget A t < 1
    linarith

/-- Source-explicit analyticity of the literal logarithmic block average at
an arbitrary physical parameter. -/
theorem analyticAt_cmp98UbarLogAverage_physicalLine_of_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hbudget : cmp98SourceContourDisplacementBudget A t < 2 / 3) :
    AnalyticAt ℝ
      (fun s : ℝ => cmp98UbarLogAverage U b
        (s • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))) t := by
  let V : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  have hline : AnalyticAt ℝ (fun s : ℝ => s • V) t :=
    analyticAt_id.smul analyticAt_const
  have hlog := analyticAt_cmp98UbarLogAverage_of_norm_lt_one
    U b (t • V)
      (cmp98UbarAmbientDeviationMatrix_physicalLine_lt_one_of_third
        U A b t hbase hsmall hbudget)
  simpa [V, Function.comp_def] using hlog.comp_of_eq' hline rfl

/-- Source-explicit analyticity of the outer exponential appearing in the
represented nonlinear block of CMP98 (118)--(119). -/
theorem analyticAt_cmp98UbarExpAverage_physicalLine_of_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hbudget : cmp98SourceContourDisplacementBudget A t < 2 / 3) :
    AnalyticAt ℝ
      (fun s : ℝ => cmp98UbarExpAverage U b
        (s • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))) t := by
  let V : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  have hline : AnalyticAt ℝ (fun s : ℝ => s • V) t :=
    analyticAt_id.smul analyticAt_const
  have hexp := analyticAt_cmp98UbarExpAverage_of_norm_lt_one
    U b (t • V)
      (cmp98UbarAmbientDeviationMatrix_physicalLine_lt_one_of_third
        U A b t hbase hsmall hbudget)
  simpa [V, Function.comp_def] using hexp.comp_of_eq' hline rfl

end

end YangMills.RG

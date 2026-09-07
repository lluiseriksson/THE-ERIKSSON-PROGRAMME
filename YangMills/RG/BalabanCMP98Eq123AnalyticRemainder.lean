/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq123QuadraticFrontier
import YangMills.RG.NearLogAnalytic
import YangMills.RG.AnalyticScalarQuadraticRemainder

/-!
# Analytic quadratic remainder for CMP98 (123)

This file closes the local second-order statement behind CMP98 (123).  Every
constituent is the literal physical one: finite contour holonomies, the four
contour deviation, the Mercator logarithm on its open unit ball, the finite
block average, and the outer matrix exponential.  Their composition is
analytic at the physical background.  Taylor's theorem therefore supplies
the quadratic remainder for the represented block, which the exact frontier
theorem transports through the final local logarithm.

The conclusion is a local asymptotic `O(t²)` statement.  It does not yet claim
the source-uniform numerical constant printed in (123).
-/

namespace YangMills.RG

open YangMills Matrix Asymptotics
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq123AnalyticRemainderMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The literal finite logarithmic block average is analytic wherever all
its physical four-contour deviations lie in the Mercator unit ball. -/
theorem analyticAt_cmp98UbarLogAverage_of_norm_lt_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1) :
    AnalyticAt ℝ (cmp98UbarLogAverage U b) Z := by
  have hsum : AnalyticAt ℝ
      (fun W => ∑ x ∈ blockOf M N' b.1,
        nearLog (cmp98UbarAmbientDeviationMatrix U b x W)) Z := by
    apply Finset.analyticAt_fun_sum
    intro x hx
    have hlog := analyticAt_nearLog_of_norm_lt_one (hsmall x hx)
    simpa [Function.comp_def] using
      hlog.comp (analyticAt_cmp98UbarAmbientDeviationMatrix U b x Z)
  simpa [cmp98UbarLogAverage, Pi.smul_apply] using
    hsum.const_smul (c := ((M : ℝ) ^ d)⁻¹)

/-- The outer exponential of the literal logarithmic average is analytic at
the physical background. -/
theorem analyticAt_cmp98UbarExpAverage_of_norm_lt_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1) :
    AnalyticAt ℝ (cmp98UbarExpAverage U b) Z := by
  have hexp := NormedSpace.exp_analytic (𝕂 := ℝ)
    (cmp98UbarLogAverage U b Z)
  simpa [cmp98UbarExpAverage, Function.comp_def] using
    hexp.comp (analyticAt_cmp98UbarLogAverage_of_norm_lt_one U b Z hsmall)

/-- Analyticity of the outer averaged exponential along the literal physical
one-parameter line. -/
theorem analyticAt_cmp98UbarExpAverage_physicalLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    AnalyticAt ℝ
      (fun t : ℝ => cmp98UbarExpAverage U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))) 0 := by
  let V : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  have hline : AnalyticAt ℝ (fun t : ℝ => t • V) 0 :=
    analyticAt_id.smul analyticAt_const
  have houter := analyticAt_cmp98UbarExpAverage_of_norm_lt_one
    U b (0 : PhysicalAmbientMatrixTangent d (M * N') Nc) hsmall
  have hcomp := houter.comp_of_eq'
    (f := fun t : ℝ => t • V) hline (zero_smul ℝ V)
  simpa [V] using hcomp

/-- Every literal finite contour curve is analytic in its real physical
chart parameter. -/
theorem analyticAt_cmp98ContourMatrixCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    AnalyticAt ℝ (cmp98ContourMatrixCurve U A es) 0 := by
  let V : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  have hline : AnalyticAt ℝ (fun t : ℝ => t • V) 0 :=
    analyticAt_id.smul analyticAt_const
  have hamb := analyticAt_cmp98AmbientWilsonLineMatrix U
    (0 : PhysicalAmbientMatrixTangent d (M * N') Nc) es
  have hcomp := hamb.comp_of_eq'
    (f := fun t : ℝ => t • V) hline (zero_smul ℝ V)
  have hfun :
      (fun t : ℝ => cmp98AmbientWilsonLineMatrix U (t • V) es) =
        cmp98ContourMatrixCurve U A es := by
    funext t
    simpa [V] using
      cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve U A es t
  simpa [Function.comp_def, hfun] using hcomp

/-- The exact represented nonlinear block of (118)--(119) is analytic at the
physical background. -/
theorem analyticAt_cmp98Eq119NonlinearBlockCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    AnalyticAt ℝ (cmp98Eq119NonlinearBlockCurve U A b) 0 := by
  simpa [cmp98Eq119NonlinearBlockCurve] using
    (analyticAt_cmp98UbarExpAverage_physicalLine U A b hsmall).mul
      (analyticAt_cmp98ContourMatrixCurve U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b))

/-- The normalized relative deviation before the final logarithm is
analytic at zero. -/
theorem analyticAt_cmp98Eq119NonlinearRelativeDeviation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    AnalyticAt ℝ (cmp98Eq119NonlinearRelativeDeviation U A b) 0 := by
  have hconstInv : AnalyticAt ℝ
      (fun _ : ℝ => cmp98Eq119NonlinearBlockInverseAtZero U A b) 0 :=
    analyticAt_const
  have hmul :=
    (analyticAt_cmp98Eq119NonlinearBlockCurve U A b hsmall).mul hconstInv
  have hconstOne : AnalyticAt ℝ
      (fun _ : ℝ => (1 : Matrix (Fin Nc) (Fin Nc) ℂ)) 0 :=
    analyticAt_const
  simpa [cmp98Eq119NonlinearRelativeDeviation] using
    hmul.sub hconstOne

/-- The literal represented block has a quadratic remainder before applying
the final logarithm. -/
theorem cmp98Eq123PhysicalBlockRemainder_isBigO_sq
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp98Eq123PhysicalBlockRemainder U A b =O[nhds 0]
      (fun t : ℝ => t ^ 2) := by
  have hrem := AnalyticAt.isBigO_sub_value_sub_deriv_smul_sq
    (analyticAt_cmp98Eq119NonlinearRelativeDeviation U A b hsmall)
  have hderiv :
      deriv (cmp98Eq119NonlinearRelativeDeviation U A b) 0 =
        cmp98Eq119NonlinearRightVariation U A b := by
    rw [(hasDerivAt_cmp98Eq119NonlinearRelativeDeviation U A b hsmall).deriv]
    unfold cmp98Eq119NonlinearRightVariation
    rw [(hasDerivAt_cmp98Eq119NonlinearBlockCurve U A b hsmall).deriv]
  simpa [cmp98Eq123PhysicalBlockRemainder,
    cmp98Eq119NonlinearRelativeDeviation_zero, hderiv] using hrem

/-- Local quadratic closure of the exact nonlinear logarithmic remainder
behind CMP98 (123). -/
theorem cmp98Eq122NonlinearLogRemainder_isBigO_sq
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp98Eq122NonlinearLogRemainder U A b =O[nhds 0]
      (fun t : ℝ => t ^ 2) :=
  (cmp98Eq122NonlinearLogRemainder_isBigO_sq_iff_physicalBlockRemainder
    U A b hsmall).2
      (cmp98Eq123PhysicalBlockRemainder_isBigO_sq U A b hsmall)

end

end YangMills.RG

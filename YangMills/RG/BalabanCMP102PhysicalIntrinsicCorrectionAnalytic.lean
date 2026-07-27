/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalCorrectionChartIndependence
import YangMills.RG.BalabanCMP102PhysicalRightVariationLinearity
import YangMills.RG.BalabanCMP98Eq123AnalyticRemainder
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Intrinsic analytic form of the physical CMP102 correction

The chart certificates used by the source estimates are not part of the
physical correction.  This module writes the correction directly in the
ambient exponential chart, projects the literal matrix remainder back to
canonical `su(N)` coordinates, and proves local smoothness on the genuine
Mercator domain.

This supplies the source map needed by a later implicit-function argument.
It does not assume regularity of the selected fixed point.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102IntrinsicCorrectionMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Continuous linear inclusion of physical cochains into the ambient
matrix tangent chart. -/
noncomputable def cmp102PhysicalCochainToAmbientCLM :
    PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
      PhysicalAmbientMatrixTangent d (M * N') Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)
      map_add' := by
        intro A B
        rw [physicalCochainToSuMatrixTangent_add]
        rfl
      map_smul' := by
        intro r A
        rw [physicalCochainToSuMatrixTangent_smul]
        rfl }

@[simp] theorem cmp102PhysicalCochainToAmbientCLM_apply
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    cmp102PhysicalCochainToAmbientCLM A =
      physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A) := rfl

/-- The intrinsic ambient equation-(122) remainder at a coarse bond.  The
normalizing inverse and linear subtraction are taken from the same fixed
ambient represented-block map. -/
def cmp102IntrinsicAmbientCorrectionBond
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  let I :=
    cmp98Eq119NonlinearBlockInverseAtZero U
      (0 : PhysicalGaugeOneCochain d (M * N') Nc) b
  nearLog (cmp102AmbientNonlinearBlock U b Z * I - 1) -
    fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 Z * I

/-- The intrinsic ambient correction is analytic wherever the inner block
logs and the final relative log remain in their literal unit balls. -/
theorem analyticAt_cmp102IntrinsicAmbientCorrectionBond
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (hlocal : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1)
    (hrelative :
      ‖cmp102AmbientNonlinearBlock U b Z *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1) :
    AnalyticAt ℝ (cmp102IntrinsicAmbientCorrectionBond U b) Z := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  let I :=
    cmp98Eq119NonlinearBlockInverseAtZero U
      (0 : PhysicalGaugeOneCochain d (M * N') Nc) b
  have hblock : AnalyticAt ℝ (cmp102AmbientNonlinearBlock U b) Z := by
    unfold cmp102AmbientNonlinearBlock
    exact
      (analyticAt_cmp98UbarExpAverage_of_norm_lt_one U b Z hlocal).mul
        (analyticAt_cmp98AmbientWilsonLineMatrix U Z
          (cmp98SourceCoarseBondPath (Nc := Nc) b))
  have hdev : AnalyticAt ℝ
      (fun W => cmp102AmbientNonlinearBlock U b W * I - 1) Z :=
    (hblock.mul analyticAt_const).sub analyticAt_const
  have hlog : AnalyticAt ℝ
      (fun W => nearLog
        (cmp102AmbientNonlinearBlock U b W * I - 1)) Z := by
    exact (analyticAt_nearLog_of_norm_lt_one
      (by simpa [I] using hrelative)).comp hdev
  have hlinear : AnalyticAt ℝ
      (fun W =>
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 W * I) Z :=
    ((fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0).analyticAt Z).mul
      analyticAt_const
  simpa [cmp102IntrinsicAmbientCorrectionBond, I] using hlog.sub hlinear

/-- The physical correction written without a chart certificate. -/
noncomputable def cmp102IntrinsicPhysicalNonlinearCorrection
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    CoarsePhysicalOneCochain d N' Nc :=
  WithLp.toLp 2 fun b =>
    cmp98AmbientToLieCoordCLM Nc
      (cmp102IntrinsicAmbientCorrectionBond U b
        (cmp102PhysicalCochainToAmbientCLM A))

@[simp] theorem cmp102IntrinsicPhysicalNonlinearCorrection_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp102IntrinsicPhysicalNonlinearCorrection U A b =
      cmp98AmbientToLieCoordCLM Nc
        (cmp102IntrinsicAmbientCorrectionBond U b
          (cmp102PhysicalCochainToAmbientCLM A)) := rfl

/-- Local smoothness of the intrinsic physical correction.  The hypotheses
are precisely the two open Mercator-domain conditions of the literal source
formula, evaluated at the base field. -/
theorem contDiffAt_cmp102IntrinsicPhysicalNonlinearCorrection
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (hlocal : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM A)‖ < 1)
    (hrelative : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM A) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1) :
    ContDiffAt ℝ ⊤ (cmp102IntrinsicPhysicalNonlinearCorrection U) A := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  have hcoord : ∀ b : PhysicalBond d N',
      AnalyticAt ℝ
        (fun X : PhysicalGaugeOneCochain d (M * N') Nc =>
          cmp98AmbientToLieCoordCLM Nc
            (cmp102IntrinsicAmbientCorrectionBond U b
              (cmp102PhysicalCochainToAmbientCLM X))) A := by
    intro b
    have hintrinsic : AnalyticAt ℝ
        (fun X : PhysicalGaugeOneCochain d (M * N') Nc =>
          cmp102IntrinsicAmbientCorrectionBond U b
            (cmp102PhysicalCochainToAmbientCLM X)) A := by
      simpa only [Function.comp_apply] using
        (analyticAt_cmp102IntrinsicAmbientCorrectionBond U b
          (cmp102PhysicalCochainToAmbientCLM A)
          (hlocal b) (hrelative b)).comp
            ((cmp102PhysicalCochainToAmbientCLM).analyticAt A)
    simpa only [Function.comp_apply] using
      ((cmp98AmbientToLieCoordCLM Nc).analyticAt
        (cmp102IntrinsicAmbientCorrectionBond U b
          (cmp102PhysicalCochainToAmbientCLM A))).comp'
            (f := fun X : PhysicalGaugeOneCochain d (M * N') Nc =>
              cmp102IntrinsicAmbientCorrectionBond U b
                (cmp102PhysicalCochainToAmbientCLM X)) hintrinsic
  have hpi : AnalyticAt ℝ
      (fun X : PhysicalGaugeOneCochain d (M * N') Nc =>
        fun b : PhysicalBond d N' =>
          cmp98AmbientToLieCoordCLM Nc
            (cmp102IntrinsicAmbientCorrectionBond U b
              (cmp102PhysicalCochainToAmbientCLM X))) A :=
    AnalyticAt.pi hcoord
  unfold cmp102IntrinsicPhysicalNonlinearCorrection
  exact PiLp.contDiff_toLp.contDiffAt.comp A hpi.contDiffAt

end

end YangMills.RG

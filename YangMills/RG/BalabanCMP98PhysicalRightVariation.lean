/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98PhysicalLieRetraction

/-!
# The physical CMP98 right variation is `su(N)`-valued

The normalized nonlinear block is already known to be a genuine `SU(N)`
curve on its logarithmic chart.  Here a local chart certificate supplies the
near-identity and no-winding budgets on a real neighbourhood of the origin.
The physical logarithm is lifted to `SUNLieCoord` there and extended by zero
outside the chart solely to obtain a total function.

Locally this coordinate curve is exactly the continuous linear retraction of
the ambient logarithm.  Differentiating and then decoding it gives the
projection of the ambient right variation.  A second differentiation of the
literal decoded curve gives the ambient right variation itself.  Uniqueness
of derivatives therefore proves that the projection fixes the right
variation.  This supplies a genuine `SuLie` element without projecting the
physical answer by definition.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Source-local logarithmic chart around the physical background. -/
structure CMP98PhysicalNonlinearLocalChart
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') where
  radius : ℝ
  radius_pos : 0 < radius
  near : ∀ t, |t| < radius → ∀ x ∈ blockOf M N' b.1,
    ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1
  noWinding : ∀ t, |t| < radius → ∀ x ∈ blockOf M N' b.1,
    (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi
  relativeNear : ∀ t (ht : |t| < radius),
    ‖(cmp98PhysicalNonlinearRelativeSUN U A b t
        (near t ht) (noWinding t ht)
        (near 0 (by simpa using radius_pos))
        (noWinding 0 (by simpa using radius_pos)) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1
  relativeNoWinding : ∀ t (ht : |t| < radius),
    (Nc : ℝ) *
      ‖nearLog
        ((cmp98PhysicalNonlinearRelativeSUN U A b t
          (near t ht) (noWinding t ht)
          (near 0 (by simpa using radius_pos))
          (noWinding 0 (by simpa using radius_pos)) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi

/-- The physical nonlinear coordinate on its local chart, extended by zero
outside the certified interval. -/
noncomputable def cmp98PhysicalNonlinearLocalCoordinate
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b)
    (t : ℝ) : SUNLieCoord Nc :=
  if ht : |t| < Chart.radius then
    cmp98PhysicalNonlinearLogCoordinate U A b t
      (Chart.near t ht) (Chart.noWinding t ht)
      (Chart.near 0 (by simpa using Chart.radius_pos))
      (Chart.noWinding 0 (by simpa using Chart.radius_pos))
      (Chart.relativeNear t ht)
      (Chart.relativeNoWinding t ht)
  else 0

theorem cmp98PhysicalNonlinearLocalCoordinate_eq_retraction_of_abs_lt
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b)
    {t : ℝ} (ht : |t| < Chart.radius) :
    cmp98PhysicalNonlinearLocalCoordinate U A b Chart t =
      cmp98AmbientToLieCoordCLM Nc
        (cmp98Eq119NonlinearLogCoordinate U A b t) := by
  rw [cmp98PhysicalNonlinearLocalCoordinate, dif_pos ht]
  let X := cmp98PhysicalNonlinearLogCoordinate U A b t
    (Chart.near t ht) (Chart.noWinding t ht)
    (Chart.near 0 (by simpa using Chart.radius_pos))
    (Chart.noWinding 0 (by simpa using Chart.radius_pos))
    (Chart.relativeNear t ht)
    (Chart.relativeNoWinding t ht)
  calc
    X = cmp98AmbientToLieCoordCLM Nc
        (cmp98LieCoordToAmbientCLM Nc X) := by
          symm
          exact cmp98AmbientToLieCoordCLM_leftInverse X
    _ = cmp98AmbientToLieCoordCLM Nc
        (cmp98Eq119NonlinearLogCoordinate U A b t) := by
          apply congrArg
          exact cmp98PhysicalNonlinearLogCoordinate_toMatrix U A b t
            (Chart.near t ht) (Chart.noWinding t ht)
            (Chart.near 0 (by simpa using Chart.radius_pos))
            (Chart.noWinding 0 (by simpa using Chart.radius_pos))
            (Chart.relativeNear t ht)
            (Chart.relativeNoWinding t ht)

theorem cmp98LieCoordToAmbient_localCoordinate_eq_log_of_abs_lt
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b)
    {t : ℝ} (ht : |t| < Chart.radius) :
    cmp98LieCoordToAmbientCLM Nc
        (cmp98PhysicalNonlinearLocalCoordinate U A b Chart t) =
      cmp98Eq119NonlinearLogCoordinate U A b t := by
  rw [cmp98PhysicalNonlinearLocalCoordinate, dif_pos ht]
  exact cmp98PhysicalNonlinearLogCoordinate_toMatrix U A b t
    (Chart.near t ht) (Chart.noWinding t ht)
    (Chart.near 0 (by simpa using Chart.radius_pos))
    (Chart.noWinding 0 (by simpa using Chart.radius_pos))
    (Chart.relativeNear t ht)
    (Chart.relativeNoWinding t ht)

theorem cmp98PhysicalNonlinearLocalCoordinate_eventuallyEq_retraction
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b) :
    cmp98PhysicalNonlinearLocalCoordinate U A b Chart =ᶠ[nhds 0]
      fun t => cmp98AmbientToLieCoordCLM Nc
        (cmp98Eq119NonlinearLogCoordinate U A b t) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) Chart.radius_pos] with t ht
  apply cmp98PhysicalNonlinearLocalCoordinate_eq_retraction_of_abs_lt
  simpa [Real.dist_eq] using ht

theorem cmp98LieCoordToAmbient_localCoordinate_eventuallyEq_log
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b) :
    (fun t => cmp98LieCoordToAmbientCLM Nc
      (cmp98PhysicalNonlinearLocalCoordinate U A b Chart t)) =ᶠ[nhds 0]
        cmp98Eq119NonlinearLogCoordinate U A b := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) Chart.radius_pos] with t ht
  apply cmp98LieCoordToAmbient_localCoordinate_eq_log_of_abs_lt
  simpa [Real.dist_eq] using ht

/-- The local physical coordinate has the retracted ambient right variation
as its exact derivative. -/
theorem hasDerivAt_cmp98PhysicalNonlinearLocalCoordinate
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b) :
    HasDerivAt (cmp98PhysicalNonlinearLocalCoordinate U A b Chart)
      (cmp98AmbientToLieCoordCLM Nc
        (cmp98Eq119NonlinearRightVariation U A b)) 0 := by
  have hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
    intro x hx
    have hzero :
        (0 : ℝ) • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A) = 0 := zero_smul ℝ _
    rw [← hzero,
      cmp98UbarAmbientDeviationMatrix_line_eq_relativeSUN_sub_one]
    exact Chart.near 0 (by simpa using Chart.radius_pos) x hx
  have hamb0 :=
    hasDerivAt_cmp98Eq119NonlinearLogCoordinate U A b hbase
  have hcoefficient :
      fourFactorFirst (cmp98Eq119NonlinearFactors U A b)
          (cmp98Eq119NonlinearFactorVariations U A b) 0 *
        cmp98Eq119NonlinearBlockInverseAtZero U A b =
      cmp98Eq119NonlinearRightVariation U A b :=
    hamb0.deriv.symm.trans
      (deriv_cmp98Eq119NonlinearLogCoordinate_zero_eq_rightVariation
        U A b hbase)
  have hamb := hamb0.congr_deriv hcoefficient
  have hcomp :=
    (cmp98AmbientToLieCoordCLM Nc).hasFDerivAt.comp_hasDerivAt 0 hamb
  exact hcomp.congr_of_eventuallyEq
    (cmp98PhysicalNonlinearLocalCoordinate_eventuallyEq_retraction
      U A b Chart)

/-- The chosen projection fixes the actual physical right variation. -/
theorem cmp98AmbientToSuLieLinearMap_rightVariation_toMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b) :
    (cmp98AmbientToSuLieLinearMap Nc
      (cmp98Eq119NonlinearRightVariation U A b)).toMatrix =
        cmp98Eq119NonlinearRightVariation U A b := by
  have hcoord :=
    hasDerivAt_cmp98PhysicalNonlinearLocalCoordinate U A b Chart
  have hdecoded :=
    (cmp98LieCoordToAmbientCLM Nc).hasFDerivAt.comp_hasDerivAt 0 hcoord
  have heventually :
      cmp98Eq119NonlinearLogCoordinate U A b =ᶠ[nhds 0]
        (cmp98LieCoordToAmbientCLM Nc) ∘
          cmp98PhysicalNonlinearLocalCoordinate U A b Chart := by
    simpa only [Function.comp_apply] using
      (cmp98LieCoordToAmbient_localCoordinate_eventuallyEq_log
        U A b Chart).symm
  have hdecoded' := hdecoded.congr_of_eventuallyEq heventually
  have hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
    intro x hx
    have hzero :
        (0 : ℝ) • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A) = 0 := zero_smul ℝ _
    rw [← hzero,
      cmp98UbarAmbientDeviationMatrix_line_eq_relativeSUN_sub_one]
    exact Chart.near 0 (by simpa using Chart.radius_pos) x hx
  have hamb0 :=
    hasDerivAt_cmp98Eq119NonlinearLogCoordinate U A b hbase
  have hcoefficient :
      fourFactorFirst (cmp98Eq119NonlinearFactors U A b)
          (cmp98Eq119NonlinearFactorVariations U A b) 0 *
        cmp98Eq119NonlinearBlockInverseAtZero U A b =
      cmp98Eq119NonlinearRightVariation U A b :=
    hamb0.deriv.symm.trans
      (deriv_cmp98Eq119NonlinearLogCoordinate_zero_eq_rightVariation
        U A b hbase)
  have hamb := hamb0.congr_deriv hcoefficient
  have hderiv := hdecoded'.unique hamb
  have hprojection :=
    cmp98LieCoordToAmbientCLM_rightInverse_projection
      (Nc := Nc) (cmp98Eq119NonlinearRightVariation U A b)
  exact hprojection.symm.trans hderiv

/-- The genuine `su(N)`-valued physical right variation. -/
noncomputable def cmp98PhysicalNonlinearRightVariationSuLie
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    SuLie Nc :=
  cmp98AmbientToSuLieLinearMap Nc
    (cmp98Eq119NonlinearRightVariation U A b)

@[simp] theorem cmp98PhysicalNonlinearRightVariationSuLie_toMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b) :
    (cmp98PhysicalNonlinearRightVariationSuLie
      U A b).toMatrix =
        cmp98Eq119NonlinearRightVariation U A b :=
  cmp98AmbientToSuLieLinearMap_rightVariation_toMatrix U A b Chart

/-- The physical linear right variation in canonical coordinates. -/
noncomputable def cmp98PhysicalNonlinearRightVariationLieCoord
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    SUNLieCoord Nc :=
  suLieCoordIso Nc
    (cmp98PhysicalNonlinearRightVariationSuLie U A b)

theorem cmp98PhysicalNonlinearRightVariationLieCoord_eq_retraction
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98PhysicalNonlinearRightVariationLieCoord U A b =
      cmp98AmbientToLieCoordCLM Nc
        (cmp98Eq119NonlinearRightVariation U A b) := by
  rfl

/-- The source correction `C` along a physical ray: exact nonlinear
coordinate minus its exact linear right variation. -/
noncomputable def cmp102PhysicalNonlinearCorrectionRay
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b)
    (t : ℝ) : SUNLieCoord Nc :=
  cmp98PhysicalNonlinearLocalCoordinate U A b Chart t -
    t • cmp98PhysicalNonlinearRightVariationLieCoord U A b

/-- On the certified chart, decoding the physical correction gives exactly
the ambient CMP98 nonlinear logarithmic remainder. -/
theorem cmp102PhysicalNonlinearCorrectionRay_toMatrix_of_abs_lt
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b)
    {t : ℝ} (ht : |t| < Chart.radius) :
    cmp98LieCoordToAmbientCLM Nc
        (cmp102PhysicalNonlinearCorrectionRay U A b Chart t) =
      cmp98Eq122NonlinearLogRemainder U A b t := by
  unfold cmp102PhysicalNonlinearCorrectionRay
    cmp98PhysicalNonlinearRightVariationLieCoord
  rw [map_sub, map_smul]
  rw [cmp98LieCoordToAmbient_localCoordinate_eq_log_of_abs_lt
    U A b Chart ht]
  rw [cmp98LieCoordToAmbientCLM_apply,
    (suLieCoordIso Nc).symm_apply_apply]
  rw [cmp98PhysicalNonlinearRightVariationSuLie_toMatrix U A b Chart]
  rfl

@[simp] theorem cmp102PhysicalNonlinearCorrectionRay_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b) :
    cmp102PhysicalNonlinearCorrectionRay U A b Chart 0 = 0 := by
  have hzero :
      cmp98PhysicalNonlinearLocalCoordinate U A b Chart 0 = 0 := by
    rw [cmp98PhysicalNonlinearLocalCoordinate_eq_retraction_of_abs_lt
      U A b Chart (by simpa using Chart.radius_pos)]
    simp
  unfold cmp102PhysicalNonlinearCorrectionRay
  rw [hzero, zero_smul, sub_zero]

/-- The physical correction begins quadratically: its first derivative
vanishes exactly. -/
theorem hasDerivAt_cmp102PhysicalNonlinearCorrectionRay_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (Chart : CMP98PhysicalNonlinearLocalChart U A b) :
    HasDerivAt (cmp102PhysicalNonlinearCorrectionRay U A b Chart) 0 0 := by
  have hcoord :=
    hasDerivAt_cmp98PhysicalNonlinearLocalCoordinate U A b Chart
  rw [← cmp98PhysicalNonlinearRightVariationLieCoord_eq_retraction] at hcoord
  have hline : HasDerivAt
      (fun t : ℝ =>
        t • cmp98PhysicalNonlinearRightVariationLieCoord U A b)
      (cmp98PhysicalNonlinearRightVariationLieCoord U A b) 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
      (cmp98PhysicalNonlinearRightVariationLieCoord U A b)
  simpa only [cmp102PhysicalNonlinearCorrectionRay, sub_self] using
    hcoord.sub hline

end

end YangMills.RG

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102IntrinsicAmbientCorrectionSourceBudget

/-!
# Source derivative budget for one physical intrinsic-correction coordinate

This module transports the source-generated ambient derivative-Lipschitz
estimate through the literal physical inclusion and Lie-coordinate
projection.  The two finite-dimensional coordinate maps appear only through
their actual operator norms; no caller-supplied comparison constant is used.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102PhysicalIntrinsicCoordCLMNorm :
    Norm (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp102PhysicalIntrinsicCoordCLMSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp102PhysicalIntrinsicCoordCLMNormedSpace :
    NormedSpace ℝ
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toNormedSpace

/-- One bond coordinate of the intrinsic physical correction. -/
noncomputable def cmp102IntrinsicPhysicalCorrectionBondCoord
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    SUNLieCoord Nc :=
  cmp98AmbientToLieCoordCLM Nc
    (cmp102IntrinsicAmbientCorrectionBond U b
      (cmp102PhysicalCochainToAmbientCLM A))

/-- Coordinate-transported source derivative-Lipschitz budget. -/
def cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
    (d M N' Nc : ℕ) [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (r q s : ℝ) : ℝ :=
  ‖cmp98AmbientToLieCoordCLM Nc‖ *
    cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
      d M r q s *
    ‖(cmp102PhysicalCochainToAmbientCLM :
      PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
        PhysicalAmbientMatrixTangent d (M * N') Nc)‖ ^ 2

set_option maxHeartbeats 1000000 in
/-- Exact chain rule for a physical bond coordinate of the intrinsic
correction. -/
theorem fderiv_cmp102IntrinsicPhysicalCorrectionBondCoord_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (A H : PhysicalGaugeOneCochain d (M * N') Nc)
    (hlocal : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM A)‖ < 1)
    (hrelative :
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM A) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1) :
    fderiv ℝ (cmp102IntrinsicPhysicalCorrectionBondCoord U b) A H =
      cmp98AmbientToLieCoordCLM Nc
        (fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b)
          (cmp102PhysicalCochainToAmbientCLM A)
          (cmp102PhysicalCochainToAmbientCLM H)) := by
  have hintrinsic :=
    (analyticAt_cmp102IntrinsicAmbientCorrectionBond U b
      (cmp102PhysicalCochainToAmbientCLM A) hlocal hrelative
      ).differentiableAt.hasFDerivAt
  have hinner :=
    hintrinsic.comp A
      (cmp102PhysicalCochainToAmbientCLM :
        PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
          PhysicalAmbientMatrixTangent d (M * N') Nc).hasFDerivAt
  have houter :=
    (cmp98AmbientToLieCoordCLM Nc).hasFDerivAt.comp A hinner
  simpa only [cmp102IntrinsicPhysicalCorrectionBondCoord,
    ContinuousLinearMap.comp_apply] using congrArg
      (fun L => L H) houter.fderiv

/-- The physical one-bond derivative variation is controlled entirely by
the generated source budget and the actual coordinate-map operator norms. -/
theorem norm_fderiv_cmp102IntrinsicPhysicalCorrectionBondCoord_sub_apply_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (A B H : PhysicalGaugeOneCochain d (M * N') Nc)
    {r q s : ℝ}
    (hr : 0 ≤ r) (hq13 : 1 / 3 ≤ q) (hq1 : q < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hA : ‖cmp102PhysicalCochainToAmbientCLM A‖ ≤ r)
    (hB : ‖cmp102PhysicalCochainToAmbientCLM B‖ ≤ r)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hDA : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM A)‖ ≤ q)
    (hDB : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM B)‖ ≤ q)
    (hdev :
      cmp102SourceAmbientRelativeDeviationValueBudget d M r q ≤ s) :
    ‖(fderiv ℝ (cmp102IntrinsicPhysicalCorrectionBondCoord U b) A -
        fderiv ℝ (cmp102IntrinsicPhysicalCorrectionBondCoord U b) B) H‖ ≤
      cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
          d M N' Nc r q s *
        ‖A - B‖ * ‖H‖ := by
  let ZA := cmp102PhysicalCochainToAmbientCLM A
  let ZB := cmp102PhysicalCochainToAmbientCLM B
  let ZH := cmp102PhysicalCochainToAmbientCLM H
  have hq0 : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hq13
  have hrelativeA :
      ‖cmp102AmbientNonlinearBlock U b ZA *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1 :=
    ((norm_cmp102AmbientRelativeDeviation_le_sourceBudget
      U b ZA hr hq13 hq1 hA hbase hDA).trans hdev).trans_lt hs1
  have hrelativeB :
      ‖cmp102AmbientNonlinearBlock U b ZB *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1 :=
    ((norm_cmp102AmbientRelativeDeviation_le_sourceBudget
      U b ZB hr hq13 hq1 hB hbase hDB).trans hdev).trans_lt hs1
  have hambient :
      ‖(fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) ZA -
          fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) ZB) ZH‖ ≤
        cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
            d M r q s *
          ‖ZA - ZB‖ * ‖ZH‖ :=
    norm_fderiv_cmp102IntrinsicAmbientCorrectionBond_sub_apply_le_sourceBudget
      U b ZA ZB ZH hr hq13 hq1 hs0 hs1 hA hB hbase hDA hDB hdev
  rw [ContinuousLinearMap.sub_apply,
    fderiv_cmp102IntrinsicPhysicalCorrectionBondCoord_apply
      U b A H (fun x hx => (hDA x hx).trans_lt hq1) hrelativeA,
    fderiv_cmp102IntrinsicPhysicalCorrectionBondCoord_apply
      U b B H (fun x hx => (hDB x hx).trans_lt hq1) hrelativeB]
  rw [← map_sub]
  calc
    ‖cmp98AmbientToLieCoordCLM Nc
        ((fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) ZA -
          fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) ZB) ZH)‖
        ≤ ‖cmp98AmbientToLieCoordCLM Nc‖ *
            ‖(fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) ZA -
              fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) ZB) ZH‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖cmp98AmbientToLieCoordCLM Nc‖ *
        (cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
            d M r q s * ‖ZA - ZB‖ * ‖ZH‖) := by
      exact mul_le_mul_of_nonneg_left hambient (norm_nonneg _)
    _ ≤ ‖cmp98AmbientToLieCoordCLM Nc‖ *
        (cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
            d M r q s *
          (‖(cmp102PhysicalCochainToAmbientCLM :
              PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
                PhysicalAmbientMatrixTangent d (M * N') Nc)‖ * ‖A - B‖) *
          (‖(cmp102PhysicalCochainToAmbientCLM :
              PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
                PhysicalAmbientMatrixTangent d (M * N') Nc)‖ * ‖H‖)) := by
      have hZA :
          ‖ZA - ZB‖ ≤
            ‖(cmp102PhysicalCochainToAmbientCLM :
              PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
                PhysicalAmbientMatrixTangent d (M * N') Nc)‖ *
              ‖A - B‖ := by
        rw [← map_sub]
        exact ContinuousLinearMap.le_opNorm _ _
      have hZH :
          ‖ZH‖ ≤
            ‖(cmp102PhysicalCochainToAmbientCLM :
              PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
                PhysicalAmbientMatrixTangent d (M * N') Nc)‖ * ‖H‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have hC :
          0 ≤ cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
            d M r q s :=
        cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget_nonneg
          hr hq0 hs0
      have hinner :
          cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
                d M r q s * ‖ZA - ZB‖ * ‖ZH‖ ≤
            cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
                d M r q s *
              (‖(cmp102PhysicalCochainToAmbientCLM :
                  PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
                    PhysicalAmbientMatrixTangent d (M * N') Nc)‖ *
                ‖A - B‖) *
              (‖(cmp102PhysicalCochainToAmbientCLM :
                  PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
                    PhysicalAmbientMatrixTangent d (M * N') Nc)‖ * ‖H‖) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hZA hC) hZH
          (norm_nonneg ZH)
          (mul_nonneg hC
            (mul_nonneg
              (norm_nonneg
                (cmp102PhysicalCochainToAmbientCLM :
                  PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
                    PhysicalAmbientMatrixTangent d (M * N') Nc))
              (norm_nonneg (A - B))))
      exact mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ = cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
          d M N' Nc r q s * ‖A - B‖ * ‖H‖ := by
      unfold cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
      ring

end

end YangMills.RG

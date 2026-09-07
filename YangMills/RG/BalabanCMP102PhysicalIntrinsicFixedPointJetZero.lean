/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalIntrinsicFixedPointSourceDerivative

/-!
# Vanishing first jet of the intrinsic CMP102 correction at zero

The literal CMP98 correction subtracts its own linearization at the origin.
This file proves that cancellation through every physical coordinate
transport and through the joint fixed-point source map.  No vanishing jet
is supplied by the caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102JetZeroCoordCLMNorm :
    Norm (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp102JetZeroCoordCLMSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp102JetZeroCoordCLMNormedSpace :
    NormedSpace ℝ
      (Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc) :=
  ContinuousLinearMap.toNormedSpace

/-- The literal represented block and its fixed normalizer cancel at the
zero ambient tangent. -/
theorem cmp102AmbientNonlinearBlock_zero_mul_inverseAtZero_source
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp102AmbientNonlinearBlock U b 0 *
        cmp98Eq119NonlinearBlockInverseAtZero U
          (0 : PhysicalGaugeOneCochain d (M * N') Nc) b = 1 := by
  have hline :=
    cmp102AmbientNonlinearBlock_physicalLine_eq U
      (0 : PhysicalGaugeOneCochain d (M * N') Nc) b 0
  have hzero :
      (0 : ℝ) • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent
            (0 : PhysicalGaugeOneCochain d (M * N') Nc)) = 0 := by
    funext e i j
    simp [Pi.smul_apply]
  rw [hzero] at hline
  rw [hline]
  exact cmp98Eq119NonlinearBlockCurve_zero_mul_inverseAtZero U 0 b

/-- The first Fréchet derivative of the intrinsic ambient correction
vanishes exactly at zero. -/
theorem fderiv_cmp102IntrinsicAmbientCorrectionBond_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) 0 = 0 := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  apply ContinuousLinearMap.ext
  intro H
  have hlog :
      fderiv ℝ
          (nearLog :
            Matrix (Fin Nc) (Fin Nc) ℂ →
              Matrix (Fin Nc) (Fin Nc) ℂ) 0 =
        ContinuousLinearMap.id ℝ (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    (hasFDerivAt_nearLog_zero
      (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)).fderiv
  rw [fderiv_cmp102IntrinsicAmbientCorrectionBond_apply U b 0 H]
  · rw [cmp102AmbientNonlinearBlock_zero_mul_inverseAtZero_source]
    simp only [sub_self]
    rw [hlog]
    change
      (fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0) H *
          cmp98Eq119NonlinearBlockInverseAtZero U 0 b -
        (fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0) H *
          cmp98Eq119NonlinearBlockInverseAtZero U 0 b = 0
    exact sub_self _
  · intro x hx
    exact (hbase x hx).trans_lt (by norm_num)
  · rw [cmp102AmbientNonlinearBlock_zero_mul_inverseAtZero_source]
    norm_num

/-- The zero-jet cancellation survives the physical Lie-coordinate
transport on one coarse bond. -/
theorem fderiv_cmp102IntrinsicPhysicalCorrectionBondCoord_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    fderiv ℝ (cmp102IntrinsicPhysicalCorrectionBondCoord U b) 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro H
  rw [fderiv_cmp102IntrinsicPhysicalCorrectionBondCoord_apply U b 0 H]
  · simp only [map_zero]
    rw [fderiv_cmp102IntrinsicAmbientCorrectionBond_zero U b hbase]
    simp
  · intro x hx
    rw [map_zero]
    exact (hbase x hx).trans_lt (by norm_num)
  · rw [map_zero]
    rw [cmp102AmbientNonlinearBlock_zero_mul_inverseAtZero_source]
    norm_num

/-- The assembled physical correction has zero first jet at the origin,
without a volume factor. -/
theorem fderiv_cmp102IntrinsicPhysicalNonlinearCorrectionSup_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U) 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro H
  apply PiLp.ext
  intro b
  rw [fderiv_cmp102IntrinsicPhysicalNonlinearCorrectionSup_apply U 0 H b]
  · rw [fderiv_cmp102IntrinsicPhysicalCorrectionBondCoord_zero
      U b (hbase b)]
    simp
  · intro c x hx
    rw [map_zero]
    exact (hbase c x hx).trans_lt (by norm_num)
  · intro c
    rw [map_zero]
    rw [cmp102AmbientNonlinearBlock_zero_mul_inverseAtZero_source]
    norm_num

variable [NeZero (M * N')]

/-- **Physical source zero jet.**  The joint fixed-point source map also
has vanishing first derivative at the origin. -/
theorem
    fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d M N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    fderiv ℝ
      (cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry
        U ha hP hε hsmall hbudget) 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro R
  rw [fderiv_cmp102IntrinsicPhysicalBackgroundCorrectionMapUncurry_apply
    U ha hP hε hsmall hbudget 0 R]
  · rw [map_zero]
    rw [fderiv_cmp102IntrinsicPhysicalNonlinearCorrectionSup_zero U hbase]
    simp
  · intro b x hx
    rw [map_zero, map_zero]
    exact (hbase b x hx).trans_lt (by norm_num)
  · intro b
    rw [map_zero, map_zero]
    rw [cmp102AmbientNonlinearBlock_zero_mul_inverseAtZero_source]
    norm_num

end

end YangMills.RG

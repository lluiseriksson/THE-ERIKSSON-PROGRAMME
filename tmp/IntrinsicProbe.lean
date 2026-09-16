import YangMills.RG.BalabanCMP102PhysicalIntrinsicCorrectionAnalytic

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance probeMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

set_option maxHeartbeats 3000000 in
theorem probe
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp102IntrinsicAmbientCorrectionBond U b
        (cmp102PhysicalCochainToAmbientCLM A) =
      cmp98Eq122NonlinearLogRemainder U A b 1 := by
  have hblock :
      cmp102AmbientNonlinearBlock U b
          (cmp102PhysicalCochainToAmbientCLM A) =
        cmp98Eq119NonlinearBlockCurve U A b 1 := by
    have h :=
      cmp102AmbientNonlinearBlock_physicalLine_eq U A b 1
    have hone :
        (1 : ℝ) • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A) =
          physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A) :=
      one_smul ℝ _
    rw [hone] at h
    rw [cmp102PhysicalCochainToAmbientCLM_apply]
    exact h
  have hright :
      fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
            (cmp102PhysicalCochainToAmbientCLM A) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b =
        cmp98Eq119NonlinearRightVariation U A b := by
    rw [cmp102PhysicalCochainToAmbientCLM_apply]
    rw [← cmp98Eq119NonlinearBlockInverseAtZero_twoField_eq U A 0 b]
    exact
      (cmp98Eq119NonlinearRightVariation_eq_ambientFDeriv
        U A b hbase).symm
  unfold cmp102IntrinsicAmbientCorrectionBond
    cmp98Eq122NonlinearLogRemainder
    cmp98Eq119NonlinearLogCoordinate
    cmp98Eq119NonlinearRelativeDeviation
  dsimp only
  rw [hblock, hright]
  rw [← cmp98Eq119NonlinearBlockInverseAtZero_twoField_eq U A 0 b]
  exact congrArg
    (fun X : Matrix (Fin Nc) (Fin Nc) ℂ =>
      nearLog
        (cmp98Eq119NonlinearBlockCurve U A b 1 *
          cmp98Eq119NonlinearBlockInverseAtZero U A b - 1) - X)
    ((one_smul ℝ
      (cmp98Eq119NonlinearRightVariation U A b :
        Matrix (Fin Nc) (Fin Nc) ℂ)).symm)

theorem probe2
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (B : CMP102PhysicalNonlinearChartBudget U A)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp102PhysicalNonlinearCorrectionOfBudget U A B =
      cmp102IntrinsicPhysicalNonlinearCorrection U A := by
  apply PiLp.ext
  intro b
  rw [cmp102IntrinsicPhysicalNonlinearCorrection_apply]
  rw [probe U A b (hbase b)]
  rw [← cmp102PhysicalNonlinearCorrectionOfBudget_toMatrix U A B b]
  exact (cmp98AmbientToLieCoordCLM_leftInverse
    (cmp102PhysicalNonlinearCorrectionOfBudget U A B b)).symm

end

end YangMills.RG

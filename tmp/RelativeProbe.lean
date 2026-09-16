import YangMills.RG.BalabanCMP102PhysicalIntrinsicImplicitFunction

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

set_option maxHeartbeats 10000000 in
theorem test_chart_intrinsic_relative
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (X : PhysicalGaugeOneCochain d (M * N') Nc)
    (B : CMP102PhysicalNonlinearChartBudget U X) :
    ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM X) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1 := by
  have hone : |(1 : ℝ)| < B.radius := by
    simpa using B.one_lt_radius
  intro b
  have hEq :
      cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM X) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1 =
        cmp98Eq119NonlinearRelativeDeviation U X b 1 := by
    unfold cmp98Eq119NonlinearRelativeDeviation
    have hblock := cmp102AmbientNonlinearBlock_physicalLine_eq U X b 1
    have hone' :
        (1 : ℝ) • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent X) =
          physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent X) :=
      one_smul ℝ _
    rw [hone'] at hblock
    rw [cmp102PhysicalCochainToAmbientCLM_apply, hblock]
    rw [cmp98Eq119NonlinearBlockInverseAtZero_twoField_eq U X 0 b]
  rw [hEq]
  rw [cmp98Eq119NonlinearRelativeDeviation_eq_relativeSUN_sub_one
    U X b 1 (B.near b 1 hone) (B.noWinding b 1 hone)
      (B.near b 0 B.zero_mem) (B.noWinding b 0 B.zero_mem)]
  exact B.relativeNear b 1 hone

end
end YangMills.RG

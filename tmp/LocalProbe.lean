import YangMills.RG.BalabanCMP102PhysicalIntrinsicImplicitFunction

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

set_option maxHeartbeats 10000000 in
theorem test_chart_intrinsic_local
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (X : PhysicalGaugeOneCochain d (M * N') Nc)
    (B : CMP102PhysicalNonlinearChartBudget U X) :
    ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM X)‖ < 1 := by
  have hone : |(1 : ℝ)| < B.radius := by
    simpa using B.one_lt_radius
  intro b x hx
  have heq :
      cmp98UbarAmbientDeviationMatrix U b x
          (cmp102PhysicalCochainToAmbientCLM X) =
        (cmp98PhysicalUbarRelativeSUN U X b x 1 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1 := by
    rw [cmp102PhysicalCochainToAmbientCLM_apply]
    have hline :=
      cmp98UbarAmbientDeviationMatrix_line_eq_relativeSUN_sub_one
        U X b x 1
    have hone' :
        (1 : ℝ) • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent X) =
          physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent X) :=
      one_smul ℝ _
    rw [hone'] at hline
    exact hline
  rw [heq]
  exact B.near b 1 hone x hx

end
end YangMills.RG

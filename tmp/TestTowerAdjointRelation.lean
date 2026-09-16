import YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance

namespace YangMills.RG
open scoped RealInnerProductSpace
noncomputable section

variable {d N : ℕ} {g : Type} [NeZero N]
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]

theorem test_Qprime_eq_smul_weightedAdjoint_adjoint
    (Omega : ActiveGaugeRegion d N) {spacing : ℝ}
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (hspacing : 0 < spacing) (hterminal : 0 < T.terminalSpacing) :
    T.Qprime =
      (spacing ^ d / T.terminalSpacing ^ d) • T.weightedAdjoint.adjoint := by
  apply ContinuousLinearMap.ext
  intro phi
  apply ext_inner_right ℝ
  intro eta
  have hpair := T.weightedAdjoint_pairing phi eta
  rw [cmp99SourceSpacingPairing, cmp99SourceSpacingPairing] at hpair
  have hterminalPow : T.terminalSpacing ^ d ≠ 0 :=
    ne_of_gt (pow_pos hterminal d)
  calc
    inner ℝ (T.Qprime phi) eta =
        spacing ^ d / T.terminalSpacing ^ d *
          inner ℝ phi (T.weightedAdjoint eta) := by
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hterminalPow).2
      nlinarith [hpair]
    _ = inner ℝ
        (((spacing ^ d / T.terminalSpacing ^ d) •
          T.weightedAdjoint.adjoint) phi) eta := by
      simp only [ContinuousLinearMap.smul_apply, inner_smul_left,
        conj_trivial]
      rw [ContinuousLinearMap.adjoint_inner_left]

end
end YangMills.RG

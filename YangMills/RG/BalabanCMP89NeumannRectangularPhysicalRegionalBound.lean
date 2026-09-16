import YangMills.RG.BalabanCMP89NeumannRectangularPhysicalGreenInsertion

/-!
# CMP89 (2.42): physical regional Green value bound

This consumer keeps the exact CMP89 (2.42) representation certificate visible
and rewrites the regional Green to the already bounded source-order image
series.  It does not construct the representation certificate.
-/

namespace YangMills.RG

noncomputable section

/-- The exact CMP89 (2.42) representation transports the physical image-series
bound to the regional kernel without introducing a second regional constant.
-/
theorem norm_cmp89Eq248PhysicalRegionalGreen_le_of_representation_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {m : Fin 4 → ℤ}
    {regionalGreen : CMP89SourceNeumannIntegerRectanglePoint m →
      CMP89SourceNeumannIntegerRectanglePoint m → ℂ}
    (R : CMP89NeumannReflectionRepresentationCertificate m regionalGreen
      (cmp89Eq248PhysicalFullLatticeGreen L j mass a))
    (x n : CMP89SourceNeumannIntegerRectanglePoint m) :
    ‖regionalGreen x n‖ ≤
      (2 : ℝ) ^ 4 *
        cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        ((∏ mu,
            2 / (1 - Real.exp
              (-(rho / ((L ^ j : ℕ) : ℝ)) *
                (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
          cmp89SignedLatticeL1ExponentialWeight
            (rho / ((L ^ j : ℕ) : ℝ)) (x.1 - n.1)) := by
  calc
    ‖regionalGreen x n‖ =
        ‖cmp89NeumannReflectionSeries
          (cmp89Eq248PhysicalFullLatticeGreen L j mass a) m x.1 n.1‖ := by
      rw [R.eq_series x n]
    _ ≤ _ := norm_cmp89Eq248PhysicalNeumannReflectionSeries_le_draft
      ha hrho hamplitude hradius hwindow hmass R.side_pos x.2 n.2

end

end YangMills.RG

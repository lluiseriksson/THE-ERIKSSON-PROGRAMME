import YangMills.L1_GibbsMeasure.Expectation

namespace YangMills

open MeasureTheory

/-! ## L1.3b: Correlations under Gibbs measure -/

/-- Correlation of two real-valued observables under the Gibbs measure. -/
noncomputable def correlation (d N : ℕ) [NeZero d] [NeZero N] {G : Type*}
    [Group G] [MeasurableSpace G]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (O₁ O₂ : GaugeConfig d N G → ℝ) : ℝ :=
  expectation d N μ plaquetteEnergy β (fun U => O₁ U * O₂ U)

/-- Symmetry of correlation. -/
theorem correlation_symm (d N : ℕ) [NeZero d] [NeZero N] {G : Type*}
    [Group G] [MeasurableSpace G]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (O₁ O₂ : GaugeConfig d N G → ℝ) :
    correlation d N μ plaquetteEnergy β O₁ O₂ =
    correlation d N μ plaquetteEnergy β O₂ O₁ := by
  unfold correlation expectation
  congr 1; ext U; ring

end YangMills

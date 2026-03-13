import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure

namespace YangMills

open MeasureTheory

/-! ## L1.3a: Expectation values under Gibbs measure -/

/-- Expectation of a real-valued observable under the finite-volume Gibbs measure. -/
noncomputable def expectation (d N : ℕ) [NeZero d] [NeZero N] {G : Type*}
    [Group G] [MeasurableSpace G]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (O : GaugeConfig d N G → ℝ) : ℝ :=
  ∫ U, O U ∂(gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β)

/-- Expectation of a constant is the constant. -/
theorem expectation_const (d N : ℕ) [NeZero d] [NeZero N] {G : Type*}
    [Group G] [MeasurableSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ)
    (h_int : Integrable (fun U : GaugeConfig d N G =>
      Real.exp (-β * wilsonAction plaquetteEnergy U)) (gaugeMeasureFrom (d:=d) (N:=N) μ))
    (c : ℝ) :
    expectation d N μ plaquetteEnergy β (fun _ => c) = c := by
  haveI : IsProbabilityMeasure (gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β) :=
    gibbsMeasure_isProbability d N μ plaquetteEnergy β h_int
  simp [expectation]

/-- Linearity: expectation of a sum. -/
theorem expectation_add (d N : ℕ) [NeZero d] [NeZero N] {G : Type*}
    [Group G] [MeasurableSpace G] (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    {O₁ O₂ : GaugeConfig d N G → ℝ}
    (h₁ : Integrable O₁ (gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β))
    (h₂ : Integrable O₂ (gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β)) :
    expectation d N μ plaquetteEnergy β (fun U => O₁ U + O₂ U) =
    expectation d N μ plaquetteEnergy β O₁ + expectation d N μ plaquetteEnergy β O₂ := by
  simp [expectation, integral_add h₁ h₂]

/-- Monotonicity of expectation. -/
theorem expectation_mono (d N : ℕ) [NeZero d] [NeZero N] {G : Type*}
    [Group G] [MeasurableSpace G] (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    {O₁ O₂ : GaugeConfig d N G → ℝ}
    (h₁ : Integrable O₁ (gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β))
    (h₂ : Integrable O₂ (gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β))
    (h_le : ∀ U, O₁ U ≤ O₂ U) :
    expectation d N μ plaquetteEnergy β O₁ ≤ expectation d N μ plaquetteEnergy β O₂ :=
  integral_mono h₁ h₂ h_le

end YangMills

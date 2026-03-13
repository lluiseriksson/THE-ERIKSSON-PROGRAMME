import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure

open YangMills MeasureTheory

-- Option 3: explicit d N in definition
noncomputable def expectation' (d N : ℕ) [NeZero d] [NeZero N] {G : Type*}
    [Group G] [MeasurableSpace G]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (O : GaugeConfig d N G → ℝ) : ℝ :=
  ∫ U, O U ∂(gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β)

example (d N : ℕ) [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (plaquetteEnergy : G → ℝ) (β : ℝ)
    (h_int : Integrable (fun U : GaugeConfig d N G =>
      Real.exp (-β * wilsonAction plaquetteEnergy U)) (gaugeMeasureFrom (d:=d) (N:=N) μ))
    (c : ℝ) : expectation' d N μ plaquetteEnergy β (fun _ => c) = c := by
  haveI : IsProbabilityMeasure (gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β) :=
    gibbsMeasure_isProbability d N μ plaquetteEnergy β h_int
  simp [expectation']

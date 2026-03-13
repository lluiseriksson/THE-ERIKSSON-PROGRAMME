import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure

open YangMills MeasureTheory

theorem partitionFunction_pos {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ)
    (h_int : Integrable
      (fun U : GaugeConfig d N G => Real.exp (-β * wilsonAction plaquetteEnergy U))
      (gaugeMeasureFrom (d:=d) (N:=N) μ)) :
    0 < partitionFunction (d:=d) (N:=N) μ plaquetteEnergy β := by
  unfold partitionFunction
  haveI hne : NeZero (gaugeMeasureFrom (d:=d) (N:=N) μ) :=
    IsProbabilityMeasure.neZero _
  exact integral_exp_pos (μ := gaugeMeasureFrom (d:=d) (N:=N) μ) h_int

#check @partitionFunction_pos

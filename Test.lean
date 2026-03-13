import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure

open YangMills MeasureTheory

theorem partitionFunction_pos {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ)
    (h_int : Integrable (fun U : GaugeConfig d N G =>
      Real.exp (-β * wilsonAction plaquetteEnergy U))
      (gaugeMeasureFrom (d:=d) (N:=N) (G:=G) μ)) :
    0 < partitionFunction μ plaquetteEnergy β := by
  unfold partitionFunction
  set ν := gaugeMeasureFrom (d:=d) (N:=N) (G:=G) μ with hν
  haveI hprob : IsProbabilityMeasure ν := gaugeMeasureFrom_isProbability μ
  haveI hne : NeZero ν := IsProbabilityMeasure.neZero ν
  exact @integral_exp_pos _ _ ν _ hne h_int

#check @partitionFunction_pos

import Mathlib
import YangMills.L1_GibbsMeasure.GibbsMeasure

open YangMills MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

lemma measurable_gaugeConfigEquiv :
    Measurable (gaugeConfigEquiv (d:=d) (N:=N) (G:=G)) := by
  rw [measurable_iff_comap_le]
  simp only [instMeasurableSpaceGaugeConfig]
  rw [MeasurableSpace.comap_comp]
  simp [MeasurableSpace.comap_id]

#check @measurable_gaugeConfigEquiv

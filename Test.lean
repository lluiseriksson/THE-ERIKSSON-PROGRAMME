import Mathlib
import YangMills.L2_Balaban.SmallLargeDecomposition
import YangMills.L1_GibbsMeasure.GibbsMeasure

open YangMills MeasureTheory Set

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]
variable (κ : ℝ) (plaquetteEnergy : G → ℝ) (β : ℝ)

-- Test 1: integrability
example (μ : Measure G) [IsProbabilityMeasure μ]
    (h_meas : MeasurableSet (SmallFieldSet (d:=d) (N:=N) κ plaquetteEnergy))
    (h_int : Integrable (fun U : GaugeConfig d N G =>
      Real.exp (-β * wilsonAction plaquetteEnergy U)) (gaugeMeasureFrom μ)) :
    Integrable (fun U : GaugeConfig d N G =>
      χ_small κ plaquetteEnergy U * Real.exp (-β * wilsonAction plaquetteEnergy U))
      (gaugeMeasureFrom μ) := by
  apply Integrable.congr (h_int.indicator h_meas)
  filter_upwards with U
  simp [χ_small, SmallFieldSet, Set.indicator]

-- Test 2: congr goal
example (e a b : ℝ) (h : a + b = 1) (hlt : a * e + b * e < e) : False := by
  have : a * e + b * e = e := by rw [← add_mul, h, one_mul]
  linarith

-- Test 3: pointwise bound
example (U : GaugeConfig d N G) (hβ : 0 ≤ β)
    (hU : U ∈ LargeFieldSet (d:=d) (N:=N) κ plaquetteEnergy) :
    χ_large κ plaquetteEnergy U * Real.exp (-β * wilsonAction plaquetteEnergy U) ≤
    Real.exp (-β * κ) := by
  simp only [χ_large, LargeFieldSet, Set.indicator, Set.mem_setOf_eq]
  split_ifs with h
  · simp only [one_mul]
    apply Real.exp_le_exp.mpr
    have hS : κ < wilsonAction plaquetteEnergy U := hU
    nlinarith
  · simp; exact (Real.exp_pos _).le
